%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:34 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 568 expanded)
%              Number of clauses        :   70 ( 147 expanded)
%              Number of leaves         :   19 ( 134 expanded)
%              Depth                    :   19
%              Number of atoms          :  333 (1461 expanded)
%              Number of equality atoms :  177 ( 643 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f38,plain,
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

fof(f39,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f38])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f75,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f35])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_enumset1(X1,X1,X2) = X0
      | k1_enumset1(X2,X2,X2) = X0
      | k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_enumset1(X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f46,f45,f67,f67,f45])).

fof(f66,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f66,f67,f67])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_enumset1(X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f59,f67,f67])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

cnf(c_13,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_12,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1081,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1761,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_1081])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1207,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1209,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1208,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1211,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1208])).

cnf(c_1766,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1761,c_1209,c_1211])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1088,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1090,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1916,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1088,c_1090])).

cnf(c_2199,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1766,c_1916])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1075,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_11])).

cnf(c_345,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_18])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_345])).

cnf(c_1073,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_1376,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1075,c_1073])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X2))
    | k1_enumset1(X1,X1,X2) = X0
    | k1_enumset1(X2,X2,X2) = X0
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1083,plain,
    ( k1_enumset1(X0,X0,X1) = X2
    | k1_enumset1(X1,X1,X1) = X2
    | k1_enumset1(X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k1_enumset1(X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1906,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1376,c_1083])).

cnf(c_2450,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_1075])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1215,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1243,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1301,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(c_1409,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_752,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1236,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_1300,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1236])).

cnf(c_1410,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1300])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_244,plain,
    ( ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_245,plain,
    ( ~ v1_relat_1(sK3)
    | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_244])).

cnf(c_1074,plain,
    ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_26,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_246,plain,
    ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_245])).

cnf(c_1216,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1215])).

cnf(c_1229,plain,
    ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1074,c_26,c_246,c_1216])).

cnf(c_1230,plain,
    ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1229])).

cnf(c_2445,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1906,c_1230])).

cnf(c_2496,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2450,c_23,c_21,c_1215,c_1301,c_1409,c_1410,c_2445])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1079,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2514,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2496,c_1079])).

cnf(c_1315,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_750,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1328,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_751,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1516,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_2154,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1516])).

cnf(c_2155,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2154])).

cnf(c_2542,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2514,c_23,c_21,c_1215,c_1301,c_1315,c_1328,c_1409,c_1410,c_2155,c_2445])).

cnf(c_1077,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2107,plain,
    ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1075,c_1077])).

cnf(c_1076,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2204,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2107,c_1076])).

cnf(c_2546,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2542,c_2204])).

cnf(c_2857,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2199,c_2546])).

cnf(c_3024,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2857,c_1088])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:41:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.07/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/0.98  
% 2.07/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.07/0.98  
% 2.07/0.98  ------  iProver source info
% 2.07/0.98  
% 2.07/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.07/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.07/0.98  git: non_committed_changes: false
% 2.07/0.98  git: last_make_outside_of_git: false
% 2.07/0.98  
% 2.07/0.98  ------ 
% 2.07/0.98  
% 2.07/0.98  ------ Input Options
% 2.07/0.98  
% 2.07/0.98  --out_options                           all
% 2.07/0.98  --tptp_safe_out                         true
% 2.07/0.98  --problem_path                          ""
% 2.07/0.98  --include_path                          ""
% 2.07/0.98  --clausifier                            res/vclausify_rel
% 2.07/0.98  --clausifier_options                    --mode clausify
% 2.07/0.98  --stdin                                 false
% 2.07/0.98  --stats_out                             all
% 2.07/0.98  
% 2.07/0.98  ------ General Options
% 2.07/0.98  
% 2.07/0.98  --fof                                   false
% 2.07/0.98  --time_out_real                         305.
% 2.07/0.98  --time_out_virtual                      -1.
% 2.07/0.98  --symbol_type_check                     false
% 2.07/0.98  --clausify_out                          false
% 2.07/0.98  --sig_cnt_out                           false
% 2.07/0.98  --trig_cnt_out                          false
% 2.07/0.98  --trig_cnt_out_tolerance                1.
% 2.07/0.98  --trig_cnt_out_sk_spl                   false
% 2.07/0.98  --abstr_cl_out                          false
% 2.07/0.98  
% 2.07/0.98  ------ Global Options
% 2.07/0.98  
% 2.07/0.98  --schedule                              default
% 2.07/0.98  --add_important_lit                     false
% 2.07/0.98  --prop_solver_per_cl                    1000
% 2.07/0.98  --min_unsat_core                        false
% 2.07/0.98  --soft_assumptions                      false
% 2.07/0.98  --soft_lemma_size                       3
% 2.07/0.98  --prop_impl_unit_size                   0
% 2.07/0.98  --prop_impl_unit                        []
% 2.07/0.98  --share_sel_clauses                     true
% 2.07/0.98  --reset_solvers                         false
% 2.07/0.98  --bc_imp_inh                            [conj_cone]
% 2.07/0.98  --conj_cone_tolerance                   3.
% 2.07/0.98  --extra_neg_conj                        none
% 2.07/0.98  --large_theory_mode                     true
% 2.07/0.98  --prolific_symb_bound                   200
% 2.07/0.98  --lt_threshold                          2000
% 2.07/0.98  --clause_weak_htbl                      true
% 2.07/0.98  --gc_record_bc_elim                     false
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing Options
% 2.07/0.98  
% 2.07/0.98  --preprocessing_flag                    true
% 2.07/0.98  --time_out_prep_mult                    0.1
% 2.07/0.98  --splitting_mode                        input
% 2.07/0.98  --splitting_grd                         true
% 2.07/0.98  --splitting_cvd                         false
% 2.07/0.98  --splitting_cvd_svl                     false
% 2.07/0.98  --splitting_nvd                         32
% 2.07/0.98  --sub_typing                            true
% 2.07/0.98  --prep_gs_sim                           true
% 2.07/0.98  --prep_unflatten                        true
% 2.07/0.98  --prep_res_sim                          true
% 2.07/0.98  --prep_upred                            true
% 2.07/0.98  --prep_sem_filter                       exhaustive
% 2.07/0.98  --prep_sem_filter_out                   false
% 2.07/0.98  --pred_elim                             true
% 2.07/0.98  --res_sim_input                         true
% 2.07/0.98  --eq_ax_congr_red                       true
% 2.07/0.98  --pure_diseq_elim                       true
% 2.07/0.98  --brand_transform                       false
% 2.07/0.98  --non_eq_to_eq                          false
% 2.07/0.98  --prep_def_merge                        true
% 2.07/0.98  --prep_def_merge_prop_impl              false
% 2.07/0.98  --prep_def_merge_mbd                    true
% 2.07/0.98  --prep_def_merge_tr_red                 false
% 2.07/0.98  --prep_def_merge_tr_cl                  false
% 2.07/0.98  --smt_preprocessing                     true
% 2.07/0.98  --smt_ac_axioms                         fast
% 2.07/0.98  --preprocessed_out                      false
% 2.07/0.98  --preprocessed_stats                    false
% 2.07/0.98  
% 2.07/0.98  ------ Abstraction refinement Options
% 2.07/0.98  
% 2.07/0.98  --abstr_ref                             []
% 2.07/0.98  --abstr_ref_prep                        false
% 2.07/0.98  --abstr_ref_until_sat                   false
% 2.07/0.98  --abstr_ref_sig_restrict                funpre
% 2.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/0.98  --abstr_ref_under                       []
% 2.07/0.98  
% 2.07/0.98  ------ SAT Options
% 2.07/0.98  
% 2.07/0.98  --sat_mode                              false
% 2.07/0.98  --sat_fm_restart_options                ""
% 2.07/0.98  --sat_gr_def                            false
% 2.07/0.98  --sat_epr_types                         true
% 2.07/0.98  --sat_non_cyclic_types                  false
% 2.07/0.98  --sat_finite_models                     false
% 2.07/0.98  --sat_fm_lemmas                         false
% 2.07/0.98  --sat_fm_prep                           false
% 2.07/0.98  --sat_fm_uc_incr                        true
% 2.07/0.98  --sat_out_model                         small
% 2.07/0.98  --sat_out_clauses                       false
% 2.07/0.98  
% 2.07/0.98  ------ QBF Options
% 2.07/0.98  
% 2.07/0.98  --qbf_mode                              false
% 2.07/0.98  --qbf_elim_univ                         false
% 2.07/0.98  --qbf_dom_inst                          none
% 2.07/0.98  --qbf_dom_pre_inst                      false
% 2.07/0.98  --qbf_sk_in                             false
% 2.07/0.98  --qbf_pred_elim                         true
% 2.07/0.98  --qbf_split                             512
% 2.07/0.98  
% 2.07/0.98  ------ BMC1 Options
% 2.07/0.98  
% 2.07/0.98  --bmc1_incremental                      false
% 2.07/0.98  --bmc1_axioms                           reachable_all
% 2.07/0.98  --bmc1_min_bound                        0
% 2.07/0.98  --bmc1_max_bound                        -1
% 2.07/0.98  --bmc1_max_bound_default                -1
% 2.07/0.98  --bmc1_symbol_reachability              true
% 2.07/0.98  --bmc1_property_lemmas                  false
% 2.07/0.98  --bmc1_k_induction                      false
% 2.07/0.98  --bmc1_non_equiv_states                 false
% 2.07/0.98  --bmc1_deadlock                         false
% 2.07/0.98  --bmc1_ucm                              false
% 2.07/0.98  --bmc1_add_unsat_core                   none
% 2.07/0.98  --bmc1_unsat_core_children              false
% 2.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/0.98  --bmc1_out_stat                         full
% 2.07/0.98  --bmc1_ground_init                      false
% 2.07/0.98  --bmc1_pre_inst_next_state              false
% 2.07/0.98  --bmc1_pre_inst_state                   false
% 2.07/0.98  --bmc1_pre_inst_reach_state             false
% 2.07/0.98  --bmc1_out_unsat_core                   false
% 2.07/0.98  --bmc1_aig_witness_out                  false
% 2.07/0.98  --bmc1_verbose                          false
% 2.07/0.98  --bmc1_dump_clauses_tptp                false
% 2.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.07/0.98  --bmc1_dump_file                        -
% 2.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.07/0.98  --bmc1_ucm_extend_mode                  1
% 2.07/0.98  --bmc1_ucm_init_mode                    2
% 2.07/0.98  --bmc1_ucm_cone_mode                    none
% 2.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.07/0.98  --bmc1_ucm_relax_model                  4
% 2.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/0.98  --bmc1_ucm_layered_model                none
% 2.07/0.98  --bmc1_ucm_max_lemma_size               10
% 2.07/0.98  
% 2.07/0.98  ------ AIG Options
% 2.07/0.98  
% 2.07/0.98  --aig_mode                              false
% 2.07/0.98  
% 2.07/0.98  ------ Instantiation Options
% 2.07/0.98  
% 2.07/0.98  --instantiation_flag                    true
% 2.07/0.98  --inst_sos_flag                         false
% 2.07/0.98  --inst_sos_phase                        true
% 2.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/0.98  --inst_lit_sel_side                     num_symb
% 2.07/0.98  --inst_solver_per_active                1400
% 2.07/0.98  --inst_solver_calls_frac                1.
% 2.07/0.98  --inst_passive_queue_type               priority_queues
% 2.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/0.98  --inst_passive_queues_freq              [25;2]
% 2.07/0.98  --inst_dismatching                      true
% 2.07/0.98  --inst_eager_unprocessed_to_passive     true
% 2.07/0.98  --inst_prop_sim_given                   true
% 2.07/0.98  --inst_prop_sim_new                     false
% 2.07/0.98  --inst_subs_new                         false
% 2.07/0.98  --inst_eq_res_simp                      false
% 2.07/0.98  --inst_subs_given                       false
% 2.07/0.98  --inst_orphan_elimination               true
% 2.07/0.98  --inst_learning_loop_flag               true
% 2.07/0.98  --inst_learning_start                   3000
% 2.07/0.98  --inst_learning_factor                  2
% 2.07/0.98  --inst_start_prop_sim_after_learn       3
% 2.07/0.98  --inst_sel_renew                        solver
% 2.07/0.98  --inst_lit_activity_flag                true
% 2.07/0.98  --inst_restr_to_given                   false
% 2.07/0.98  --inst_activity_threshold               500
% 2.07/0.98  --inst_out_proof                        true
% 2.07/0.98  
% 2.07/0.98  ------ Resolution Options
% 2.07/0.98  
% 2.07/0.98  --resolution_flag                       true
% 2.07/0.98  --res_lit_sel                           adaptive
% 2.07/0.98  --res_lit_sel_side                      none
% 2.07/0.98  --res_ordering                          kbo
% 2.07/0.98  --res_to_prop_solver                    active
% 2.07/0.98  --res_prop_simpl_new                    false
% 2.07/0.98  --res_prop_simpl_given                  true
% 2.07/0.98  --res_passive_queue_type                priority_queues
% 2.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/0.98  --res_passive_queues_freq               [15;5]
% 2.07/0.98  --res_forward_subs                      full
% 2.07/0.98  --res_backward_subs                     full
% 2.07/0.98  --res_forward_subs_resolution           true
% 2.07/0.98  --res_backward_subs_resolution          true
% 2.07/0.98  --res_orphan_elimination                true
% 2.07/0.98  --res_time_limit                        2.
% 2.07/0.98  --res_out_proof                         true
% 2.07/0.98  
% 2.07/0.98  ------ Superposition Options
% 2.07/0.98  
% 2.07/0.98  --superposition_flag                    true
% 2.07/0.98  --sup_passive_queue_type                priority_queues
% 2.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.07/0.98  --demod_completeness_check              fast
% 2.07/0.98  --demod_use_ground                      true
% 2.07/0.98  --sup_to_prop_solver                    passive
% 2.07/0.98  --sup_prop_simpl_new                    true
% 2.07/0.98  --sup_prop_simpl_given                  true
% 2.07/0.98  --sup_fun_splitting                     false
% 2.07/0.98  --sup_smt_interval                      50000
% 2.07/0.98  
% 2.07/0.98  ------ Superposition Simplification Setup
% 2.07/0.98  
% 2.07/0.98  --sup_indices_passive                   []
% 2.07/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_full_bw                           [BwDemod]
% 2.07/0.98  --sup_immed_triv                        [TrivRules]
% 2.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_immed_bw_main                     []
% 2.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.98  
% 2.07/0.98  ------ Combination Options
% 2.07/0.98  
% 2.07/0.98  --comb_res_mult                         3
% 2.07/0.98  --comb_sup_mult                         2
% 2.07/0.98  --comb_inst_mult                        10
% 2.07/0.98  
% 2.07/0.98  ------ Debug Options
% 2.07/0.98  
% 2.07/0.98  --dbg_backtrace                         false
% 2.07/0.98  --dbg_dump_prop_clauses                 false
% 2.07/0.98  --dbg_dump_prop_clauses_file            -
% 2.07/0.98  --dbg_out_stat                          false
% 2.07/0.98  ------ Parsing...
% 2.07/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.07/0.98  ------ Proving...
% 2.07/0.98  ------ Problem Properties 
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  clauses                                 21
% 2.07/0.98  conjectures                             3
% 2.07/0.98  EPR                                     4
% 2.07/0.98  Horn                                    20
% 2.07/0.98  unary                                   12
% 2.07/0.98  binary                                  4
% 2.07/0.98  lits                                    37
% 2.07/0.98  lits eq                                 15
% 2.07/0.98  fd_pure                                 0
% 2.07/0.98  fd_pseudo                               0
% 2.07/0.98  fd_cond                                 2
% 2.07/0.98  fd_pseudo_cond                          2
% 2.07/0.98  AC symbols                              0
% 2.07/0.98  
% 2.07/0.98  ------ Schedule dynamic 5 is on 
% 2.07/0.98  
% 2.07/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  ------ 
% 2.07/0.98  Current options:
% 2.07/0.98  ------ 
% 2.07/0.98  
% 2.07/0.98  ------ Input Options
% 2.07/0.98  
% 2.07/0.98  --out_options                           all
% 2.07/0.98  --tptp_safe_out                         true
% 2.07/0.98  --problem_path                          ""
% 2.07/0.98  --include_path                          ""
% 2.07/0.98  --clausifier                            res/vclausify_rel
% 2.07/0.98  --clausifier_options                    --mode clausify
% 2.07/0.98  --stdin                                 false
% 2.07/0.98  --stats_out                             all
% 2.07/0.98  
% 2.07/0.98  ------ General Options
% 2.07/0.98  
% 2.07/0.98  --fof                                   false
% 2.07/0.98  --time_out_real                         305.
% 2.07/0.98  --time_out_virtual                      -1.
% 2.07/0.98  --symbol_type_check                     false
% 2.07/0.98  --clausify_out                          false
% 2.07/0.98  --sig_cnt_out                           false
% 2.07/0.98  --trig_cnt_out                          false
% 2.07/0.98  --trig_cnt_out_tolerance                1.
% 2.07/0.98  --trig_cnt_out_sk_spl                   false
% 2.07/0.98  --abstr_cl_out                          false
% 2.07/0.98  
% 2.07/0.98  ------ Global Options
% 2.07/0.98  
% 2.07/0.98  --schedule                              default
% 2.07/0.98  --add_important_lit                     false
% 2.07/0.98  --prop_solver_per_cl                    1000
% 2.07/0.98  --min_unsat_core                        false
% 2.07/0.98  --soft_assumptions                      false
% 2.07/0.98  --soft_lemma_size                       3
% 2.07/0.98  --prop_impl_unit_size                   0
% 2.07/0.98  --prop_impl_unit                        []
% 2.07/0.98  --share_sel_clauses                     true
% 2.07/0.98  --reset_solvers                         false
% 2.07/0.98  --bc_imp_inh                            [conj_cone]
% 2.07/0.98  --conj_cone_tolerance                   3.
% 2.07/0.98  --extra_neg_conj                        none
% 2.07/0.98  --large_theory_mode                     true
% 2.07/0.98  --prolific_symb_bound                   200
% 2.07/0.98  --lt_threshold                          2000
% 2.07/0.98  --clause_weak_htbl                      true
% 2.07/0.98  --gc_record_bc_elim                     false
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing Options
% 2.07/0.98  
% 2.07/0.98  --preprocessing_flag                    true
% 2.07/0.98  --time_out_prep_mult                    0.1
% 2.07/0.98  --splitting_mode                        input
% 2.07/0.98  --splitting_grd                         true
% 2.07/0.98  --splitting_cvd                         false
% 2.07/0.98  --splitting_cvd_svl                     false
% 2.07/0.98  --splitting_nvd                         32
% 2.07/0.98  --sub_typing                            true
% 2.07/0.98  --prep_gs_sim                           true
% 2.07/0.98  --prep_unflatten                        true
% 2.07/0.98  --prep_res_sim                          true
% 2.07/0.98  --prep_upred                            true
% 2.07/0.98  --prep_sem_filter                       exhaustive
% 2.07/0.98  --prep_sem_filter_out                   false
% 2.07/0.98  --pred_elim                             true
% 2.07/0.98  --res_sim_input                         true
% 2.07/0.98  --eq_ax_congr_red                       true
% 2.07/0.98  --pure_diseq_elim                       true
% 2.07/0.98  --brand_transform                       false
% 2.07/0.98  --non_eq_to_eq                          false
% 2.07/0.98  --prep_def_merge                        true
% 2.07/0.98  --prep_def_merge_prop_impl              false
% 2.07/0.98  --prep_def_merge_mbd                    true
% 2.07/0.98  --prep_def_merge_tr_red                 false
% 2.07/0.98  --prep_def_merge_tr_cl                  false
% 2.07/0.98  --smt_preprocessing                     true
% 2.07/0.98  --smt_ac_axioms                         fast
% 2.07/0.98  --preprocessed_out                      false
% 2.07/0.98  --preprocessed_stats                    false
% 2.07/0.98  
% 2.07/0.98  ------ Abstraction refinement Options
% 2.07/0.98  
% 2.07/0.98  --abstr_ref                             []
% 2.07/0.98  --abstr_ref_prep                        false
% 2.07/0.98  --abstr_ref_until_sat                   false
% 2.07/0.98  --abstr_ref_sig_restrict                funpre
% 2.07/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.07/0.98  --abstr_ref_under                       []
% 2.07/0.98  
% 2.07/0.98  ------ SAT Options
% 2.07/0.98  
% 2.07/0.98  --sat_mode                              false
% 2.07/0.98  --sat_fm_restart_options                ""
% 2.07/0.98  --sat_gr_def                            false
% 2.07/0.98  --sat_epr_types                         true
% 2.07/0.98  --sat_non_cyclic_types                  false
% 2.07/0.98  --sat_finite_models                     false
% 2.07/0.98  --sat_fm_lemmas                         false
% 2.07/0.98  --sat_fm_prep                           false
% 2.07/0.98  --sat_fm_uc_incr                        true
% 2.07/0.98  --sat_out_model                         small
% 2.07/0.98  --sat_out_clauses                       false
% 2.07/0.98  
% 2.07/0.98  ------ QBF Options
% 2.07/0.98  
% 2.07/0.98  --qbf_mode                              false
% 2.07/0.98  --qbf_elim_univ                         false
% 2.07/0.98  --qbf_dom_inst                          none
% 2.07/0.98  --qbf_dom_pre_inst                      false
% 2.07/0.98  --qbf_sk_in                             false
% 2.07/0.98  --qbf_pred_elim                         true
% 2.07/0.98  --qbf_split                             512
% 2.07/0.98  
% 2.07/0.98  ------ BMC1 Options
% 2.07/0.98  
% 2.07/0.98  --bmc1_incremental                      false
% 2.07/0.98  --bmc1_axioms                           reachable_all
% 2.07/0.98  --bmc1_min_bound                        0
% 2.07/0.98  --bmc1_max_bound                        -1
% 2.07/0.98  --bmc1_max_bound_default                -1
% 2.07/0.98  --bmc1_symbol_reachability              true
% 2.07/0.98  --bmc1_property_lemmas                  false
% 2.07/0.98  --bmc1_k_induction                      false
% 2.07/0.98  --bmc1_non_equiv_states                 false
% 2.07/0.98  --bmc1_deadlock                         false
% 2.07/0.98  --bmc1_ucm                              false
% 2.07/0.98  --bmc1_add_unsat_core                   none
% 2.07/0.98  --bmc1_unsat_core_children              false
% 2.07/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.07/0.98  --bmc1_out_stat                         full
% 2.07/0.98  --bmc1_ground_init                      false
% 2.07/0.98  --bmc1_pre_inst_next_state              false
% 2.07/0.98  --bmc1_pre_inst_state                   false
% 2.07/0.98  --bmc1_pre_inst_reach_state             false
% 2.07/0.98  --bmc1_out_unsat_core                   false
% 2.07/0.98  --bmc1_aig_witness_out                  false
% 2.07/0.98  --bmc1_verbose                          false
% 2.07/0.98  --bmc1_dump_clauses_tptp                false
% 2.07/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.07/0.98  --bmc1_dump_file                        -
% 2.07/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.07/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.07/0.98  --bmc1_ucm_extend_mode                  1
% 2.07/0.98  --bmc1_ucm_init_mode                    2
% 2.07/0.98  --bmc1_ucm_cone_mode                    none
% 2.07/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.07/0.98  --bmc1_ucm_relax_model                  4
% 2.07/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.07/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.07/0.98  --bmc1_ucm_layered_model                none
% 2.07/0.98  --bmc1_ucm_max_lemma_size               10
% 2.07/0.98  
% 2.07/0.98  ------ AIG Options
% 2.07/0.98  
% 2.07/0.98  --aig_mode                              false
% 2.07/0.98  
% 2.07/0.98  ------ Instantiation Options
% 2.07/0.98  
% 2.07/0.98  --instantiation_flag                    true
% 2.07/0.98  --inst_sos_flag                         false
% 2.07/0.98  --inst_sos_phase                        true
% 2.07/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.07/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.07/0.98  --inst_lit_sel_side                     none
% 2.07/0.98  --inst_solver_per_active                1400
% 2.07/0.98  --inst_solver_calls_frac                1.
% 2.07/0.98  --inst_passive_queue_type               priority_queues
% 2.07/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.07/0.98  --inst_passive_queues_freq              [25;2]
% 2.07/0.98  --inst_dismatching                      true
% 2.07/0.98  --inst_eager_unprocessed_to_passive     true
% 2.07/0.98  --inst_prop_sim_given                   true
% 2.07/0.98  --inst_prop_sim_new                     false
% 2.07/0.98  --inst_subs_new                         false
% 2.07/0.98  --inst_eq_res_simp                      false
% 2.07/0.98  --inst_subs_given                       false
% 2.07/0.98  --inst_orphan_elimination               true
% 2.07/0.98  --inst_learning_loop_flag               true
% 2.07/0.98  --inst_learning_start                   3000
% 2.07/0.98  --inst_learning_factor                  2
% 2.07/0.98  --inst_start_prop_sim_after_learn       3
% 2.07/0.98  --inst_sel_renew                        solver
% 2.07/0.98  --inst_lit_activity_flag                true
% 2.07/0.98  --inst_restr_to_given                   false
% 2.07/0.98  --inst_activity_threshold               500
% 2.07/0.98  --inst_out_proof                        true
% 2.07/0.98  
% 2.07/0.98  ------ Resolution Options
% 2.07/0.98  
% 2.07/0.98  --resolution_flag                       false
% 2.07/0.98  --res_lit_sel                           adaptive
% 2.07/0.98  --res_lit_sel_side                      none
% 2.07/0.98  --res_ordering                          kbo
% 2.07/0.98  --res_to_prop_solver                    active
% 2.07/0.98  --res_prop_simpl_new                    false
% 2.07/0.98  --res_prop_simpl_given                  true
% 2.07/0.98  --res_passive_queue_type                priority_queues
% 2.07/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.07/0.98  --res_passive_queues_freq               [15;5]
% 2.07/0.98  --res_forward_subs                      full
% 2.07/0.98  --res_backward_subs                     full
% 2.07/0.98  --res_forward_subs_resolution           true
% 2.07/0.98  --res_backward_subs_resolution          true
% 2.07/0.98  --res_orphan_elimination                true
% 2.07/0.98  --res_time_limit                        2.
% 2.07/0.98  --res_out_proof                         true
% 2.07/0.98  
% 2.07/0.98  ------ Superposition Options
% 2.07/0.98  
% 2.07/0.98  --superposition_flag                    true
% 2.07/0.98  --sup_passive_queue_type                priority_queues
% 2.07/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.07/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.07/0.98  --demod_completeness_check              fast
% 2.07/0.98  --demod_use_ground                      true
% 2.07/0.98  --sup_to_prop_solver                    passive
% 2.07/0.98  --sup_prop_simpl_new                    true
% 2.07/0.98  --sup_prop_simpl_given                  true
% 2.07/0.98  --sup_fun_splitting                     false
% 2.07/0.98  --sup_smt_interval                      50000
% 2.07/0.98  
% 2.07/0.98  ------ Superposition Simplification Setup
% 2.07/0.98  
% 2.07/0.98  --sup_indices_passive                   []
% 2.07/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.07/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.07/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_full_bw                           [BwDemod]
% 2.07/0.98  --sup_immed_triv                        [TrivRules]
% 2.07/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.07/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_immed_bw_main                     []
% 2.07/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.07/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.07/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.07/0.98  
% 2.07/0.98  ------ Combination Options
% 2.07/0.98  
% 2.07/0.98  --comb_res_mult                         3
% 2.07/0.98  --comb_sup_mult                         2
% 2.07/0.98  --comb_inst_mult                        10
% 2.07/0.98  
% 2.07/0.98  ------ Debug Options
% 2.07/0.98  
% 2.07/0.98  --dbg_backtrace                         false
% 2.07/0.98  --dbg_dump_prop_clauses                 false
% 2.07/0.98  --dbg_dump_prop_clauses_file            -
% 2.07/0.98  --dbg_out_stat                          false
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  ------ Proving...
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  % SZS status Theorem for theBenchmark.p
% 2.07/0.98  
% 2.07/0.98   Resolution empty clause
% 2.07/0.98  
% 2.07/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.07/0.98  
% 2.07/0.98  fof(f10,axiom,(
% 2.07/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f56,plain,(
% 2.07/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.07/0.98    inference(cnf_transformation,[],[f10])).
% 2.07/0.98  
% 2.07/0.98  fof(f9,axiom,(
% 2.07/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f23,plain,(
% 2.07/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.07/0.98    inference(ennf_transformation,[],[f9])).
% 2.07/0.98  
% 2.07/0.98  fof(f54,plain,(
% 2.07/0.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f23])).
% 2.07/0.98  
% 2.07/0.98  fof(f13,axiom,(
% 2.07/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f28,plain,(
% 2.07/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.98    inference(ennf_transformation,[],[f13])).
% 2.07/0.98  
% 2.07/0.98  fof(f60,plain,(
% 2.07/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/0.98    inference(cnf_transformation,[],[f28])).
% 2.07/0.98  
% 2.07/0.98  fof(f6,axiom,(
% 2.07/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f51,plain,(
% 2.07/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.07/0.98    inference(cnf_transformation,[],[f6])).
% 2.07/0.98  
% 2.07/0.98  fof(f2,axiom,(
% 2.07/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f43,plain,(
% 2.07/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f2])).
% 2.07/0.98  
% 2.07/0.98  fof(f1,axiom,(
% 2.07/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f33,plain,(
% 2.07/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.98    inference(nnf_transformation,[],[f1])).
% 2.07/0.98  
% 2.07/0.98  fof(f34,plain,(
% 2.07/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.07/0.98    inference(flattening,[],[f33])).
% 2.07/0.98  
% 2.07/0.98  fof(f42,plain,(
% 2.07/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f34])).
% 2.07/0.98  
% 2.07/0.98  fof(f16,conjecture,(
% 2.07/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f17,negated_conjecture,(
% 2.07/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.07/0.98    inference(negated_conjecture,[],[f16])).
% 2.07/0.98  
% 2.07/0.98  fof(f18,plain,(
% 2.07/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.07/0.98    inference(pure_predicate_removal,[],[f17])).
% 2.07/0.98  
% 2.07/0.98  fof(f31,plain,(
% 2.07/0.98    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.07/0.98    inference(ennf_transformation,[],[f18])).
% 2.07/0.98  
% 2.07/0.98  fof(f32,plain,(
% 2.07/0.98    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.07/0.98    inference(flattening,[],[f31])).
% 2.07/0.98  
% 2.07/0.98  fof(f38,plain,(
% 2.07/0.98    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.07/0.98    introduced(choice_axiom,[])).
% 2.07/0.98  
% 2.07/0.98  fof(f39,plain,(
% 2.07/0.98    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.07/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f38])).
% 2.07/0.98  
% 2.07/0.98  fof(f64,plain,(
% 2.07/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.07/0.98    inference(cnf_transformation,[],[f39])).
% 2.07/0.98  
% 2.07/0.98  fof(f3,axiom,(
% 2.07/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f44,plain,(
% 2.07/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f3])).
% 2.07/0.98  
% 2.07/0.98  fof(f4,axiom,(
% 2.07/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f45,plain,(
% 2.07/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f4])).
% 2.07/0.98  
% 2.07/0.98  fof(f67,plain,(
% 2.07/0.98    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.07/0.98    inference(definition_unfolding,[],[f44,f45])).
% 2.07/0.98  
% 2.07/0.98  fof(f75,plain,(
% 2.07/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 2.07/0.98    inference(definition_unfolding,[],[f64,f67])).
% 2.07/0.98  
% 2.07/0.98  fof(f14,axiom,(
% 2.07/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f19,plain,(
% 2.07/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.07/0.98    inference(pure_predicate_removal,[],[f14])).
% 2.07/0.98  
% 2.07/0.98  fof(f29,plain,(
% 2.07/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.98    inference(ennf_transformation,[],[f19])).
% 2.07/0.98  
% 2.07/0.98  fof(f61,plain,(
% 2.07/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/0.98    inference(cnf_transformation,[],[f29])).
% 2.07/0.98  
% 2.07/0.98  fof(f8,axiom,(
% 2.07/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f22,plain,(
% 2.07/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.07/0.98    inference(ennf_transformation,[],[f8])).
% 2.07/0.98  
% 2.07/0.98  fof(f37,plain,(
% 2.07/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.07/0.98    inference(nnf_transformation,[],[f22])).
% 2.07/0.98  
% 2.07/0.98  fof(f52,plain,(
% 2.07/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f37])).
% 2.07/0.98  
% 2.07/0.98  fof(f5,axiom,(
% 2.07/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f21,plain,(
% 2.07/0.98    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.07/0.98    inference(ennf_transformation,[],[f5])).
% 2.07/0.98  
% 2.07/0.98  fof(f35,plain,(
% 2.07/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.07/0.98    inference(nnf_transformation,[],[f21])).
% 2.07/0.98  
% 2.07/0.98  fof(f36,plain,(
% 2.07/0.98    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.07/0.98    inference(flattening,[],[f35])).
% 2.07/0.98  
% 2.07/0.98  fof(f46,plain,(
% 2.07/0.98    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 2.07/0.98    inference(cnf_transformation,[],[f36])).
% 2.07/0.98  
% 2.07/0.98  fof(f72,plain,(
% 2.07/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X1,X1,X2) = X0 | k1_enumset1(X2,X2,X2) = X0 | k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_enumset1(X1,X1,X2))) )),
% 2.07/0.98    inference(definition_unfolding,[],[f46,f45,f67,f67,f45])).
% 2.07/0.98  
% 2.07/0.98  fof(f66,plain,(
% 2.07/0.98    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.07/0.98    inference(cnf_transformation,[],[f39])).
% 2.07/0.98  
% 2.07/0.98  fof(f74,plain,(
% 2.07/0.98    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.07/0.98    inference(definition_unfolding,[],[f66,f67,f67])).
% 2.07/0.98  
% 2.07/0.98  fof(f15,axiom,(
% 2.07/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f30,plain,(
% 2.07/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.07/0.98    inference(ennf_transformation,[],[f15])).
% 2.07/0.98  
% 2.07/0.98  fof(f62,plain,(
% 2.07/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.07/0.98    inference(cnf_transformation,[],[f30])).
% 2.07/0.98  
% 2.07/0.98  fof(f12,axiom,(
% 2.07/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f26,plain,(
% 2.07/0.98    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.07/0.98    inference(ennf_transformation,[],[f12])).
% 2.07/0.98  
% 2.07/0.98  fof(f27,plain,(
% 2.07/0.98    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.07/0.98    inference(flattening,[],[f26])).
% 2.07/0.98  
% 2.07/0.98  fof(f59,plain,(
% 2.07/0.98    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f27])).
% 2.07/0.98  
% 2.07/0.98  fof(f73,plain,(
% 2.07/0.98    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_enumset1(X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.07/0.98    inference(definition_unfolding,[],[f59,f67,f67])).
% 2.07/0.98  
% 2.07/0.98  fof(f63,plain,(
% 2.07/0.98    v1_funct_1(sK3)),
% 2.07/0.98    inference(cnf_transformation,[],[f39])).
% 2.07/0.98  
% 2.07/0.98  fof(f11,axiom,(
% 2.07/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.07/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.07/0.98  
% 2.07/0.98  fof(f24,plain,(
% 2.07/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.07/0.98    inference(ennf_transformation,[],[f11])).
% 2.07/0.98  
% 2.07/0.98  fof(f25,plain,(
% 2.07/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.07/0.98    inference(flattening,[],[f24])).
% 2.07/0.98  
% 2.07/0.98  fof(f57,plain,(
% 2.07/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.07/0.98    inference(cnf_transformation,[],[f25])).
% 2.07/0.98  
% 2.07/0.98  cnf(c_13,plain,
% 2.07/0.98      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.07/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_12,plain,
% 2.07/0.98      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.07/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1081,plain,
% 2.07/0.98      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 2.07/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1761,plain,
% 2.07/0.98      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 2.07/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_13,c_1081]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_18,plain,
% 2.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.07/0.98      inference(cnf_transformation,[],[f60]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1207,plain,
% 2.07/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.07/0.98      | v1_relat_1(k1_xboole_0) ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1209,plain,
% 2.07/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.07/0.98      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_9,plain,
% 2.07/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.07/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1208,plain,
% 2.07/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1211,plain,
% 2.07/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_1208]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1766,plain,
% 2.07/0.98      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 2.07/0.98      inference(global_propositional_subsumption,
% 2.07/0.98                [status(thm)],
% 2.07/0.98                [c_1761,c_1209,c_1211]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_3,plain,
% 2.07/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 2.07/0.98      inference(cnf_transformation,[],[f43]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1088,plain,
% 2.07/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_0,plain,
% 2.07/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.07/0.98      inference(cnf_transformation,[],[f42]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1090,plain,
% 2.07/0.98      ( X0 = X1
% 2.07/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.07/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1916,plain,
% 2.07/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_1088,c_1090]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2199,plain,
% 2.07/0.98      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_1766,c_1916]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_23,negated_conjecture,
% 2.07/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
% 2.07/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1075,plain,
% 2.07/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_19,plain,
% 2.07/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.07/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_11,plain,
% 2.07/0.98      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.07/0.98      inference(cnf_transformation,[],[f52]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_341,plain,
% 2.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 2.07/0.98      | ~ v1_relat_1(X0) ),
% 2.07/0.98      inference(resolution,[status(thm)],[c_19,c_11]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_345,plain,
% 2.07/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 2.07/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.07/0.98      inference(global_propositional_subsumption,[status(thm)],[c_341,c_18]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_346,plain,
% 2.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.07/0.98      inference(renaming,[status(thm)],[c_345]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1073,plain,
% 2.07/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.07/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1376,plain,
% 2.07/0.98      ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_1075,c_1073]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_8,plain,
% 2.07/0.98      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X2))
% 2.07/0.98      | k1_enumset1(X1,X1,X2) = X0
% 2.07/0.98      | k1_enumset1(X2,X2,X2) = X0
% 2.07/0.98      | k1_enumset1(X1,X1,X1) = X0
% 2.07/0.98      | k1_xboole_0 = X0 ),
% 2.07/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1083,plain,
% 2.07/0.98      ( k1_enumset1(X0,X0,X1) = X2
% 2.07/0.98      | k1_enumset1(X1,X1,X1) = X2
% 2.07/0.98      | k1_enumset1(X0,X0,X0) = X2
% 2.07/0.98      | k1_xboole_0 = X2
% 2.07/0.98      | r1_tarski(X2,k1_enumset1(X0,X0,X1)) != iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1906,plain,
% 2.07/0.98      ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.07/0.98      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_1376,c_1083]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2450,plain,
% 2.07/0.98      ( k1_relat_1(sK3) = k1_xboole_0
% 2.07/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_1906,c_1075]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_21,negated_conjecture,
% 2.07/0.98      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.07/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1215,plain,
% 2.07/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 2.07/0.98      | v1_relat_1(sK3) ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_18]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_20,plain,
% 2.07/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.07/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.07/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1243,plain,
% 2.07/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 2.07/0.98      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1301,plain,
% 2.07/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 2.07/0.98      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_1243]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1409,plain,
% 2.07/0.98      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_752,plain,
% 2.07/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.07/0.98      theory(equality) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1236,plain,
% 2.07/0.98      ( ~ r1_tarski(X0,X1)
% 2.07/0.98      | r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.07/0.98      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 2.07/0.98      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_752]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1300,plain,
% 2.07/0.98      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.07/0.98      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 2.07/0.98      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.07/0.98      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_1236]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1410,plain,
% 2.07/0.98      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.07/0.98      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.07/0.98      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.07/0.98      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_1300]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_17,plain,
% 2.07/0.98      ( ~ v1_funct_1(X0)
% 2.07/0.98      | ~ v1_relat_1(X0)
% 2.07/0.98      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 2.07/0.98      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.07/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_24,negated_conjecture,
% 2.07/0.98      ( v1_funct_1(sK3) ),
% 2.07/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_244,plain,
% 2.07/0.98      ( ~ v1_relat_1(X0)
% 2.07/0.98      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 2.07/0.98      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.07/0.98      | sK3 != X0 ),
% 2.07/0.98      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_245,plain,
% 2.07/0.98      ( ~ v1_relat_1(sK3)
% 2.07/0.98      | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 2.07/0.98      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.07/0.98      inference(unflattening,[status(thm)],[c_244]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1074,plain,
% 2.07/0.98      ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 2.07/0.98      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.07/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_26,plain,
% 2.07/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_246,plain,
% 2.07/0.98      ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 2.07/0.98      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.07/0.98      | v1_relat_1(sK3) != iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_245]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1216,plain,
% 2.07/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) != iProver_top
% 2.07/0.98      | v1_relat_1(sK3) = iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_1215]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1229,plain,
% 2.07/0.98      ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.07/0.98      | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3) ),
% 2.07/0.98      inference(global_propositional_subsumption,
% 2.07/0.98                [status(thm)],
% 2.07/0.98                [c_1074,c_26,c_246,c_1216]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1230,plain,
% 2.07/0.98      ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 2.07/0.98      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.07/0.98      inference(renaming,[status(thm)],[c_1229]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2445,plain,
% 2.07/0.98      ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.07/0.98      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_1906,c_1230]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2496,plain,
% 2.07/0.98      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.07/0.98      inference(global_propositional_subsumption,
% 2.07/0.98                [status(thm)],
% 2.07/0.98                [c_2450,c_23,c_21,c_1215,c_1301,c_1409,c_1410,c_2445]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_16,plain,
% 2.07/0.98      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.07/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1079,plain,
% 2.07/0.98      ( k1_relat_1(X0) != k1_xboole_0
% 2.07/0.98      | k1_xboole_0 = X0
% 2.07/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2514,plain,
% 2.07/0.98      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_2496,c_1079]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1315,plain,
% 2.07/0.98      ( ~ v1_relat_1(sK3)
% 2.07/0.98      | k1_relat_1(sK3) != k1_xboole_0
% 2.07/0.98      | k1_xboole_0 = sK3 ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_750,plain,( X0 = X0 ),theory(equality) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1328,plain,
% 2.07/0.98      ( sK3 = sK3 ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_750]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_751,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1516,plain,
% 2.07/0.98      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_751]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2154,plain,
% 2.07/0.98      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_1516]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2155,plain,
% 2.07/0.98      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.07/0.98      inference(instantiation,[status(thm)],[c_2154]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2542,plain,
% 2.07/0.98      ( sK3 = k1_xboole_0 ),
% 2.07/0.98      inference(global_propositional_subsumption,
% 2.07/0.98                [status(thm)],
% 2.07/0.98                [c_2514,c_23,c_21,c_1215,c_1301,c_1315,c_1328,c_1409,c_1410,
% 2.07/0.98                 c_2155,c_2445]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1077,plain,
% 2.07/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.07/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2107,plain,
% 2.07/0.98      ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.07/0.98      inference(superposition,[status(thm)],[c_1075,c_1077]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_1076,plain,
% 2.07/0.98      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.07/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2204,plain,
% 2.07/0.98      ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.07/0.98      inference(demodulation,[status(thm)],[c_2107,c_1076]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2546,plain,
% 2.07/0.98      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.07/0.98      inference(demodulation,[status(thm)],[c_2542,c_2204]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_2857,plain,
% 2.07/0.98      ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.07/0.98      inference(demodulation,[status(thm)],[c_2199,c_2546]) ).
% 2.07/0.98  
% 2.07/0.98  cnf(c_3024,plain,
% 2.07/0.98      ( $false ),
% 2.07/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_2857,c_1088]) ).
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.07/0.98  
% 2.07/0.98  ------                               Statistics
% 2.07/0.98  
% 2.07/0.98  ------ General
% 2.07/0.98  
% 2.07/0.98  abstr_ref_over_cycles:                  0
% 2.07/0.98  abstr_ref_under_cycles:                 0
% 2.07/0.98  gc_basic_clause_elim:                   0
% 2.07/0.98  forced_gc_time:                         0
% 2.07/0.98  parsing_time:                           0.01
% 2.07/0.98  unif_index_cands_time:                  0.
% 2.07/0.98  unif_index_add_time:                    0.
% 2.07/0.98  orderings_time:                         0.
% 2.07/0.98  out_proof_time:                         0.011
% 2.07/0.98  total_time:                             0.121
% 2.07/0.98  num_of_symbols:                         49
% 2.07/0.98  num_of_terms:                           2332
% 2.07/0.98  
% 2.07/0.98  ------ Preprocessing
% 2.07/0.98  
% 2.07/0.98  num_of_splits:                          0
% 2.07/0.98  num_of_split_atoms:                     0
% 2.07/0.98  num_of_reused_defs:                     0
% 2.07/0.98  num_eq_ax_congr_red:                    9
% 2.07/0.98  num_of_sem_filtered_clauses:            1
% 2.07/0.98  num_of_subtypes:                        0
% 2.07/0.98  monotx_restored_types:                  0
% 2.07/0.98  sat_num_of_epr_types:                   0
% 2.07/0.98  sat_num_of_non_cyclic_types:            0
% 2.07/0.98  sat_guarded_non_collapsed_types:        0
% 2.07/0.98  num_pure_diseq_elim:                    0
% 2.07/0.98  simp_replaced_by:                       0
% 2.07/0.98  res_preprocessed:                       112
% 2.07/0.98  prep_upred:                             0
% 2.07/0.98  prep_unflattend:                        21
% 2.07/0.98  smt_new_axioms:                         0
% 2.07/0.98  pred_elim_cands:                        3
% 2.07/0.98  pred_elim:                              2
% 2.07/0.98  pred_elim_cl:                           3
% 2.07/0.98  pred_elim_cycles:                       7
% 2.07/0.98  merged_defs:                            0
% 2.07/0.98  merged_defs_ncl:                        0
% 2.07/0.98  bin_hyper_res:                          0
% 2.07/0.98  prep_cycles:                            4
% 2.07/0.98  pred_elim_time:                         0.005
% 2.07/0.98  splitting_time:                         0.
% 2.07/0.98  sem_filter_time:                        0.
% 2.07/0.98  monotx_time:                            0.001
% 2.07/0.98  subtype_inf_time:                       0.
% 2.07/0.98  
% 2.07/0.98  ------ Problem properties
% 2.07/0.98  
% 2.07/0.98  clauses:                                21
% 2.07/0.98  conjectures:                            3
% 2.07/0.98  epr:                                    4
% 2.07/0.98  horn:                                   20
% 2.07/0.98  ground:                                 5
% 2.07/0.98  unary:                                  12
% 2.07/0.98  binary:                                 4
% 2.07/0.98  lits:                                   37
% 2.07/0.98  lits_eq:                                15
% 2.07/0.98  fd_pure:                                0
% 2.07/0.98  fd_pseudo:                              0
% 2.07/0.98  fd_cond:                                2
% 2.07/0.98  fd_pseudo_cond:                         2
% 2.07/0.98  ac_symbols:                             0
% 2.07/0.98  
% 2.07/0.98  ------ Propositional Solver
% 2.07/0.98  
% 2.07/0.98  prop_solver_calls:                      27
% 2.07/0.98  prop_fast_solver_calls:                 605
% 2.07/0.98  smt_solver_calls:                       0
% 2.07/0.98  smt_fast_solver_calls:                  0
% 2.07/0.98  prop_num_of_clauses:                    1068
% 2.07/0.98  prop_preprocess_simplified:             4278
% 2.07/0.98  prop_fo_subsumed:                       10
% 2.07/0.98  prop_solver_time:                       0.
% 2.07/0.98  smt_solver_time:                        0.
% 2.07/0.98  smt_fast_solver_time:                   0.
% 2.07/0.98  prop_fast_solver_time:                  0.
% 2.07/0.98  prop_unsat_core_time:                   0.
% 2.07/0.98  
% 2.07/0.98  ------ QBF
% 2.07/0.98  
% 2.07/0.98  qbf_q_res:                              0
% 2.07/0.98  qbf_num_tautologies:                    0
% 2.07/0.98  qbf_prep_cycles:                        0
% 2.07/0.98  
% 2.07/0.98  ------ BMC1
% 2.07/0.98  
% 2.07/0.98  bmc1_current_bound:                     -1
% 2.07/0.98  bmc1_last_solved_bound:                 -1
% 2.07/0.98  bmc1_unsat_core_size:                   -1
% 2.07/0.98  bmc1_unsat_core_parents_size:           -1
% 2.07/0.98  bmc1_merge_next_fun:                    0
% 2.07/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.07/0.98  
% 2.07/0.98  ------ Instantiation
% 2.07/0.98  
% 2.07/0.98  inst_num_of_clauses:                    358
% 2.07/0.98  inst_num_in_passive:                    126
% 2.07/0.98  inst_num_in_active:                     158
% 2.07/0.98  inst_num_in_unprocessed:                74
% 2.07/0.98  inst_num_of_loops:                      190
% 2.07/0.98  inst_num_of_learning_restarts:          0
% 2.07/0.98  inst_num_moves_active_passive:          30
% 2.07/0.98  inst_lit_activity:                      0
% 2.07/0.98  inst_lit_activity_moves:                0
% 2.07/0.98  inst_num_tautologies:                   0
% 2.07/0.98  inst_num_prop_implied:                  0
% 2.07/0.98  inst_num_existing_simplified:           0
% 2.07/0.98  inst_num_eq_res_simplified:             0
% 2.07/0.98  inst_num_child_elim:                    0
% 2.07/0.98  inst_num_of_dismatching_blockings:      38
% 2.07/0.98  inst_num_of_non_proper_insts:           262
% 2.07/0.98  inst_num_of_duplicates:                 0
% 2.07/0.98  inst_inst_num_from_inst_to_res:         0
% 2.07/0.98  inst_dismatching_checking_time:         0.
% 2.07/0.98  
% 2.07/0.98  ------ Resolution
% 2.07/0.98  
% 2.07/0.98  res_num_of_clauses:                     0
% 2.07/0.98  res_num_in_passive:                     0
% 2.07/0.98  res_num_in_active:                      0
% 2.07/0.98  res_num_of_loops:                       116
% 2.07/0.98  res_forward_subset_subsumed:            40
% 2.07/0.98  res_backward_subset_subsumed:           0
% 2.07/0.98  res_forward_subsumed:                   0
% 2.07/0.98  res_backward_subsumed:                  0
% 2.07/0.98  res_forward_subsumption_resolution:     0
% 2.07/0.98  res_backward_subsumption_resolution:    0
% 2.07/0.98  res_clause_to_clause_subsumption:       125
% 2.07/0.98  res_orphan_elimination:                 0
% 2.07/0.98  res_tautology_del:                      13
% 2.07/0.98  res_num_eq_res_simplified:              0
% 2.07/0.98  res_num_sel_changes:                    0
% 2.07/0.98  res_moves_from_active_to_pass:          0
% 2.07/0.98  
% 2.07/0.98  ------ Superposition
% 2.07/0.98  
% 2.07/0.98  sup_time_total:                         0.
% 2.07/0.98  sup_time_generating:                    0.
% 2.07/0.98  sup_time_sim_full:                      0.
% 2.07/0.98  sup_time_sim_immed:                     0.
% 2.07/0.98  
% 2.07/0.98  sup_num_of_clauses:                     29
% 2.07/0.98  sup_num_in_active:                      23
% 2.07/0.98  sup_num_in_passive:                     6
% 2.07/0.98  sup_num_of_loops:                       36
% 2.07/0.98  sup_fw_superposition:                   26
% 2.07/0.98  sup_bw_superposition:                   13
% 2.07/0.98  sup_immediate_simplified:               8
% 2.07/0.98  sup_given_eliminated:                   0
% 2.07/0.98  comparisons_done:                       0
% 2.07/0.98  comparisons_avoided:                    0
% 2.07/0.98  
% 2.07/0.98  ------ Simplifications
% 2.07/0.98  
% 2.07/0.98  
% 2.07/0.98  sim_fw_subset_subsumed:                 1
% 2.07/0.98  sim_bw_subset_subsumed:                 4
% 2.07/0.98  sim_fw_subsumed:                        8
% 2.07/0.98  sim_bw_subsumed:                        0
% 2.07/0.98  sim_fw_subsumption_res:                 1
% 2.07/0.98  sim_bw_subsumption_res:                 0
% 2.07/0.98  sim_tautology_del:                      0
% 2.07/0.98  sim_eq_tautology_del:                   9
% 2.07/0.98  sim_eq_res_simp:                        0
% 2.07/0.98  sim_fw_demodulated:                     0
% 2.07/0.98  sim_bw_demodulated:                     13
% 2.07/0.98  sim_light_normalised:                   3
% 2.07/0.98  sim_joinable_taut:                      0
% 2.07/0.98  sim_joinable_simp:                      0
% 2.07/0.98  sim_ac_normalised:                      0
% 2.07/0.98  sim_smt_subsumption:                    0
% 2.07/0.98  
%------------------------------------------------------------------------------
