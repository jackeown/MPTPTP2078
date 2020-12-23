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
% DateTime   : Thu Dec  3 12:05:42 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 746 expanded)
%              Number of clauses        :   94 ( 226 expanded)
%              Number of leaves         :   21 ( 167 expanded)
%              Depth                    :   23
%              Number of atoms          :  361 (1697 expanded)
%              Number of equality atoms :  207 ( 690 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f19,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f38])).

fof(f62,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f66,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f41,f65])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f62,f66])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f64,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f64,f66,f66])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f57,f66,f66])).

fof(f61,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

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
    inference(nnf_transformation,[],[f22])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f44,f65,f66,f66,f65])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_16,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_236,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_16,c_9])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_240,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_236,c_16,c_15,c_9])).

cnf(c_20,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_286,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_240,c_20])).

cnf(c_287,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_286])).

cnf(c_1000,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k7_relat_1(sK3,X0_47) = sK3 ),
    inference(subtyping,[status(esa)],[c_287])).

cnf(c_1421,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_1000])).

cnf(c_304,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_20])).

cnf(c_305,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_304])).

cnf(c_998,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_305])).

cnf(c_1314,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_998])).

cnf(c_1021,plain,
    ( X0_48 = X0_48 ),
    theory(equality)).

cnf(c_1422,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_1425,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_998])).

cnf(c_1426,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1425])).

cnf(c_1479,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1314,c_1422,c_1426])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1011,plain,
    ( ~ v1_relat_1(X0_47)
    | k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1308,plain,
    ( k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47)
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1011])).

cnf(c_1994,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0_47)) = k9_relat_1(sK3,X0_47) ),
    inference(superposition,[status(thm)],[c_1479,c_1308])).

cnf(c_2157,plain,
    ( k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1421,c_1994])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1008,plain,
    ( ~ v1_relat_1(X0_47)
    | k2_relat_1(X0_47) != k1_xboole_0
    | k1_xboole_0 = X0_47 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1309,plain,
    ( k2_relat_1(X0_47) != k1_xboole_0
    | k1_xboole_0 = X0_47
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_2158,plain,
    ( k7_relat_1(sK3,X0_47) = k1_xboole_0
    | k9_relat_1(sK3,X0_47) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,X0_47)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1994,c_1309])).

cnf(c_2313,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2157,c_2158])).

cnf(c_2314,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
    | k2_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2313,c_1421])).

cnf(c_2315,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2314,c_1421])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_295,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_20])).

cnf(c_296,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_295])).

cnf(c_999,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k7_relset_1(X0_47,X1_47,sK3,X2_47) = k9_relat_1(sK3,X2_47) ),
    inference(subtyping,[status(esa)],[c_296])).

cnf(c_1450,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0_47) = k9_relat_1(sK3,X0_47) ),
    inference(equality_resolution,[status(thm)],[c_999])).

cnf(c_18,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1006,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1311,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1006])).

cnf(c_1466,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1450,c_1311])).

cnf(c_1467,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1466])).

cnf(c_1020,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1780,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_1809,plain,
    ( k9_relat_1(sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_14,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_21,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_221,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_222,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_221])).

cnf(c_1004,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50)))
    | ~ v1_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_222])).

cnf(c_1312,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1004])).

cnf(c_1070,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1004])).

cnf(c_1607,plain,
    ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1312,c_1070,c_1422,c_1426])).

cnf(c_1614,plain,
    ( r1_tarski(k2_relat_1(sK3),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1421,c_1607])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1013,plain,
    ( ~ r1_tarski(X0_47,k2_enumset1(X0_50,X0_50,X0_50,X1_50))
    | k2_enumset1(X1_50,X1_50,X1_50,X1_50) = X0_47
    | k2_enumset1(X0_50,X0_50,X0_50,X1_50) = X0_47
    | k2_enumset1(X0_50,X0_50,X0_50,X0_50) = X0_47
    | k1_xboole_0 = X0_47 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1306,plain,
    ( k2_enumset1(X0_50,X0_50,X0_50,X0_50) = X0_47
    | k2_enumset1(X1_50,X1_50,X1_50,X0_50) = X0_47
    | k2_enumset1(X1_50,X1_50,X1_50,X1_50) = X0_47
    | k1_xboole_0 = X0_47
    | r1_tarski(X0_47,k2_enumset1(X1_50,X1_50,X1_50,X0_50)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_1917,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1614,c_1306])).

cnf(c_7,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1012,plain,
    ( r1_tarski(k9_relat_1(X0_47,X1_47),k2_relat_1(X0_47))
    | ~ v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1945,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_2029,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_1008])).

cnf(c_1024,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1782,plain,
    ( X0_47 != X1_47
    | sK3 != X1_47
    | sK3 = X0_47 ),
    inference(instantiation,[status(thm)],[c_1024])).

cnf(c_2112,plain,
    ( X0_47 != sK3
    | sK3 = X0_47
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1782])).

cnf(c_2113,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2112])).

cnf(c_1026,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | r1_tarski(X2_47,X3_47)
    | X2_47 != X0_47
    | X3_47 != X1_47 ),
    theory(equality)).

cnf(c_1616,plain,
    ( ~ r1_tarski(X0_47,X1_47)
    | r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1_47
    | k9_relat_1(sK3,sK2) != X0_47 ),
    inference(instantiation,[status(thm)],[c_1026])).

cnf(c_1808,plain,
    ( ~ r1_tarski(k9_relat_1(sK3,sK2),X0_47)
    | r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0_47
    | k9_relat_1(sK3,sK2) != k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1616])).

cnf(c_2210,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3)
    | k9_relat_1(sK3,sK2) != k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1808])).

cnf(c_2424,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2315,c_1422,c_1425,c_1467,c_1780,c_1809,c_1917,c_1945,c_2029,c_2113,c_2210])).

cnf(c_2434,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2424,c_1466])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_274,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_275,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
    inference(unflattening,[status(thm)],[c_274])).

cnf(c_1001,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_275])).

cnf(c_1313,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1001])).

cnf(c_1429,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(instantiation,[status(thm)],[c_1001])).

cnf(c_1431,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1429])).

cnf(c_1430,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) = k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(instantiation,[status(thm)],[c_1021])).

cnf(c_1828,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1313,c_1431,c_1430])).

cnf(c_1993,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0_47)) = k9_relat_1(k1_xboole_0,X0_47) ),
    inference(superposition,[status(thm)],[c_1828,c_1308])).

cnf(c_10,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1010,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_256,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_240])).

cnf(c_257,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_1003,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
    | k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_257])).

cnf(c_1542,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
    | k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1003])).

cnf(c_1833,plain,
    ( k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1003,c_1430,c_1542])).

cnf(c_1998,plain,
    ( k9_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1993,c_1010,c_1833])).

cnf(c_2448,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2434,c_1998])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1018,plain,
    ( r1_tarski(k1_xboole_0,X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1301,plain,
    ( r1_tarski(k1_xboole_0,X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1018])).

cnf(c_2545,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2448,c_1301])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.16/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/0.99  
% 2.16/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.16/0.99  
% 2.16/0.99  ------  iProver source info
% 2.16/0.99  
% 2.16/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.16/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.16/0.99  git: non_committed_changes: false
% 2.16/0.99  git: last_make_outside_of_git: false
% 2.16/0.99  
% 2.16/0.99  ------ 
% 2.16/0.99  
% 2.16/0.99  ------ Input Options
% 2.16/0.99  
% 2.16/0.99  --out_options                           all
% 2.16/0.99  --tptp_safe_out                         true
% 2.16/0.99  --problem_path                          ""
% 2.16/0.99  --include_path                          ""
% 2.16/0.99  --clausifier                            res/vclausify_rel
% 2.16/0.99  --clausifier_options                    --mode clausify
% 2.16/0.99  --stdin                                 false
% 2.16/0.99  --stats_out                             all
% 2.16/0.99  
% 2.16/0.99  ------ General Options
% 2.16/0.99  
% 2.16/0.99  --fof                                   false
% 2.16/0.99  --time_out_real                         305.
% 2.16/0.99  --time_out_virtual                      -1.
% 2.16/0.99  --symbol_type_check                     false
% 2.16/0.99  --clausify_out                          false
% 2.16/0.99  --sig_cnt_out                           false
% 2.16/0.99  --trig_cnt_out                          false
% 2.16/0.99  --trig_cnt_out_tolerance                1.
% 2.16/0.99  --trig_cnt_out_sk_spl                   false
% 2.16/0.99  --abstr_cl_out                          false
% 2.16/0.99  
% 2.16/0.99  ------ Global Options
% 2.16/0.99  
% 2.16/0.99  --schedule                              default
% 2.16/0.99  --add_important_lit                     false
% 2.16/0.99  --prop_solver_per_cl                    1000
% 2.16/0.99  --min_unsat_core                        false
% 2.16/0.99  --soft_assumptions                      false
% 2.16/0.99  --soft_lemma_size                       3
% 2.16/0.99  --prop_impl_unit_size                   0
% 2.16/0.99  --prop_impl_unit                        []
% 2.16/0.99  --share_sel_clauses                     true
% 2.16/0.99  --reset_solvers                         false
% 2.16/0.99  --bc_imp_inh                            [conj_cone]
% 2.16/0.99  --conj_cone_tolerance                   3.
% 2.16/0.99  --extra_neg_conj                        none
% 2.16/0.99  --large_theory_mode                     true
% 2.16/0.99  --prolific_symb_bound                   200
% 2.16/0.99  --lt_threshold                          2000
% 2.16/0.99  --clause_weak_htbl                      true
% 2.16/0.99  --gc_record_bc_elim                     false
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing Options
% 2.16/0.99  
% 2.16/0.99  --preprocessing_flag                    true
% 2.16/0.99  --time_out_prep_mult                    0.1
% 2.16/0.99  --splitting_mode                        input
% 2.16/0.99  --splitting_grd                         true
% 2.16/0.99  --splitting_cvd                         false
% 2.16/0.99  --splitting_cvd_svl                     false
% 2.16/0.99  --splitting_nvd                         32
% 2.16/0.99  --sub_typing                            true
% 2.16/0.99  --prep_gs_sim                           true
% 2.16/0.99  --prep_unflatten                        true
% 2.16/0.99  --prep_res_sim                          true
% 2.16/0.99  --prep_upred                            true
% 2.16/0.99  --prep_sem_filter                       exhaustive
% 2.16/0.99  --prep_sem_filter_out                   false
% 2.16/0.99  --pred_elim                             true
% 2.16/0.99  --res_sim_input                         true
% 2.16/0.99  --eq_ax_congr_red                       true
% 2.16/0.99  --pure_diseq_elim                       true
% 2.16/0.99  --brand_transform                       false
% 2.16/0.99  --non_eq_to_eq                          false
% 2.16/0.99  --prep_def_merge                        true
% 2.16/0.99  --prep_def_merge_prop_impl              false
% 2.16/0.99  --prep_def_merge_mbd                    true
% 2.16/0.99  --prep_def_merge_tr_red                 false
% 2.16/0.99  --prep_def_merge_tr_cl                  false
% 2.16/0.99  --smt_preprocessing                     true
% 2.16/0.99  --smt_ac_axioms                         fast
% 2.16/0.99  --preprocessed_out                      false
% 2.16/0.99  --preprocessed_stats                    false
% 2.16/0.99  
% 2.16/0.99  ------ Abstraction refinement Options
% 2.16/0.99  
% 2.16/0.99  --abstr_ref                             []
% 2.16/0.99  --abstr_ref_prep                        false
% 2.16/0.99  --abstr_ref_until_sat                   false
% 2.16/0.99  --abstr_ref_sig_restrict                funpre
% 2.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/0.99  --abstr_ref_under                       []
% 2.16/0.99  
% 2.16/0.99  ------ SAT Options
% 2.16/0.99  
% 2.16/0.99  --sat_mode                              false
% 2.16/0.99  --sat_fm_restart_options                ""
% 2.16/0.99  --sat_gr_def                            false
% 2.16/0.99  --sat_epr_types                         true
% 2.16/0.99  --sat_non_cyclic_types                  false
% 2.16/0.99  --sat_finite_models                     false
% 2.16/0.99  --sat_fm_lemmas                         false
% 2.16/0.99  --sat_fm_prep                           false
% 2.16/0.99  --sat_fm_uc_incr                        true
% 2.16/0.99  --sat_out_model                         small
% 2.16/0.99  --sat_out_clauses                       false
% 2.16/0.99  
% 2.16/0.99  ------ QBF Options
% 2.16/0.99  
% 2.16/0.99  --qbf_mode                              false
% 2.16/0.99  --qbf_elim_univ                         false
% 2.16/0.99  --qbf_dom_inst                          none
% 2.16/0.99  --qbf_dom_pre_inst                      false
% 2.16/0.99  --qbf_sk_in                             false
% 2.16/0.99  --qbf_pred_elim                         true
% 2.16/0.99  --qbf_split                             512
% 2.16/0.99  
% 2.16/0.99  ------ BMC1 Options
% 2.16/0.99  
% 2.16/0.99  --bmc1_incremental                      false
% 2.16/0.99  --bmc1_axioms                           reachable_all
% 2.16/0.99  --bmc1_min_bound                        0
% 2.16/0.99  --bmc1_max_bound                        -1
% 2.16/0.99  --bmc1_max_bound_default                -1
% 2.16/0.99  --bmc1_symbol_reachability              true
% 2.16/0.99  --bmc1_property_lemmas                  false
% 2.16/0.99  --bmc1_k_induction                      false
% 2.16/0.99  --bmc1_non_equiv_states                 false
% 2.16/0.99  --bmc1_deadlock                         false
% 2.16/0.99  --bmc1_ucm                              false
% 2.16/0.99  --bmc1_add_unsat_core                   none
% 2.16/0.99  --bmc1_unsat_core_children              false
% 2.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/0.99  --bmc1_out_stat                         full
% 2.16/0.99  --bmc1_ground_init                      false
% 2.16/0.99  --bmc1_pre_inst_next_state              false
% 2.16/0.99  --bmc1_pre_inst_state                   false
% 2.16/0.99  --bmc1_pre_inst_reach_state             false
% 2.16/0.99  --bmc1_out_unsat_core                   false
% 2.16/0.99  --bmc1_aig_witness_out                  false
% 2.16/0.99  --bmc1_verbose                          false
% 2.16/0.99  --bmc1_dump_clauses_tptp                false
% 2.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.16/0.99  --bmc1_dump_file                        -
% 2.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.16/0.99  --bmc1_ucm_extend_mode                  1
% 2.16/0.99  --bmc1_ucm_init_mode                    2
% 2.16/0.99  --bmc1_ucm_cone_mode                    none
% 2.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.16/0.99  --bmc1_ucm_relax_model                  4
% 2.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/0.99  --bmc1_ucm_layered_model                none
% 2.16/0.99  --bmc1_ucm_max_lemma_size               10
% 2.16/0.99  
% 2.16/0.99  ------ AIG Options
% 2.16/0.99  
% 2.16/0.99  --aig_mode                              false
% 2.16/0.99  
% 2.16/0.99  ------ Instantiation Options
% 2.16/0.99  
% 2.16/0.99  --instantiation_flag                    true
% 2.16/0.99  --inst_sos_flag                         false
% 2.16/0.99  --inst_sos_phase                        true
% 2.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/0.99  --inst_lit_sel_side                     num_symb
% 2.16/0.99  --inst_solver_per_active                1400
% 2.16/0.99  --inst_solver_calls_frac                1.
% 2.16/0.99  --inst_passive_queue_type               priority_queues
% 2.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/0.99  --inst_passive_queues_freq              [25;2]
% 2.16/0.99  --inst_dismatching                      true
% 2.16/0.99  --inst_eager_unprocessed_to_passive     true
% 2.16/0.99  --inst_prop_sim_given                   true
% 2.16/0.99  --inst_prop_sim_new                     false
% 2.16/0.99  --inst_subs_new                         false
% 2.16/0.99  --inst_eq_res_simp                      false
% 2.16/0.99  --inst_subs_given                       false
% 2.16/0.99  --inst_orphan_elimination               true
% 2.16/0.99  --inst_learning_loop_flag               true
% 2.16/0.99  --inst_learning_start                   3000
% 2.16/0.99  --inst_learning_factor                  2
% 2.16/0.99  --inst_start_prop_sim_after_learn       3
% 2.16/0.99  --inst_sel_renew                        solver
% 2.16/0.99  --inst_lit_activity_flag                true
% 2.16/0.99  --inst_restr_to_given                   false
% 2.16/0.99  --inst_activity_threshold               500
% 2.16/0.99  --inst_out_proof                        true
% 2.16/0.99  
% 2.16/0.99  ------ Resolution Options
% 2.16/0.99  
% 2.16/0.99  --resolution_flag                       true
% 2.16/0.99  --res_lit_sel                           adaptive
% 2.16/0.99  --res_lit_sel_side                      none
% 2.16/0.99  --res_ordering                          kbo
% 2.16/0.99  --res_to_prop_solver                    active
% 2.16/0.99  --res_prop_simpl_new                    false
% 2.16/0.99  --res_prop_simpl_given                  true
% 2.16/0.99  --res_passive_queue_type                priority_queues
% 2.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/0.99  --res_passive_queues_freq               [15;5]
% 2.16/0.99  --res_forward_subs                      full
% 2.16/0.99  --res_backward_subs                     full
% 2.16/0.99  --res_forward_subs_resolution           true
% 2.16/0.99  --res_backward_subs_resolution          true
% 2.16/0.99  --res_orphan_elimination                true
% 2.16/0.99  --res_time_limit                        2.
% 2.16/0.99  --res_out_proof                         true
% 2.16/0.99  
% 2.16/0.99  ------ Superposition Options
% 2.16/0.99  
% 2.16/0.99  --superposition_flag                    true
% 2.16/0.99  --sup_passive_queue_type                priority_queues
% 2.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.16/0.99  --demod_completeness_check              fast
% 2.16/0.99  --demod_use_ground                      true
% 2.16/0.99  --sup_to_prop_solver                    passive
% 2.16/0.99  --sup_prop_simpl_new                    true
% 2.16/0.99  --sup_prop_simpl_given                  true
% 2.16/0.99  --sup_fun_splitting                     false
% 2.16/0.99  --sup_smt_interval                      50000
% 2.16/0.99  
% 2.16/0.99  ------ Superposition Simplification Setup
% 2.16/0.99  
% 2.16/0.99  --sup_indices_passive                   []
% 2.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_full_bw                           [BwDemod]
% 2.16/0.99  --sup_immed_triv                        [TrivRules]
% 2.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_immed_bw_main                     []
% 2.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/0.99  
% 2.16/0.99  ------ Combination Options
% 2.16/0.99  
% 2.16/0.99  --comb_res_mult                         3
% 2.16/0.99  --comb_sup_mult                         2
% 2.16/0.99  --comb_inst_mult                        10
% 2.16/0.99  
% 2.16/0.99  ------ Debug Options
% 2.16/0.99  
% 2.16/0.99  --dbg_backtrace                         false
% 2.16/0.99  --dbg_dump_prop_clauses                 false
% 2.16/0.99  --dbg_dump_prop_clauses_file            -
% 2.16/0.99  --dbg_out_stat                          false
% 2.16/0.99  ------ Parsing...
% 2.16/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.16/0.99  ------ Proving...
% 2.16/0.99  ------ Problem Properties 
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  clauses                                 21
% 2.16/0.99  conjectures                             2
% 2.16/0.99  EPR                                     2
% 2.16/0.99  Horn                                    20
% 2.16/0.99  unary                                   9
% 2.16/0.99  binary                                  9
% 2.16/0.99  lits                                    38
% 2.16/0.99  lits eq                                 22
% 2.16/0.99  fd_pure                                 0
% 2.16/0.99  fd_pseudo                               0
% 2.16/0.99  fd_cond                                 2
% 2.16/0.99  fd_pseudo_cond                          1
% 2.16/0.99  AC symbols                              0
% 2.16/0.99  
% 2.16/0.99  ------ Schedule dynamic 5 is on 
% 2.16/0.99  
% 2.16/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  ------ 
% 2.16/0.99  Current options:
% 2.16/0.99  ------ 
% 2.16/0.99  
% 2.16/0.99  ------ Input Options
% 2.16/0.99  
% 2.16/0.99  --out_options                           all
% 2.16/0.99  --tptp_safe_out                         true
% 2.16/0.99  --problem_path                          ""
% 2.16/0.99  --include_path                          ""
% 2.16/0.99  --clausifier                            res/vclausify_rel
% 2.16/0.99  --clausifier_options                    --mode clausify
% 2.16/0.99  --stdin                                 false
% 2.16/0.99  --stats_out                             all
% 2.16/0.99  
% 2.16/0.99  ------ General Options
% 2.16/0.99  
% 2.16/0.99  --fof                                   false
% 2.16/0.99  --time_out_real                         305.
% 2.16/0.99  --time_out_virtual                      -1.
% 2.16/0.99  --symbol_type_check                     false
% 2.16/0.99  --clausify_out                          false
% 2.16/0.99  --sig_cnt_out                           false
% 2.16/0.99  --trig_cnt_out                          false
% 2.16/0.99  --trig_cnt_out_tolerance                1.
% 2.16/0.99  --trig_cnt_out_sk_spl                   false
% 2.16/0.99  --abstr_cl_out                          false
% 2.16/0.99  
% 2.16/0.99  ------ Global Options
% 2.16/0.99  
% 2.16/0.99  --schedule                              default
% 2.16/0.99  --add_important_lit                     false
% 2.16/0.99  --prop_solver_per_cl                    1000
% 2.16/0.99  --min_unsat_core                        false
% 2.16/0.99  --soft_assumptions                      false
% 2.16/0.99  --soft_lemma_size                       3
% 2.16/0.99  --prop_impl_unit_size                   0
% 2.16/0.99  --prop_impl_unit                        []
% 2.16/0.99  --share_sel_clauses                     true
% 2.16/0.99  --reset_solvers                         false
% 2.16/0.99  --bc_imp_inh                            [conj_cone]
% 2.16/0.99  --conj_cone_tolerance                   3.
% 2.16/0.99  --extra_neg_conj                        none
% 2.16/0.99  --large_theory_mode                     true
% 2.16/0.99  --prolific_symb_bound                   200
% 2.16/0.99  --lt_threshold                          2000
% 2.16/0.99  --clause_weak_htbl                      true
% 2.16/0.99  --gc_record_bc_elim                     false
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing Options
% 2.16/0.99  
% 2.16/0.99  --preprocessing_flag                    true
% 2.16/0.99  --time_out_prep_mult                    0.1
% 2.16/0.99  --splitting_mode                        input
% 2.16/0.99  --splitting_grd                         true
% 2.16/0.99  --splitting_cvd                         false
% 2.16/0.99  --splitting_cvd_svl                     false
% 2.16/0.99  --splitting_nvd                         32
% 2.16/0.99  --sub_typing                            true
% 2.16/0.99  --prep_gs_sim                           true
% 2.16/0.99  --prep_unflatten                        true
% 2.16/0.99  --prep_res_sim                          true
% 2.16/0.99  --prep_upred                            true
% 2.16/0.99  --prep_sem_filter                       exhaustive
% 2.16/0.99  --prep_sem_filter_out                   false
% 2.16/0.99  --pred_elim                             true
% 2.16/0.99  --res_sim_input                         true
% 2.16/0.99  --eq_ax_congr_red                       true
% 2.16/0.99  --pure_diseq_elim                       true
% 2.16/0.99  --brand_transform                       false
% 2.16/0.99  --non_eq_to_eq                          false
% 2.16/0.99  --prep_def_merge                        true
% 2.16/0.99  --prep_def_merge_prop_impl              false
% 2.16/0.99  --prep_def_merge_mbd                    true
% 2.16/0.99  --prep_def_merge_tr_red                 false
% 2.16/0.99  --prep_def_merge_tr_cl                  false
% 2.16/0.99  --smt_preprocessing                     true
% 2.16/0.99  --smt_ac_axioms                         fast
% 2.16/0.99  --preprocessed_out                      false
% 2.16/0.99  --preprocessed_stats                    false
% 2.16/0.99  
% 2.16/0.99  ------ Abstraction refinement Options
% 2.16/0.99  
% 2.16/0.99  --abstr_ref                             []
% 2.16/0.99  --abstr_ref_prep                        false
% 2.16/0.99  --abstr_ref_until_sat                   false
% 2.16/0.99  --abstr_ref_sig_restrict                funpre
% 2.16/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.16/0.99  --abstr_ref_under                       []
% 2.16/0.99  
% 2.16/0.99  ------ SAT Options
% 2.16/0.99  
% 2.16/0.99  --sat_mode                              false
% 2.16/0.99  --sat_fm_restart_options                ""
% 2.16/0.99  --sat_gr_def                            false
% 2.16/0.99  --sat_epr_types                         true
% 2.16/0.99  --sat_non_cyclic_types                  false
% 2.16/0.99  --sat_finite_models                     false
% 2.16/0.99  --sat_fm_lemmas                         false
% 2.16/0.99  --sat_fm_prep                           false
% 2.16/0.99  --sat_fm_uc_incr                        true
% 2.16/0.99  --sat_out_model                         small
% 2.16/0.99  --sat_out_clauses                       false
% 2.16/0.99  
% 2.16/0.99  ------ QBF Options
% 2.16/0.99  
% 2.16/0.99  --qbf_mode                              false
% 2.16/0.99  --qbf_elim_univ                         false
% 2.16/0.99  --qbf_dom_inst                          none
% 2.16/0.99  --qbf_dom_pre_inst                      false
% 2.16/0.99  --qbf_sk_in                             false
% 2.16/0.99  --qbf_pred_elim                         true
% 2.16/0.99  --qbf_split                             512
% 2.16/0.99  
% 2.16/0.99  ------ BMC1 Options
% 2.16/0.99  
% 2.16/0.99  --bmc1_incremental                      false
% 2.16/0.99  --bmc1_axioms                           reachable_all
% 2.16/0.99  --bmc1_min_bound                        0
% 2.16/0.99  --bmc1_max_bound                        -1
% 2.16/0.99  --bmc1_max_bound_default                -1
% 2.16/0.99  --bmc1_symbol_reachability              true
% 2.16/0.99  --bmc1_property_lemmas                  false
% 2.16/0.99  --bmc1_k_induction                      false
% 2.16/0.99  --bmc1_non_equiv_states                 false
% 2.16/0.99  --bmc1_deadlock                         false
% 2.16/0.99  --bmc1_ucm                              false
% 2.16/0.99  --bmc1_add_unsat_core                   none
% 2.16/0.99  --bmc1_unsat_core_children              false
% 2.16/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.16/0.99  --bmc1_out_stat                         full
% 2.16/0.99  --bmc1_ground_init                      false
% 2.16/0.99  --bmc1_pre_inst_next_state              false
% 2.16/0.99  --bmc1_pre_inst_state                   false
% 2.16/0.99  --bmc1_pre_inst_reach_state             false
% 2.16/0.99  --bmc1_out_unsat_core                   false
% 2.16/0.99  --bmc1_aig_witness_out                  false
% 2.16/0.99  --bmc1_verbose                          false
% 2.16/0.99  --bmc1_dump_clauses_tptp                false
% 2.16/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.16/0.99  --bmc1_dump_file                        -
% 2.16/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.16/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.16/0.99  --bmc1_ucm_extend_mode                  1
% 2.16/0.99  --bmc1_ucm_init_mode                    2
% 2.16/0.99  --bmc1_ucm_cone_mode                    none
% 2.16/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.16/0.99  --bmc1_ucm_relax_model                  4
% 2.16/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.16/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.16/0.99  --bmc1_ucm_layered_model                none
% 2.16/0.99  --bmc1_ucm_max_lemma_size               10
% 2.16/0.99  
% 2.16/0.99  ------ AIG Options
% 2.16/0.99  
% 2.16/0.99  --aig_mode                              false
% 2.16/0.99  
% 2.16/0.99  ------ Instantiation Options
% 2.16/0.99  
% 2.16/0.99  --instantiation_flag                    true
% 2.16/0.99  --inst_sos_flag                         false
% 2.16/0.99  --inst_sos_phase                        true
% 2.16/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.16/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.16/0.99  --inst_lit_sel_side                     none
% 2.16/0.99  --inst_solver_per_active                1400
% 2.16/0.99  --inst_solver_calls_frac                1.
% 2.16/0.99  --inst_passive_queue_type               priority_queues
% 2.16/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.16/0.99  --inst_passive_queues_freq              [25;2]
% 2.16/0.99  --inst_dismatching                      true
% 2.16/0.99  --inst_eager_unprocessed_to_passive     true
% 2.16/0.99  --inst_prop_sim_given                   true
% 2.16/0.99  --inst_prop_sim_new                     false
% 2.16/0.99  --inst_subs_new                         false
% 2.16/0.99  --inst_eq_res_simp                      false
% 2.16/0.99  --inst_subs_given                       false
% 2.16/0.99  --inst_orphan_elimination               true
% 2.16/0.99  --inst_learning_loop_flag               true
% 2.16/0.99  --inst_learning_start                   3000
% 2.16/0.99  --inst_learning_factor                  2
% 2.16/0.99  --inst_start_prop_sim_after_learn       3
% 2.16/0.99  --inst_sel_renew                        solver
% 2.16/0.99  --inst_lit_activity_flag                true
% 2.16/0.99  --inst_restr_to_given                   false
% 2.16/0.99  --inst_activity_threshold               500
% 2.16/0.99  --inst_out_proof                        true
% 2.16/0.99  
% 2.16/0.99  ------ Resolution Options
% 2.16/0.99  
% 2.16/0.99  --resolution_flag                       false
% 2.16/0.99  --res_lit_sel                           adaptive
% 2.16/0.99  --res_lit_sel_side                      none
% 2.16/0.99  --res_ordering                          kbo
% 2.16/0.99  --res_to_prop_solver                    active
% 2.16/0.99  --res_prop_simpl_new                    false
% 2.16/0.99  --res_prop_simpl_given                  true
% 2.16/0.99  --res_passive_queue_type                priority_queues
% 2.16/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.16/0.99  --res_passive_queues_freq               [15;5]
% 2.16/0.99  --res_forward_subs                      full
% 2.16/0.99  --res_backward_subs                     full
% 2.16/0.99  --res_forward_subs_resolution           true
% 2.16/0.99  --res_backward_subs_resolution          true
% 2.16/0.99  --res_orphan_elimination                true
% 2.16/0.99  --res_time_limit                        2.
% 2.16/0.99  --res_out_proof                         true
% 2.16/0.99  
% 2.16/0.99  ------ Superposition Options
% 2.16/0.99  
% 2.16/0.99  --superposition_flag                    true
% 2.16/0.99  --sup_passive_queue_type                priority_queues
% 2.16/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.16/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.16/0.99  --demod_completeness_check              fast
% 2.16/0.99  --demod_use_ground                      true
% 2.16/0.99  --sup_to_prop_solver                    passive
% 2.16/0.99  --sup_prop_simpl_new                    true
% 2.16/0.99  --sup_prop_simpl_given                  true
% 2.16/0.99  --sup_fun_splitting                     false
% 2.16/0.99  --sup_smt_interval                      50000
% 2.16/0.99  
% 2.16/0.99  ------ Superposition Simplification Setup
% 2.16/0.99  
% 2.16/0.99  --sup_indices_passive                   []
% 2.16/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.16/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.16/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_full_bw                           [BwDemod]
% 2.16/0.99  --sup_immed_triv                        [TrivRules]
% 2.16/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.16/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_immed_bw_main                     []
% 2.16/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.16/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.16/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.16/0.99  
% 2.16/0.99  ------ Combination Options
% 2.16/0.99  
% 2.16/0.99  --comb_res_mult                         3
% 2.16/0.99  --comb_sup_mult                         2
% 2.16/0.99  --comb_inst_mult                        10
% 2.16/0.99  
% 2.16/0.99  ------ Debug Options
% 2.16/0.99  
% 2.16/0.99  --dbg_backtrace                         false
% 2.16/0.99  --dbg_dump_prop_clauses                 false
% 2.16/0.99  --dbg_dump_prop_clauses_file            -
% 2.16/0.99  --dbg_out_stat                          false
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  ------ Proving...
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  % SZS status Theorem for theBenchmark.p
% 2.16/0.99  
% 2.16/0.99   Resolution empty clause
% 2.16/0.99  
% 2.16/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.16/0.99  
% 2.16/0.99  fof(f15,axiom,(
% 2.16/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f20,plain,(
% 2.16/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.16/0.99    inference(pure_predicate_removal,[],[f15])).
% 2.16/0.99  
% 2.16/0.99  fof(f32,plain,(
% 2.16/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.99    inference(ennf_transformation,[],[f20])).
% 2.16/0.99  
% 2.16/0.99  fof(f59,plain,(
% 2.16/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f32])).
% 2.16/0.99  
% 2.16/0.99  fof(f10,axiom,(
% 2.16/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f25,plain,(
% 2.16/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.16/0.99    inference(ennf_transformation,[],[f10])).
% 2.16/0.99  
% 2.16/0.99  fof(f26,plain,(
% 2.16/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.16/0.99    inference(flattening,[],[f25])).
% 2.16/0.99  
% 2.16/0.99  fof(f52,plain,(
% 2.16/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f26])).
% 2.16/0.99  
% 2.16/0.99  fof(f14,axiom,(
% 2.16/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f31,plain,(
% 2.16/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.99    inference(ennf_transformation,[],[f14])).
% 2.16/0.99  
% 2.16/0.99  fof(f58,plain,(
% 2.16/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f31])).
% 2.16/0.99  
% 2.16/0.99  fof(f17,conjecture,(
% 2.16/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f18,negated_conjecture,(
% 2.16/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.16/0.99    inference(negated_conjecture,[],[f17])).
% 2.16/0.99  
% 2.16/0.99  fof(f19,plain,(
% 2.16/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.16/0.99    inference(pure_predicate_removal,[],[f18])).
% 2.16/0.99  
% 2.16/0.99  fof(f34,plain,(
% 2.16/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.16/0.99    inference(ennf_transformation,[],[f19])).
% 2.16/0.99  
% 2.16/0.99  fof(f35,plain,(
% 2.16/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.16/0.99    inference(flattening,[],[f34])).
% 2.16/0.99  
% 2.16/0.99  fof(f38,plain,(
% 2.16/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.16/0.99    introduced(choice_axiom,[])).
% 2.16/0.99  
% 2.16/0.99  fof(f39,plain,(
% 2.16/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.16/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f38])).
% 2.16/0.99  
% 2.16/0.99  fof(f62,plain,(
% 2.16/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.16/0.99    inference(cnf_transformation,[],[f39])).
% 2.16/0.99  
% 2.16/0.99  fof(f2,axiom,(
% 2.16/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f41,plain,(
% 2.16/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f2])).
% 2.16/0.99  
% 2.16/0.99  fof(f3,axiom,(
% 2.16/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f42,plain,(
% 2.16/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f3])).
% 2.16/0.99  
% 2.16/0.99  fof(f4,axiom,(
% 2.16/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f43,plain,(
% 2.16/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f4])).
% 2.16/0.99  
% 2.16/0.99  fof(f65,plain,(
% 2.16/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.16/0.99    inference(definition_unfolding,[],[f42,f43])).
% 2.16/0.99  
% 2.16/0.99  fof(f66,plain,(
% 2.16/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.16/0.99    inference(definition_unfolding,[],[f41,f65])).
% 2.16/0.99  
% 2.16/0.99  fof(f74,plain,(
% 2.16/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.16/0.99    inference(definition_unfolding,[],[f62,f66])).
% 2.16/0.99  
% 2.16/0.99  fof(f9,axiom,(
% 2.16/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f24,plain,(
% 2.16/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.16/0.99    inference(ennf_transformation,[],[f9])).
% 2.16/0.99  
% 2.16/0.99  fof(f51,plain,(
% 2.16/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f24])).
% 2.16/0.99  
% 2.16/0.99  fof(f12,axiom,(
% 2.16/0.99    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f27,plain,(
% 2.16/0.99    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.16/0.99    inference(ennf_transformation,[],[f12])).
% 2.16/0.99  
% 2.16/0.99  fof(f28,plain,(
% 2.16/0.99    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.16/0.99    inference(flattening,[],[f27])).
% 2.16/0.99  
% 2.16/0.99  fof(f56,plain,(
% 2.16/0.99    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f28])).
% 2.16/0.99  
% 2.16/0.99  fof(f16,axiom,(
% 2.16/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f33,plain,(
% 2.16/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.99    inference(ennf_transformation,[],[f16])).
% 2.16/0.99  
% 2.16/0.99  fof(f60,plain,(
% 2.16/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f33])).
% 2.16/0.99  
% 2.16/0.99  fof(f64,plain,(
% 2.16/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.16/0.99    inference(cnf_transformation,[],[f39])).
% 2.16/0.99  
% 2.16/0.99  fof(f73,plain,(
% 2.16/0.99    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.16/0.99    inference(definition_unfolding,[],[f64,f66,f66])).
% 2.16/0.99  
% 2.16/0.99  fof(f13,axiom,(
% 2.16/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))))),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f29,plain,(
% 2.16/0.99    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.16/0.99    inference(ennf_transformation,[],[f13])).
% 2.16/0.99  
% 2.16/0.99  fof(f30,plain,(
% 2.16/0.99    ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.16/0.99    inference(flattening,[],[f29])).
% 2.16/0.99  
% 2.16/0.99  fof(f57,plain,(
% 2.16/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k1_tarski(X0))),k1_tarski(k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f30])).
% 2.16/0.99  
% 2.16/0.99  fof(f72,plain,(
% 2.16/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X1,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.16/0.99    inference(definition_unfolding,[],[f57,f66,f66])).
% 2.16/0.99  
% 2.16/0.99  fof(f61,plain,(
% 2.16/0.99    v1_funct_1(sK3)),
% 2.16/0.99    inference(cnf_transformation,[],[f39])).
% 2.16/0.99  
% 2.16/0.99  fof(f5,axiom,(
% 2.16/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f22,plain,(
% 2.16/0.99    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.16/0.99    inference(ennf_transformation,[],[f5])).
% 2.16/0.99  
% 2.16/0.99  fof(f36,plain,(
% 2.16/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.16/0.99    inference(nnf_transformation,[],[f22])).
% 2.16/0.99  
% 2.16/0.99  fof(f37,plain,(
% 2.16/0.99    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.16/0.99    inference(flattening,[],[f36])).
% 2.16/0.99  
% 2.16/0.99  fof(f44,plain,(
% 2.16/0.99    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f37])).
% 2.16/0.99  
% 2.16/0.99  fof(f71,plain,(
% 2.16/0.99    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 2.16/0.99    inference(definition_unfolding,[],[f44,f65,f66,f66,f65])).
% 2.16/0.99  
% 2.16/0.99  fof(f8,axiom,(
% 2.16/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f23,plain,(
% 2.16/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.16/0.99    inference(ennf_transformation,[],[f8])).
% 2.16/0.99  
% 2.16/0.99  fof(f50,plain,(
% 2.16/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f23])).
% 2.16/0.99  
% 2.16/0.99  fof(f6,axiom,(
% 2.16/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f49,plain,(
% 2.16/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.16/0.99    inference(cnf_transformation,[],[f6])).
% 2.16/0.99  
% 2.16/0.99  fof(f11,axiom,(
% 2.16/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f54,plain,(
% 2.16/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.16/0.99    inference(cnf_transformation,[],[f11])).
% 2.16/0.99  
% 2.16/0.99  fof(f1,axiom,(
% 2.16/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.16/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.16/0.99  
% 2.16/0.99  fof(f40,plain,(
% 2.16/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.16/0.99    inference(cnf_transformation,[],[f1])).
% 2.16/0.99  
% 2.16/0.99  cnf(c_16,plain,
% 2.16/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.16/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_9,plain,
% 2.16/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.16/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_236,plain,
% 2.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/0.99      | ~ v1_relat_1(X0)
% 2.16/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.16/0.99      inference(resolution,[status(thm)],[c_16,c_9]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_15,plain,
% 2.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_240,plain,
% 2.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_236,c_16,c_15,c_9]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_20,negated_conjecture,
% 2.16/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.16/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_286,plain,
% 2.16/0.99      ( k7_relat_1(X0,X1) = X0
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.16/0.99      | sK3 != X0 ),
% 2.16/0.99      inference(resolution_lifted,[status(thm)],[c_240,c_20]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_287,plain,
% 2.16/0.99      ( k7_relat_1(sK3,X0) = sK3
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.16/0.99      inference(unflattening,[status(thm)],[c_286]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1000,plain,
% 2.16/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 2.16/0.99      | k7_relat_1(sK3,X0_47) = sK3 ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_287]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1421,plain,
% 2.16/0.99      ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = sK3 ),
% 2.16/0.99      inference(equality_resolution,[status(thm)],[c_1000]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_304,plain,
% 2.16/0.99      ( v1_relat_1(X0)
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.16/0.99      | sK3 != X0 ),
% 2.16/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_20]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_305,plain,
% 2.16/0.99      ( v1_relat_1(sK3)
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.16/0.99      inference(unflattening,[status(thm)],[c_304]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_998,plain,
% 2.16/0.99      ( v1_relat_1(sK3)
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_305]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1314,plain,
% 2.16/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 2.16/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_998]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1021,plain,( X0_48 = X0_48 ),theory(equality) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1422,plain,
% 2.16/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1021]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1425,plain,
% 2.16/0.99      ( v1_relat_1(sK3)
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_998]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1426,plain,
% 2.16/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.16/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1425]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1479,plain,
% 2.16/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_1314,c_1422,c_1426]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_8,plain,
% 2.16/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.16/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1011,plain,
% 2.16/0.99      ( ~ v1_relat_1(X0_47)
% 2.16/0.99      | k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47) ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1308,plain,
% 2.16/0.99      ( k2_relat_1(k7_relat_1(X0_47,X1_47)) = k9_relat_1(X0_47,X1_47)
% 2.16/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1011]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1994,plain,
% 2.16/0.99      ( k2_relat_1(k7_relat_1(sK3,X0_47)) = k9_relat_1(sK3,X0_47) ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_1479,c_1308]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2157,plain,
% 2.16/0.99      ( k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK3) ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_1421,c_1994]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_12,plain,
% 2.16/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.16/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1008,plain,
% 2.16/0.99      ( ~ v1_relat_1(X0_47)
% 2.16/0.99      | k2_relat_1(X0_47) != k1_xboole_0
% 2.16/0.99      | k1_xboole_0 = X0_47 ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_12]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1309,plain,
% 2.16/0.99      ( k2_relat_1(X0_47) != k1_xboole_0
% 2.16/0.99      | k1_xboole_0 = X0_47
% 2.16/0.99      | v1_relat_1(X0_47) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2158,plain,
% 2.16/0.99      ( k7_relat_1(sK3,X0_47) = k1_xboole_0
% 2.16/0.99      | k9_relat_1(sK3,X0_47) != k1_xboole_0
% 2.16/0.99      | v1_relat_1(k7_relat_1(sK3,X0_47)) != iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_1994,c_1309]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2313,plain,
% 2.16/0.99      ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
% 2.16/0.99      | k2_relat_1(sK3) != k1_xboole_0
% 2.16/0.99      | v1_relat_1(k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0))) != iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_2157,c_2158]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2314,plain,
% 2.16/0.99      ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k1_xboole_0
% 2.16/0.99      | k2_relat_1(sK3) != k1_xboole_0
% 2.16/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.16/0.99      inference(light_normalisation,[status(thm)],[c_2313,c_1421]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2315,plain,
% 2.16/0.99      ( k2_relat_1(sK3) != k1_xboole_0
% 2.16/0.99      | sK3 = k1_xboole_0
% 2.16/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.16/0.99      inference(demodulation,[status(thm)],[c_2314,c_1421]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_17,plain,
% 2.16/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.16/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.16/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_295,plain,
% 2.16/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.16/0.99      | sK3 != X2 ),
% 2.16/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_20]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_296,plain,
% 2.16/0.99      ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.16/0.99      inference(unflattening,[status(thm)],[c_295]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_999,plain,
% 2.16/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 2.16/0.99      | k7_relset_1(X0_47,X1_47,sK3,X2_47) = k9_relat_1(sK3,X2_47) ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_296]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1450,plain,
% 2.16/0.99      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0_47) = k9_relat_1(sK3,X0_47) ),
% 2.16/0.99      inference(equality_resolution,[status(thm)],[c_999]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_18,negated_conjecture,
% 2.16/0.99      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.16/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1006,negated_conjecture,
% 2.16/0.99      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_18]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1311,plain,
% 2.16/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1006]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1466,plain,
% 2.16/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.16/0.99      inference(demodulation,[status(thm)],[c_1450,c_1311]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1467,plain,
% 2.16/0.99      ( ~ r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.16/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1466]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1020,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1780,plain,
% 2.16/0.99      ( sK3 = sK3 ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1020]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1809,plain,
% 2.16/0.99      ( k9_relat_1(sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1020]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_14,plain,
% 2.16/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
% 2.16/0.99      | ~ v1_funct_1(X0)
% 2.16/0.99      | ~ v1_relat_1(X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_21,negated_conjecture,
% 2.16/0.99      ( v1_funct_1(sK3) ),
% 2.16/0.99      inference(cnf_transformation,[],[f61]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_221,plain,
% 2.16/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(X0,k2_enumset1(X1,X1,X1,X1))),k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)))
% 2.16/0.99      | ~ v1_relat_1(X0)
% 2.16/0.99      | sK3 != X0 ),
% 2.16/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_222,plain,
% 2.16/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0,X0,X0,X0))),k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)))
% 2.16/0.99      | ~ v1_relat_1(sK3) ),
% 2.16/0.99      inference(unflattening,[status(thm)],[c_221]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1004,plain,
% 2.16/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50)))
% 2.16/0.99      | ~ v1_relat_1(sK3) ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_222]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1312,plain,
% 2.16/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top
% 2.16/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1004]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1070,plain,
% 2.16/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top
% 2.16/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1004]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1607,plain,
% 2.16/0.99      ( r1_tarski(k2_relat_1(k7_relat_1(sK3,k2_enumset1(X0_50,X0_50,X0_50,X0_50))),k2_enumset1(k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50),k1_funct_1(sK3,X0_50))) = iProver_top ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_1312,c_1070,c_1422,c_1426]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1614,plain,
% 2.16/0.99      ( r1_tarski(k2_relat_1(sK3),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_1421,c_1607]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_5,plain,
% 2.16/0.99      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 2.16/0.99      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.16/0.99      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.16/0.99      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.16/0.99      | k1_xboole_0 = X0 ),
% 2.16/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1013,plain,
% 2.16/0.99      ( ~ r1_tarski(X0_47,k2_enumset1(X0_50,X0_50,X0_50,X1_50))
% 2.16/0.99      | k2_enumset1(X1_50,X1_50,X1_50,X1_50) = X0_47
% 2.16/0.99      | k2_enumset1(X0_50,X0_50,X0_50,X1_50) = X0_47
% 2.16/0.99      | k2_enumset1(X0_50,X0_50,X0_50,X0_50) = X0_47
% 2.16/0.99      | k1_xboole_0 = X0_47 ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1306,plain,
% 2.16/0.99      ( k2_enumset1(X0_50,X0_50,X0_50,X0_50) = X0_47
% 2.16/0.99      | k2_enumset1(X1_50,X1_50,X1_50,X0_50) = X0_47
% 2.16/0.99      | k2_enumset1(X1_50,X1_50,X1_50,X1_50) = X0_47
% 2.16/0.99      | k1_xboole_0 = X0_47
% 2.16/0.99      | r1_tarski(X0_47,k2_enumset1(X1_50,X1_50,X1_50,X0_50)) != iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1013]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1917,plain,
% 2.16/0.99      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.16/0.99      | k2_relat_1(sK3) = k1_xboole_0 ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_1614,c_1306]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_7,plain,
% 2.16/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1012,plain,
% 2.16/0.99      ( r1_tarski(k9_relat_1(X0_47,X1_47),k2_relat_1(X0_47))
% 2.16/0.99      | ~ v1_relat_1(X0_47) ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1945,plain,
% 2.16/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1012]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2029,plain,
% 2.16/0.99      ( ~ v1_relat_1(sK3)
% 2.16/0.99      | k2_relat_1(sK3) != k1_xboole_0
% 2.16/0.99      | k1_xboole_0 = sK3 ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1008]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1024,plain,
% 2.16/0.99      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 2.16/0.99      theory(equality) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1782,plain,
% 2.16/0.99      ( X0_47 != X1_47 | sK3 != X1_47 | sK3 = X0_47 ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1024]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2112,plain,
% 2.16/0.99      ( X0_47 != sK3 | sK3 = X0_47 | sK3 != sK3 ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1782]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2113,plain,
% 2.16/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_2112]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1026,plain,
% 2.16/0.99      ( ~ r1_tarski(X0_47,X1_47)
% 2.16/0.99      | r1_tarski(X2_47,X3_47)
% 2.16/0.99      | X2_47 != X0_47
% 2.16/0.99      | X3_47 != X1_47 ),
% 2.16/0.99      theory(equality) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1616,plain,
% 2.16/0.99      ( ~ r1_tarski(X0_47,X1_47)
% 2.16/0.99      | r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.16/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1_47
% 2.16/0.99      | k9_relat_1(sK3,sK2) != X0_47 ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1026]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1808,plain,
% 2.16/0.99      ( ~ r1_tarski(k9_relat_1(sK3,sK2),X0_47)
% 2.16/0.99      | r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.16/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0_47
% 2.16/0.99      | k9_relat_1(sK3,sK2) != k9_relat_1(sK3,sK2) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1616]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2210,plain,
% 2.16/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.16/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.16/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3)
% 2.16/0.99      | k9_relat_1(sK3,sK2) != k9_relat_1(sK3,sK2) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1808]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2424,plain,
% 2.16/0.99      ( sK3 = k1_xboole_0 ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_2315,c_1422,c_1425,c_1467,c_1780,c_1809,c_1917,c_1945,
% 2.16/0.99                 c_2029,c_2113,c_2210]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2434,plain,
% 2.16/0.99      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.16/0.99      inference(demodulation,[status(thm)],[c_2424,c_1466]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_6,plain,
% 2.16/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.16/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_274,plain,
% 2.16/0.99      ( v1_relat_1(X0)
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
% 2.16/0.99      | k1_xboole_0 != X0 ),
% 2.16/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_275,plain,
% 2.16/0.99      ( v1_relat_1(k1_xboole_0)
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
% 2.16/0.99      inference(unflattening,[status(thm)],[c_274]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1001,plain,
% 2.16/0.99      ( v1_relat_1(k1_xboole_0)
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49) ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_275]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1313,plain,
% 2.16/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
% 2.16/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1001]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1429,plain,
% 2.16/0.99      ( v1_relat_1(k1_xboole_0)
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1001]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1431,plain,
% 2.16/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 2.16/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1429]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1430,plain,
% 2.16/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) = k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1021]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1828,plain,
% 2.16/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_1313,c_1431,c_1430]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1993,plain,
% 2.16/0.99      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0_47)) = k9_relat_1(k1_xboole_0,X0_47) ),
% 2.16/0.99      inference(superposition,[status(thm)],[c_1828,c_1308]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_10,plain,
% 2.16/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.16/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1010,plain,
% 2.16/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_10]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_256,plain,
% 2.16/0.99      ( k7_relat_1(X0,X1) = X0
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
% 2.16/0.99      | k1_xboole_0 != X0 ),
% 2.16/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_240]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_257,plain,
% 2.16/0.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 2.16/0.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
% 2.16/0.99      inference(unflattening,[status(thm)],[c_256]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1003,plain,
% 2.16/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(X0_49)
% 2.16/0.99      | k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_257]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1542,plain,
% 2.16/0.99      ( k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)) != k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))
% 2.16/0.99      | k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
% 2.16/0.99      inference(instantiation,[status(thm)],[c_1003]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1833,plain,
% 2.16/0.99      ( k7_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
% 2.16/0.99      inference(global_propositional_subsumption,
% 2.16/0.99                [status(thm)],
% 2.16/0.99                [c_1003,c_1430,c_1542]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1998,plain,
% 2.16/0.99      ( k9_relat_1(k1_xboole_0,X0_47) = k1_xboole_0 ),
% 2.16/0.99      inference(light_normalisation,[status(thm)],[c_1993,c_1010,c_1833]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2448,plain,
% 2.16/0.99      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.16/0.99      inference(demodulation,[status(thm)],[c_2434,c_1998]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_0,plain,
% 2.16/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.16/0.99      inference(cnf_transformation,[],[f40]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1018,plain,
% 2.16/0.99      ( r1_tarski(k1_xboole_0,X0_47) ),
% 2.16/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_1301,plain,
% 2.16/0.99      ( r1_tarski(k1_xboole_0,X0_47) = iProver_top ),
% 2.16/0.99      inference(predicate_to_equality,[status(thm)],[c_1018]) ).
% 2.16/0.99  
% 2.16/0.99  cnf(c_2545,plain,
% 2.16/0.99      ( $false ),
% 2.16/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2448,c_1301]) ).
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.16/0.99  
% 2.16/0.99  ------                               Statistics
% 2.16/0.99  
% 2.16/0.99  ------ General
% 2.16/0.99  
% 2.16/0.99  abstr_ref_over_cycles:                  0
% 2.16/0.99  abstr_ref_under_cycles:                 0
% 2.16/0.99  gc_basic_clause_elim:                   0
% 2.16/0.99  forced_gc_time:                         0
% 2.16/0.99  parsing_time:                           0.01
% 2.16/0.99  unif_index_cands_time:                  0.
% 2.16/0.99  unif_index_add_time:                    0.
% 2.16/0.99  orderings_time:                         0.
% 2.16/0.99  out_proof_time:                         0.011
% 2.16/0.99  total_time:                             0.114
% 2.16/0.99  num_of_symbols:                         54
% 2.16/0.99  num_of_terms:                           2289
% 2.16/0.99  
% 2.16/0.99  ------ Preprocessing
% 2.16/0.99  
% 2.16/0.99  num_of_splits:                          0
% 2.16/0.99  num_of_split_atoms:                     0
% 2.16/0.99  num_of_reused_defs:                     0
% 2.16/0.99  num_eq_ax_congr_red:                    8
% 2.16/0.99  num_of_sem_filtered_clauses:            1
% 2.16/0.99  num_of_subtypes:                        4
% 2.16/0.99  monotx_restored_types:                  0
% 2.16/0.99  sat_num_of_epr_types:                   0
% 2.16/0.99  sat_num_of_non_cyclic_types:            0
% 2.16/0.99  sat_guarded_non_collapsed_types:        1
% 2.16/0.99  num_pure_diseq_elim:                    0
% 2.16/0.99  simp_replaced_by:                       0
% 2.16/0.99  res_preprocessed:                       120
% 2.16/0.99  prep_upred:                             0
% 2.16/0.99  prep_unflattend:                        41
% 2.16/0.99  smt_new_axioms:                         0
% 2.16/0.99  pred_elim_cands:                        2
% 2.16/0.99  pred_elim:                              3
% 2.16/0.99  pred_elim_cl:                           1
% 2.16/0.99  pred_elim_cycles:                       7
% 2.16/0.99  merged_defs:                            0
% 2.16/0.99  merged_defs_ncl:                        0
% 2.16/0.99  bin_hyper_res:                          0
% 2.16/0.99  prep_cycles:                            4
% 2.16/0.99  pred_elim_time:                         0.013
% 2.16/0.99  splitting_time:                         0.
% 2.16/0.99  sem_filter_time:                        0.
% 2.16/0.99  monotx_time:                            0.
% 2.16/0.99  subtype_inf_time:                       0.
% 2.16/0.99  
% 2.16/0.99  ------ Problem properties
% 2.16/0.99  
% 2.16/0.99  clauses:                                21
% 2.16/0.99  conjectures:                            2
% 2.16/0.99  epr:                                    2
% 2.16/0.99  horn:                                   20
% 2.16/0.99  ground:                                 4
% 2.16/0.99  unary:                                  9
% 2.16/0.99  binary:                                 9
% 2.16/0.99  lits:                                   38
% 2.16/0.99  lits_eq:                                22
% 2.16/0.99  fd_pure:                                0
% 2.16/0.99  fd_pseudo:                              0
% 2.16/0.99  fd_cond:                                2
% 2.16/0.99  fd_pseudo_cond:                         1
% 2.16/0.99  ac_symbols:                             0
% 2.16/0.99  
% 2.16/0.99  ------ Propositional Solver
% 2.16/0.99  
% 2.16/0.99  prop_solver_calls:                      28
% 2.16/0.99  prop_fast_solver_calls:                 681
% 2.16/0.99  smt_solver_calls:                       0
% 2.16/0.99  smt_fast_solver_calls:                  0
% 2.16/0.99  prop_num_of_clauses:                    674
% 2.16/0.99  prop_preprocess_simplified:             3417
% 2.16/0.99  prop_fo_subsumed:                       9
% 2.16/0.99  prop_solver_time:                       0.
% 2.16/0.99  smt_solver_time:                        0.
% 2.16/0.99  smt_fast_solver_time:                   0.
% 2.16/0.99  prop_fast_solver_time:                  0.
% 2.16/0.99  prop_unsat_core_time:                   0.
% 2.16/0.99  
% 2.16/0.99  ------ QBF
% 2.16/0.99  
% 2.16/0.99  qbf_q_res:                              0
% 2.16/0.99  qbf_num_tautologies:                    0
% 2.16/0.99  qbf_prep_cycles:                        0
% 2.16/0.99  
% 2.16/0.99  ------ BMC1
% 2.16/0.99  
% 2.16/0.99  bmc1_current_bound:                     -1
% 2.16/0.99  bmc1_last_solved_bound:                 -1
% 2.16/0.99  bmc1_unsat_core_size:                   -1
% 2.16/0.99  bmc1_unsat_core_parents_size:           -1
% 2.16/0.99  bmc1_merge_next_fun:                    0
% 2.16/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.16/0.99  
% 2.16/0.99  ------ Instantiation
% 2.16/0.99  
% 2.16/0.99  inst_num_of_clauses:                    229
% 2.16/0.99  inst_num_in_passive:                    37
% 2.16/0.99  inst_num_in_active:                     171
% 2.16/0.99  inst_num_in_unprocessed:                21
% 2.16/0.99  inst_num_of_loops:                      180
% 2.16/0.99  inst_num_of_learning_restarts:          0
% 2.16/0.99  inst_num_moves_active_passive:          4
% 2.16/0.99  inst_lit_activity:                      0
% 2.16/0.99  inst_lit_activity_moves:                0
% 2.16/0.99  inst_num_tautologies:                   0
% 2.16/0.99  inst_num_prop_implied:                  0
% 2.16/0.99  inst_num_existing_simplified:           0
% 2.16/0.99  inst_num_eq_res_simplified:             0
% 2.16/0.99  inst_num_child_elim:                    0
% 2.16/0.99  inst_num_of_dismatching_blockings:      42
% 2.16/0.99  inst_num_of_non_proper_insts:           222
% 2.16/0.99  inst_num_of_duplicates:                 0
% 2.16/0.99  inst_inst_num_from_inst_to_res:         0
% 2.16/0.99  inst_dismatching_checking_time:         0.
% 2.16/0.99  
% 2.16/0.99  ------ Resolution
% 2.16/0.99  
% 2.16/0.99  res_num_of_clauses:                     0
% 2.16/0.99  res_num_in_passive:                     0
% 2.16/0.99  res_num_in_active:                      0
% 2.16/0.99  res_num_of_loops:                       124
% 2.16/0.99  res_forward_subset_subsumed:            58
% 2.16/0.99  res_backward_subset_subsumed:           0
% 2.16/0.99  res_forward_subsumed:                   0
% 2.16/0.99  res_backward_subsumed:                  0
% 2.16/0.99  res_forward_subsumption_resolution:     0
% 2.16/0.99  res_backward_subsumption_resolution:    0
% 2.16/0.99  res_clause_to_clause_subsumption:       71
% 2.16/0.99  res_orphan_elimination:                 0
% 2.16/0.99  res_tautology_del:                      47
% 2.16/0.99  res_num_eq_res_simplified:              0
% 2.16/0.99  res_num_sel_changes:                    0
% 2.16/0.99  res_moves_from_active_to_pass:          0
% 2.16/0.99  
% 2.16/0.99  ------ Superposition
% 2.16/0.99  
% 2.16/0.99  sup_time_total:                         0.
% 2.16/0.99  sup_time_generating:                    0.
% 2.16/0.99  sup_time_sim_full:                      0.
% 2.16/0.99  sup_time_sim_immed:                     0.
% 2.16/0.99  
% 2.16/0.99  sup_num_of_clauses:                     24
% 2.16/0.99  sup_num_in_active:                      17
% 2.16/0.99  sup_num_in_passive:                     7
% 2.16/0.99  sup_num_of_loops:                       35
% 2.16/0.99  sup_fw_superposition:                   17
% 2.16/0.99  sup_bw_superposition:                   5
% 2.16/0.99  sup_immediate_simplified:               18
% 2.16/0.99  sup_given_eliminated:                   0
% 2.16/0.99  comparisons_done:                       0
% 2.16/0.99  comparisons_avoided:                    0
% 2.16/0.99  
% 2.16/0.99  ------ Simplifications
% 2.16/0.99  
% 2.16/0.99  
% 2.16/0.99  sim_fw_subset_subsumed:                 3
% 2.16/0.99  sim_bw_subset_subsumed:                 0
% 2.16/0.99  sim_fw_subsumed:                        10
% 2.16/0.99  sim_bw_subsumed:                        0
% 2.16/0.99  sim_fw_subsumption_res:                 1
% 2.16/0.99  sim_bw_subsumption_res:                 0
% 2.16/0.99  sim_tautology_del:                      0
% 2.16/0.99  sim_eq_tautology_del:                   5
% 2.16/0.99  sim_eq_res_simp:                        0
% 2.16/0.99  sim_fw_demodulated:                     5
% 2.16/0.99  sim_bw_demodulated:                     18
% 2.16/0.99  sim_light_normalised:                   10
% 2.16/1.00  sim_joinable_taut:                      0
% 2.16/1.00  sim_joinable_simp:                      0
% 2.16/1.00  sim_ac_normalised:                      0
% 2.16/1.00  sim_smt_subsumption:                    0
% 2.16/1.00  
%------------------------------------------------------------------------------
