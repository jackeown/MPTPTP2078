%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:37 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  136 ( 609 expanded)
%              Number of clauses        :   73 ( 160 expanded)
%              Number of leaves         :   20 ( 144 expanded)
%              Depth                    :   21
%              Number of atoms          :  310 (1380 expanded)
%              Number of equality atoms :  170 ( 580 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f22,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f44,plain,
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

fof(f45,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f44])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f75,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f74])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f71,f75])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f75,f75])).

fof(f73,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f73,f75,f75])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f66,f75,f75])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_19,c_10])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_255,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_251,c_19,c_18,c_10])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_320,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_255,c_23])).

cnf(c_321,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_320])).

cnf(c_1228,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_321])).

cnf(c_15,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1100,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1724,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_1100])).

cnf(c_807,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1229,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_338,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_23])).

cnf(c_339,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_1232,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_1233,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1232])).

cnf(c_1758,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1724,c_1229,c_1233])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1105,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2656,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1758,c_1105])).

cnf(c_2838,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(superposition,[status(thm)],[c_2656,c_321])).

cnf(c_21,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_329,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_23])).

cnf(c_330,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_1230,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_330])).

cnf(c_1351,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1230])).

cnf(c_809,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1283,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_809])).

cnf(c_1352,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1283])).

cnf(c_1423,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1352])).

cnf(c_8,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1424,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_271,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_24])).

cnf(c_272,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_271])).

cnf(c_1097,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_273,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_1566,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1097,c_273,c_1229,c_1233])).

cnf(c_1567,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1566])).

cnf(c_2831,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2656,c_1567])).

cnf(c_2992,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2838,c_21,c_1229,c_1232,c_1351,c_1423,c_1424,c_2831])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1101,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3010,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2992,c_1101])).

cnf(c_3076,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3010,c_1229,c_1233])).

cnf(c_1256,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(equality_resolution,[status(thm)],[c_330])).

cnf(c_1098,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1281,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1256,c_1098])).

cnf(c_3086,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3076,c_1281])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_308,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_309,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_1096,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2)
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_1242,plain,
    ( v1_relat_1(k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_309])).

cnf(c_1244,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1242])).

cnf(c_1243,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_807])).

cnf(c_1648,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1096,c_1244,c_1243])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1103,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1766,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1648,c_1103])).

cnf(c_11,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_290,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_255])).

cnf(c_291,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_1359,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_291])).

cnf(c_1771,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1766,c_11,c_1359])).

cnf(c_3100,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3086,c_1771])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1108,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3305,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3100,c_1108])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:15:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.18/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.18/1.01  
% 2.18/1.01  ------  iProver source info
% 2.18/1.01  
% 2.18/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.18/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.18/1.01  git: non_committed_changes: false
% 2.18/1.01  git: last_make_outside_of_git: false
% 2.18/1.01  
% 2.18/1.01  ------ 
% 2.18/1.01  
% 2.18/1.01  ------ Input Options
% 2.18/1.01  
% 2.18/1.01  --out_options                           all
% 2.18/1.01  --tptp_safe_out                         true
% 2.18/1.01  --problem_path                          ""
% 2.18/1.01  --include_path                          ""
% 2.18/1.01  --clausifier                            res/vclausify_rel
% 2.18/1.01  --clausifier_options                    --mode clausify
% 2.18/1.01  --stdin                                 false
% 2.18/1.01  --stats_out                             all
% 2.18/1.01  
% 2.18/1.01  ------ General Options
% 2.18/1.01  
% 2.18/1.01  --fof                                   false
% 2.18/1.01  --time_out_real                         305.
% 2.18/1.01  --time_out_virtual                      -1.
% 2.18/1.01  --symbol_type_check                     false
% 2.18/1.01  --clausify_out                          false
% 2.18/1.01  --sig_cnt_out                           false
% 2.18/1.01  --trig_cnt_out                          false
% 2.18/1.01  --trig_cnt_out_tolerance                1.
% 2.18/1.01  --trig_cnt_out_sk_spl                   false
% 2.18/1.01  --abstr_cl_out                          false
% 2.18/1.01  
% 2.18/1.01  ------ Global Options
% 2.18/1.01  
% 2.18/1.01  --schedule                              default
% 2.18/1.01  --add_important_lit                     false
% 2.18/1.01  --prop_solver_per_cl                    1000
% 2.18/1.01  --min_unsat_core                        false
% 2.18/1.01  --soft_assumptions                      false
% 2.18/1.01  --soft_lemma_size                       3
% 2.18/1.01  --prop_impl_unit_size                   0
% 2.18/1.01  --prop_impl_unit                        []
% 2.18/1.01  --share_sel_clauses                     true
% 2.18/1.01  --reset_solvers                         false
% 2.18/1.01  --bc_imp_inh                            [conj_cone]
% 2.18/1.01  --conj_cone_tolerance                   3.
% 2.18/1.01  --extra_neg_conj                        none
% 2.18/1.01  --large_theory_mode                     true
% 2.18/1.01  --prolific_symb_bound                   200
% 2.18/1.01  --lt_threshold                          2000
% 2.18/1.01  --clause_weak_htbl                      true
% 2.18/1.01  --gc_record_bc_elim                     false
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing Options
% 2.18/1.01  
% 2.18/1.01  --preprocessing_flag                    true
% 2.18/1.01  --time_out_prep_mult                    0.1
% 2.18/1.01  --splitting_mode                        input
% 2.18/1.01  --splitting_grd                         true
% 2.18/1.01  --splitting_cvd                         false
% 2.18/1.01  --splitting_cvd_svl                     false
% 2.18/1.01  --splitting_nvd                         32
% 2.18/1.01  --sub_typing                            true
% 2.18/1.01  --prep_gs_sim                           true
% 2.18/1.01  --prep_unflatten                        true
% 2.18/1.01  --prep_res_sim                          true
% 2.18/1.01  --prep_upred                            true
% 2.18/1.01  --prep_sem_filter                       exhaustive
% 2.18/1.01  --prep_sem_filter_out                   false
% 2.18/1.01  --pred_elim                             true
% 2.18/1.01  --res_sim_input                         true
% 2.18/1.01  --eq_ax_congr_red                       true
% 2.18/1.01  --pure_diseq_elim                       true
% 2.18/1.01  --brand_transform                       false
% 2.18/1.01  --non_eq_to_eq                          false
% 2.18/1.01  --prep_def_merge                        true
% 2.18/1.01  --prep_def_merge_prop_impl              false
% 2.18/1.01  --prep_def_merge_mbd                    true
% 2.18/1.01  --prep_def_merge_tr_red                 false
% 2.18/1.01  --prep_def_merge_tr_cl                  false
% 2.18/1.01  --smt_preprocessing                     true
% 2.18/1.01  --smt_ac_axioms                         fast
% 2.18/1.01  --preprocessed_out                      false
% 2.18/1.01  --preprocessed_stats                    false
% 2.18/1.01  
% 2.18/1.01  ------ Abstraction refinement Options
% 2.18/1.01  
% 2.18/1.01  --abstr_ref                             []
% 2.18/1.01  --abstr_ref_prep                        false
% 2.18/1.01  --abstr_ref_until_sat                   false
% 2.18/1.01  --abstr_ref_sig_restrict                funpre
% 2.18/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.01  --abstr_ref_under                       []
% 2.18/1.01  
% 2.18/1.01  ------ SAT Options
% 2.18/1.01  
% 2.18/1.01  --sat_mode                              false
% 2.18/1.01  --sat_fm_restart_options                ""
% 2.18/1.01  --sat_gr_def                            false
% 2.18/1.01  --sat_epr_types                         true
% 2.18/1.01  --sat_non_cyclic_types                  false
% 2.18/1.01  --sat_finite_models                     false
% 2.18/1.01  --sat_fm_lemmas                         false
% 2.18/1.01  --sat_fm_prep                           false
% 2.18/1.01  --sat_fm_uc_incr                        true
% 2.18/1.01  --sat_out_model                         small
% 2.18/1.01  --sat_out_clauses                       false
% 2.18/1.01  
% 2.18/1.01  ------ QBF Options
% 2.18/1.01  
% 2.18/1.01  --qbf_mode                              false
% 2.18/1.01  --qbf_elim_univ                         false
% 2.18/1.01  --qbf_dom_inst                          none
% 2.18/1.01  --qbf_dom_pre_inst                      false
% 2.18/1.01  --qbf_sk_in                             false
% 2.18/1.01  --qbf_pred_elim                         true
% 2.18/1.01  --qbf_split                             512
% 2.18/1.01  
% 2.18/1.01  ------ BMC1 Options
% 2.18/1.01  
% 2.18/1.01  --bmc1_incremental                      false
% 2.18/1.01  --bmc1_axioms                           reachable_all
% 2.18/1.01  --bmc1_min_bound                        0
% 2.18/1.01  --bmc1_max_bound                        -1
% 2.18/1.01  --bmc1_max_bound_default                -1
% 2.18/1.01  --bmc1_symbol_reachability              true
% 2.18/1.01  --bmc1_property_lemmas                  false
% 2.18/1.01  --bmc1_k_induction                      false
% 2.18/1.01  --bmc1_non_equiv_states                 false
% 2.18/1.01  --bmc1_deadlock                         false
% 2.18/1.01  --bmc1_ucm                              false
% 2.18/1.01  --bmc1_add_unsat_core                   none
% 2.18/1.01  --bmc1_unsat_core_children              false
% 2.18/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.01  --bmc1_out_stat                         full
% 2.18/1.01  --bmc1_ground_init                      false
% 2.18/1.01  --bmc1_pre_inst_next_state              false
% 2.18/1.01  --bmc1_pre_inst_state                   false
% 2.18/1.01  --bmc1_pre_inst_reach_state             false
% 2.18/1.01  --bmc1_out_unsat_core                   false
% 2.18/1.01  --bmc1_aig_witness_out                  false
% 2.18/1.01  --bmc1_verbose                          false
% 2.18/1.01  --bmc1_dump_clauses_tptp                false
% 2.18/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.01  --bmc1_dump_file                        -
% 2.18/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.01  --bmc1_ucm_extend_mode                  1
% 2.18/1.01  --bmc1_ucm_init_mode                    2
% 2.18/1.01  --bmc1_ucm_cone_mode                    none
% 2.18/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.01  --bmc1_ucm_relax_model                  4
% 2.18/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.01  --bmc1_ucm_layered_model                none
% 2.18/1.01  --bmc1_ucm_max_lemma_size               10
% 2.18/1.01  
% 2.18/1.01  ------ AIG Options
% 2.18/1.01  
% 2.18/1.01  --aig_mode                              false
% 2.18/1.01  
% 2.18/1.01  ------ Instantiation Options
% 2.18/1.01  
% 2.18/1.01  --instantiation_flag                    true
% 2.18/1.01  --inst_sos_flag                         false
% 2.18/1.01  --inst_sos_phase                        true
% 2.18/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel_side                     num_symb
% 2.18/1.01  --inst_solver_per_active                1400
% 2.18/1.01  --inst_solver_calls_frac                1.
% 2.18/1.01  --inst_passive_queue_type               priority_queues
% 2.18/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.01  --inst_passive_queues_freq              [25;2]
% 2.18/1.01  --inst_dismatching                      true
% 2.18/1.01  --inst_eager_unprocessed_to_passive     true
% 2.18/1.01  --inst_prop_sim_given                   true
% 2.18/1.01  --inst_prop_sim_new                     false
% 2.18/1.01  --inst_subs_new                         false
% 2.18/1.01  --inst_eq_res_simp                      false
% 2.18/1.01  --inst_subs_given                       false
% 2.18/1.01  --inst_orphan_elimination               true
% 2.18/1.01  --inst_learning_loop_flag               true
% 2.18/1.01  --inst_learning_start                   3000
% 2.18/1.01  --inst_learning_factor                  2
% 2.18/1.01  --inst_start_prop_sim_after_learn       3
% 2.18/1.01  --inst_sel_renew                        solver
% 2.18/1.01  --inst_lit_activity_flag                true
% 2.18/1.01  --inst_restr_to_given                   false
% 2.18/1.01  --inst_activity_threshold               500
% 2.18/1.01  --inst_out_proof                        true
% 2.18/1.01  
% 2.18/1.01  ------ Resolution Options
% 2.18/1.01  
% 2.18/1.01  --resolution_flag                       true
% 2.18/1.01  --res_lit_sel                           adaptive
% 2.18/1.01  --res_lit_sel_side                      none
% 2.18/1.01  --res_ordering                          kbo
% 2.18/1.01  --res_to_prop_solver                    active
% 2.18/1.01  --res_prop_simpl_new                    false
% 2.18/1.01  --res_prop_simpl_given                  true
% 2.18/1.01  --res_passive_queue_type                priority_queues
% 2.18/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.01  --res_passive_queues_freq               [15;5]
% 2.18/1.01  --res_forward_subs                      full
% 2.18/1.01  --res_backward_subs                     full
% 2.18/1.01  --res_forward_subs_resolution           true
% 2.18/1.01  --res_backward_subs_resolution          true
% 2.18/1.01  --res_orphan_elimination                true
% 2.18/1.01  --res_time_limit                        2.
% 2.18/1.01  --res_out_proof                         true
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Options
% 2.18/1.01  
% 2.18/1.01  --superposition_flag                    true
% 2.18/1.01  --sup_passive_queue_type                priority_queues
% 2.18/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.01  --demod_completeness_check              fast
% 2.18/1.01  --demod_use_ground                      true
% 2.18/1.01  --sup_to_prop_solver                    passive
% 2.18/1.01  --sup_prop_simpl_new                    true
% 2.18/1.01  --sup_prop_simpl_given                  true
% 2.18/1.01  --sup_fun_splitting                     false
% 2.18/1.01  --sup_smt_interval                      50000
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Simplification Setup
% 2.18/1.01  
% 2.18/1.01  --sup_indices_passive                   []
% 2.18/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_full_bw                           [BwDemod]
% 2.18/1.01  --sup_immed_triv                        [TrivRules]
% 2.18/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_immed_bw_main                     []
% 2.18/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  
% 2.18/1.01  ------ Combination Options
% 2.18/1.01  
% 2.18/1.01  --comb_res_mult                         3
% 2.18/1.01  --comb_sup_mult                         2
% 2.18/1.01  --comb_inst_mult                        10
% 2.18/1.01  
% 2.18/1.01  ------ Debug Options
% 2.18/1.01  
% 2.18/1.01  --dbg_backtrace                         false
% 2.18/1.01  --dbg_dump_prop_clauses                 false
% 2.18/1.01  --dbg_dump_prop_clauses_file            -
% 2.18/1.01  --dbg_out_stat                          false
% 2.18/1.01  ------ Parsing...
% 2.18/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.18/1.01  ------ Proving...
% 2.18/1.01  ------ Problem Properties 
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  clauses                                 23
% 2.18/1.01  conjectures                             2
% 2.18/1.01  EPR                                     4
% 2.18/1.01  Horn                                    22
% 2.18/1.01  unary                                   8
% 2.18/1.01  binary                                  10
% 2.18/1.01  lits                                    43
% 2.18/1.01  lits eq                                 23
% 2.18/1.01  fd_pure                                 0
% 2.18/1.01  fd_pseudo                               0
% 2.18/1.01  fd_cond                                 2
% 2.18/1.01  fd_pseudo_cond                          2
% 2.18/1.01  AC symbols                              0
% 2.18/1.01  
% 2.18/1.01  ------ Schedule dynamic 5 is on 
% 2.18/1.01  
% 2.18/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  ------ 
% 2.18/1.01  Current options:
% 2.18/1.01  ------ 
% 2.18/1.01  
% 2.18/1.01  ------ Input Options
% 2.18/1.01  
% 2.18/1.01  --out_options                           all
% 2.18/1.01  --tptp_safe_out                         true
% 2.18/1.01  --problem_path                          ""
% 2.18/1.01  --include_path                          ""
% 2.18/1.01  --clausifier                            res/vclausify_rel
% 2.18/1.01  --clausifier_options                    --mode clausify
% 2.18/1.01  --stdin                                 false
% 2.18/1.01  --stats_out                             all
% 2.18/1.01  
% 2.18/1.01  ------ General Options
% 2.18/1.01  
% 2.18/1.01  --fof                                   false
% 2.18/1.01  --time_out_real                         305.
% 2.18/1.01  --time_out_virtual                      -1.
% 2.18/1.01  --symbol_type_check                     false
% 2.18/1.01  --clausify_out                          false
% 2.18/1.01  --sig_cnt_out                           false
% 2.18/1.01  --trig_cnt_out                          false
% 2.18/1.01  --trig_cnt_out_tolerance                1.
% 2.18/1.01  --trig_cnt_out_sk_spl                   false
% 2.18/1.01  --abstr_cl_out                          false
% 2.18/1.01  
% 2.18/1.01  ------ Global Options
% 2.18/1.01  
% 2.18/1.01  --schedule                              default
% 2.18/1.01  --add_important_lit                     false
% 2.18/1.01  --prop_solver_per_cl                    1000
% 2.18/1.01  --min_unsat_core                        false
% 2.18/1.01  --soft_assumptions                      false
% 2.18/1.01  --soft_lemma_size                       3
% 2.18/1.01  --prop_impl_unit_size                   0
% 2.18/1.01  --prop_impl_unit                        []
% 2.18/1.01  --share_sel_clauses                     true
% 2.18/1.01  --reset_solvers                         false
% 2.18/1.01  --bc_imp_inh                            [conj_cone]
% 2.18/1.01  --conj_cone_tolerance                   3.
% 2.18/1.01  --extra_neg_conj                        none
% 2.18/1.01  --large_theory_mode                     true
% 2.18/1.01  --prolific_symb_bound                   200
% 2.18/1.01  --lt_threshold                          2000
% 2.18/1.01  --clause_weak_htbl                      true
% 2.18/1.01  --gc_record_bc_elim                     false
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing Options
% 2.18/1.01  
% 2.18/1.01  --preprocessing_flag                    true
% 2.18/1.01  --time_out_prep_mult                    0.1
% 2.18/1.01  --splitting_mode                        input
% 2.18/1.01  --splitting_grd                         true
% 2.18/1.01  --splitting_cvd                         false
% 2.18/1.01  --splitting_cvd_svl                     false
% 2.18/1.01  --splitting_nvd                         32
% 2.18/1.01  --sub_typing                            true
% 2.18/1.01  --prep_gs_sim                           true
% 2.18/1.01  --prep_unflatten                        true
% 2.18/1.01  --prep_res_sim                          true
% 2.18/1.01  --prep_upred                            true
% 2.18/1.01  --prep_sem_filter                       exhaustive
% 2.18/1.01  --prep_sem_filter_out                   false
% 2.18/1.01  --pred_elim                             true
% 2.18/1.01  --res_sim_input                         true
% 2.18/1.01  --eq_ax_congr_red                       true
% 2.18/1.01  --pure_diseq_elim                       true
% 2.18/1.01  --brand_transform                       false
% 2.18/1.01  --non_eq_to_eq                          false
% 2.18/1.01  --prep_def_merge                        true
% 2.18/1.01  --prep_def_merge_prop_impl              false
% 2.18/1.01  --prep_def_merge_mbd                    true
% 2.18/1.01  --prep_def_merge_tr_red                 false
% 2.18/1.01  --prep_def_merge_tr_cl                  false
% 2.18/1.01  --smt_preprocessing                     true
% 2.18/1.01  --smt_ac_axioms                         fast
% 2.18/1.01  --preprocessed_out                      false
% 2.18/1.01  --preprocessed_stats                    false
% 2.18/1.01  
% 2.18/1.01  ------ Abstraction refinement Options
% 2.18/1.01  
% 2.18/1.01  --abstr_ref                             []
% 2.18/1.01  --abstr_ref_prep                        false
% 2.18/1.01  --abstr_ref_until_sat                   false
% 2.18/1.01  --abstr_ref_sig_restrict                funpre
% 2.18/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.18/1.01  --abstr_ref_under                       []
% 2.18/1.01  
% 2.18/1.01  ------ SAT Options
% 2.18/1.01  
% 2.18/1.01  --sat_mode                              false
% 2.18/1.01  --sat_fm_restart_options                ""
% 2.18/1.01  --sat_gr_def                            false
% 2.18/1.01  --sat_epr_types                         true
% 2.18/1.01  --sat_non_cyclic_types                  false
% 2.18/1.01  --sat_finite_models                     false
% 2.18/1.01  --sat_fm_lemmas                         false
% 2.18/1.01  --sat_fm_prep                           false
% 2.18/1.01  --sat_fm_uc_incr                        true
% 2.18/1.01  --sat_out_model                         small
% 2.18/1.01  --sat_out_clauses                       false
% 2.18/1.01  
% 2.18/1.01  ------ QBF Options
% 2.18/1.01  
% 2.18/1.01  --qbf_mode                              false
% 2.18/1.01  --qbf_elim_univ                         false
% 2.18/1.01  --qbf_dom_inst                          none
% 2.18/1.01  --qbf_dom_pre_inst                      false
% 2.18/1.01  --qbf_sk_in                             false
% 2.18/1.01  --qbf_pred_elim                         true
% 2.18/1.01  --qbf_split                             512
% 2.18/1.01  
% 2.18/1.01  ------ BMC1 Options
% 2.18/1.01  
% 2.18/1.01  --bmc1_incremental                      false
% 2.18/1.01  --bmc1_axioms                           reachable_all
% 2.18/1.01  --bmc1_min_bound                        0
% 2.18/1.01  --bmc1_max_bound                        -1
% 2.18/1.01  --bmc1_max_bound_default                -1
% 2.18/1.01  --bmc1_symbol_reachability              true
% 2.18/1.01  --bmc1_property_lemmas                  false
% 2.18/1.01  --bmc1_k_induction                      false
% 2.18/1.01  --bmc1_non_equiv_states                 false
% 2.18/1.01  --bmc1_deadlock                         false
% 2.18/1.01  --bmc1_ucm                              false
% 2.18/1.01  --bmc1_add_unsat_core                   none
% 2.18/1.01  --bmc1_unsat_core_children              false
% 2.18/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.18/1.01  --bmc1_out_stat                         full
% 2.18/1.01  --bmc1_ground_init                      false
% 2.18/1.01  --bmc1_pre_inst_next_state              false
% 2.18/1.01  --bmc1_pre_inst_state                   false
% 2.18/1.01  --bmc1_pre_inst_reach_state             false
% 2.18/1.01  --bmc1_out_unsat_core                   false
% 2.18/1.01  --bmc1_aig_witness_out                  false
% 2.18/1.01  --bmc1_verbose                          false
% 2.18/1.01  --bmc1_dump_clauses_tptp                false
% 2.18/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.18/1.01  --bmc1_dump_file                        -
% 2.18/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.18/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.18/1.01  --bmc1_ucm_extend_mode                  1
% 2.18/1.01  --bmc1_ucm_init_mode                    2
% 2.18/1.01  --bmc1_ucm_cone_mode                    none
% 2.18/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.18/1.01  --bmc1_ucm_relax_model                  4
% 2.18/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.18/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.18/1.01  --bmc1_ucm_layered_model                none
% 2.18/1.01  --bmc1_ucm_max_lemma_size               10
% 2.18/1.01  
% 2.18/1.01  ------ AIG Options
% 2.18/1.01  
% 2.18/1.01  --aig_mode                              false
% 2.18/1.01  
% 2.18/1.01  ------ Instantiation Options
% 2.18/1.01  
% 2.18/1.01  --instantiation_flag                    true
% 2.18/1.01  --inst_sos_flag                         false
% 2.18/1.01  --inst_sos_phase                        true
% 2.18/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.18/1.01  --inst_lit_sel_side                     none
% 2.18/1.01  --inst_solver_per_active                1400
% 2.18/1.01  --inst_solver_calls_frac                1.
% 2.18/1.01  --inst_passive_queue_type               priority_queues
% 2.18/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.18/1.01  --inst_passive_queues_freq              [25;2]
% 2.18/1.01  --inst_dismatching                      true
% 2.18/1.01  --inst_eager_unprocessed_to_passive     true
% 2.18/1.01  --inst_prop_sim_given                   true
% 2.18/1.01  --inst_prop_sim_new                     false
% 2.18/1.01  --inst_subs_new                         false
% 2.18/1.01  --inst_eq_res_simp                      false
% 2.18/1.01  --inst_subs_given                       false
% 2.18/1.01  --inst_orphan_elimination               true
% 2.18/1.01  --inst_learning_loop_flag               true
% 2.18/1.01  --inst_learning_start                   3000
% 2.18/1.01  --inst_learning_factor                  2
% 2.18/1.01  --inst_start_prop_sim_after_learn       3
% 2.18/1.01  --inst_sel_renew                        solver
% 2.18/1.01  --inst_lit_activity_flag                true
% 2.18/1.01  --inst_restr_to_given                   false
% 2.18/1.01  --inst_activity_threshold               500
% 2.18/1.01  --inst_out_proof                        true
% 2.18/1.01  
% 2.18/1.01  ------ Resolution Options
% 2.18/1.01  
% 2.18/1.01  --resolution_flag                       false
% 2.18/1.01  --res_lit_sel                           adaptive
% 2.18/1.01  --res_lit_sel_side                      none
% 2.18/1.01  --res_ordering                          kbo
% 2.18/1.01  --res_to_prop_solver                    active
% 2.18/1.01  --res_prop_simpl_new                    false
% 2.18/1.01  --res_prop_simpl_given                  true
% 2.18/1.01  --res_passive_queue_type                priority_queues
% 2.18/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.18/1.01  --res_passive_queues_freq               [15;5]
% 2.18/1.01  --res_forward_subs                      full
% 2.18/1.01  --res_backward_subs                     full
% 2.18/1.01  --res_forward_subs_resolution           true
% 2.18/1.01  --res_backward_subs_resolution          true
% 2.18/1.01  --res_orphan_elimination                true
% 2.18/1.01  --res_time_limit                        2.
% 2.18/1.01  --res_out_proof                         true
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Options
% 2.18/1.01  
% 2.18/1.01  --superposition_flag                    true
% 2.18/1.01  --sup_passive_queue_type                priority_queues
% 2.18/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.18/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.18/1.01  --demod_completeness_check              fast
% 2.18/1.01  --demod_use_ground                      true
% 2.18/1.01  --sup_to_prop_solver                    passive
% 2.18/1.01  --sup_prop_simpl_new                    true
% 2.18/1.01  --sup_prop_simpl_given                  true
% 2.18/1.01  --sup_fun_splitting                     false
% 2.18/1.01  --sup_smt_interval                      50000
% 2.18/1.01  
% 2.18/1.01  ------ Superposition Simplification Setup
% 2.18/1.01  
% 2.18/1.01  --sup_indices_passive                   []
% 2.18/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.18/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.18/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_full_bw                           [BwDemod]
% 2.18/1.01  --sup_immed_triv                        [TrivRules]
% 2.18/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.18/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_immed_bw_main                     []
% 2.18/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.18/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.18/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.18/1.01  
% 2.18/1.01  ------ Combination Options
% 2.18/1.01  
% 2.18/1.01  --comb_res_mult                         3
% 2.18/1.01  --comb_sup_mult                         2
% 2.18/1.01  --comb_inst_mult                        10
% 2.18/1.01  
% 2.18/1.01  ------ Debug Options
% 2.18/1.01  
% 2.18/1.01  --dbg_backtrace                         false
% 2.18/1.01  --dbg_dump_prop_clauses                 false
% 2.18/1.01  --dbg_dump_prop_clauses_file            -
% 2.18/1.01  --dbg_out_stat                          false
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  ------ Proving...
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  % SZS status Theorem for theBenchmark.p
% 2.18/1.01  
% 2.18/1.01   Resolution empty clause
% 2.18/1.01  
% 2.18/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  fof(f18,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f23,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.18/1.01    inference(pure_predicate_removal,[],[f18])).
% 2.18/1.01  
% 2.18/1.01  fof(f36,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/1.01    inference(ennf_transformation,[],[f23])).
% 2.18/1.01  
% 2.18/1.01  fof(f68,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f36])).
% 2.18/1.01  
% 2.18/1.01  fof(f11,axiom,(
% 2.18/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f27,plain,(
% 2.18/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.18/1.01    inference(ennf_transformation,[],[f11])).
% 2.18/1.01  
% 2.18/1.01  fof(f28,plain,(
% 2.18/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.18/1.01    inference(flattening,[],[f27])).
% 2.18/1.01  
% 2.18/1.01  fof(f59,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f28])).
% 2.18/1.01  
% 2.18/1.01  fof(f17,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f35,plain,(
% 2.18/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/1.01    inference(ennf_transformation,[],[f17])).
% 2.18/1.01  
% 2.18/1.01  fof(f67,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f35])).
% 2.18/1.01  
% 2.18/1.01  fof(f20,conjecture,(
% 2.18/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f21,negated_conjecture,(
% 2.18/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.18/1.01    inference(negated_conjecture,[],[f20])).
% 2.18/1.01  
% 2.18/1.01  fof(f22,plain,(
% 2.18/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.18/1.01    inference(pure_predicate_removal,[],[f21])).
% 2.18/1.01  
% 2.18/1.01  fof(f38,plain,(
% 2.18/1.01    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.18/1.01    inference(ennf_transformation,[],[f22])).
% 2.18/1.01  
% 2.18/1.01  fof(f39,plain,(
% 2.18/1.01    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.18/1.01    inference(flattening,[],[f38])).
% 2.18/1.01  
% 2.18/1.01  fof(f44,plain,(
% 2.18/1.01    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.18/1.01    introduced(choice_axiom,[])).
% 2.18/1.01  
% 2.18/1.01  fof(f45,plain,(
% 2.18/1.01    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.18/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f39,f44])).
% 2.18/1.01  
% 2.18/1.01  fof(f71,plain,(
% 2.18/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.18/1.01    inference(cnf_transformation,[],[f45])).
% 2.18/1.01  
% 2.18/1.01  fof(f3,axiom,(
% 2.18/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f50,plain,(
% 2.18/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f3])).
% 2.18/1.01  
% 2.18/1.01  fof(f4,axiom,(
% 2.18/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f51,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f4])).
% 2.18/1.01  
% 2.18/1.01  fof(f5,axiom,(
% 2.18/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f52,plain,(
% 2.18/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f5])).
% 2.18/1.01  
% 2.18/1.01  fof(f74,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.18/1.01    inference(definition_unfolding,[],[f51,f52])).
% 2.18/1.01  
% 2.18/1.01  fof(f75,plain,(
% 2.18/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.18/1.01    inference(definition_unfolding,[],[f50,f74])).
% 2.18/1.01  
% 2.18/1.01  fof(f81,plain,(
% 2.18/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.18/1.01    inference(definition_unfolding,[],[f71,f75])).
% 2.18/1.01  
% 2.18/1.01  fof(f14,axiom,(
% 2.18/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f31,plain,(
% 2.18/1.01    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.18/1.01    inference(ennf_transformation,[],[f14])).
% 2.18/1.01  
% 2.18/1.01  fof(f64,plain,(
% 2.18/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f31])).
% 2.18/1.01  
% 2.18/1.01  fof(f6,axiom,(
% 2.18/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f42,plain,(
% 2.18/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.18/1.01    inference(nnf_transformation,[],[f6])).
% 2.18/1.01  
% 2.18/1.01  fof(f43,plain,(
% 2.18/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.18/1.01    inference(flattening,[],[f42])).
% 2.18/1.01  
% 2.18/1.01  fof(f53,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f43])).
% 2.18/1.01  
% 2.18/1.01  fof(f78,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 2.18/1.01    inference(definition_unfolding,[],[f53,f75,f75])).
% 2.18/1.01  
% 2.18/1.01  fof(f73,plain,(
% 2.18/1.01    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.18/1.01    inference(cnf_transformation,[],[f45])).
% 2.18/1.01  
% 2.18/1.01  fof(f80,plain,(
% 2.18/1.01    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.18/1.01    inference(definition_unfolding,[],[f73,f75,f75])).
% 2.18/1.01  
% 2.18/1.01  fof(f19,axiom,(
% 2.18/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f37,plain,(
% 2.18/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/1.01    inference(ennf_transformation,[],[f19])).
% 2.18/1.01  
% 2.18/1.01  fof(f69,plain,(
% 2.18/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f37])).
% 2.18/1.01  
% 2.18/1.01  fof(f9,axiom,(
% 2.18/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f25,plain,(
% 2.18/1.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.18/1.01    inference(ennf_transformation,[],[f9])).
% 2.18/1.01  
% 2.18/1.01  fof(f57,plain,(
% 2.18/1.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f25])).
% 2.18/1.01  
% 2.18/1.01  fof(f16,axiom,(
% 2.18/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f33,plain,(
% 2.18/1.01    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.18/1.01    inference(ennf_transformation,[],[f16])).
% 2.18/1.01  
% 2.18/1.01  fof(f34,plain,(
% 2.18/1.01    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.18/1.01    inference(flattening,[],[f33])).
% 2.18/1.01  
% 2.18/1.01  fof(f66,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f34])).
% 2.18/1.01  
% 2.18/1.01  fof(f79,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.18/1.01    inference(definition_unfolding,[],[f66,f75,f75])).
% 2.18/1.01  
% 2.18/1.01  fof(f70,plain,(
% 2.18/1.01    v1_funct_1(sK3)),
% 2.18/1.01    inference(cnf_transformation,[],[f45])).
% 2.18/1.01  
% 2.18/1.01  fof(f13,axiom,(
% 2.18/1.01    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f29,plain,(
% 2.18/1.01    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(ennf_transformation,[],[f13])).
% 2.18/1.01  
% 2.18/1.01  fof(f30,plain,(
% 2.18/1.01    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.18/1.01    inference(flattening,[],[f29])).
% 2.18/1.01  
% 2.18/1.01  fof(f62,plain,(
% 2.18/1.01    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f30])).
% 2.18/1.01  
% 2.18/1.01  fof(f7,axiom,(
% 2.18/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f56,plain,(
% 2.18/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.18/1.01    inference(cnf_transformation,[],[f7])).
% 2.18/1.01  
% 2.18/1.01  fof(f10,axiom,(
% 2.18/1.01    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f26,plain,(
% 2.18/1.01    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.18/1.01    inference(ennf_transformation,[],[f10])).
% 2.18/1.01  
% 2.18/1.01  fof(f58,plain,(
% 2.18/1.01    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f26])).
% 2.18/1.01  
% 2.18/1.01  fof(f12,axiom,(
% 2.18/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f61,plain,(
% 2.18/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.18/1.01    inference(cnf_transformation,[],[f12])).
% 2.18/1.01  
% 2.18/1.01  fof(f2,axiom,(
% 2.18/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.18/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.18/1.01  
% 2.18/1.01  fof(f49,plain,(
% 2.18/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.18/1.01    inference(cnf_transformation,[],[f2])).
% 2.18/1.01  
% 2.18/1.01  cnf(c_19,plain,
% 2.18/1.01      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.18/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_10,plain,
% 2.18/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.18/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_251,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | k7_relat_1(X0,X1) = X0 ),
% 2.18/1.01      inference(resolution,[status(thm)],[c_19,c_10]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_18,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_255,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | k7_relat_1(X0,X1) = X0 ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_251,c_19,c_18,c_10]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_23,negated_conjecture,
% 2.18/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.18/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_320,plain,
% 2.18/1.01      ( k7_relat_1(X0,X1) = X0
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.18/1.01      | sK3 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_255,c_23]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_321,plain,
% 2.18/1.01      ( k7_relat_1(sK3,X0) = sK3
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_320]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1228,plain,
% 2.18/1.01      ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = sK3 ),
% 2.18/1.01      inference(equality_resolution,[status(thm)],[c_321]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_15,plain,
% 2.18/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1100,plain,
% 2.18/1.01      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 2.18/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1724,plain,
% 2.18/1.01      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1228,c_1100]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_807,plain,( X0 = X0 ),theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1229,plain,
% 2.18/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_807]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_338,plain,
% 2.18/1.01      ( v1_relat_1(X0)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.18/1.01      | sK3 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_23]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_339,plain,
% 2.18/1.01      ( v1_relat_1(sK3)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_338]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1232,plain,
% 2.18/1.01      ( v1_relat_1(sK3)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_339]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1233,plain,
% 2.18/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.18/1.01      | v1_relat_1(sK3) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_1232]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1758,plain,
% 2.18/1.01      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_1724,c_1229,c_1233]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_6,plain,
% 2.18/1.01      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 2.18/1.01      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.18/1.01      | k1_xboole_0 = X0 ),
% 2.18/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1105,plain,
% 2.18/1.01      ( k2_enumset1(X0,X0,X0,X0) = X1
% 2.18/1.01      | k1_xboole_0 = X1
% 2.18/1.01      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2656,plain,
% 2.18/1.01      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.18/1.01      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1758,c_1105]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2838,plain,
% 2.18/1.01      ( k7_relat_1(sK3,X0) = sK3
% 2.18/1.01      | k1_relat_1(sK3) = k1_xboole_0
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2656,c_321]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_21,negated_conjecture,
% 2.18/1.01      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.18/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_20,plain,
% 2.18/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.18/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.18/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_329,plain,
% 2.18/1.01      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.18/1.01      | sK3 != X2 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_23]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_330,plain,
% 2.18/1.01      ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_329]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1230,plain,
% 2.18/1.01      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_330]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1351,plain,
% 2.18/1.01      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_1230]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_809,plain,
% 2.18/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.18/1.01      theory(equality) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1283,plain,
% 2.18/1.01      ( ~ r1_tarski(X0,X1)
% 2.18/1.01      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.18/1.01      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 2.18/1.01      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_809]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1352,plain,
% 2.18/1.01      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.18/1.01      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 2.18/1.01      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.18/1.01      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_1283]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1423,plain,
% 2.18/1.01      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.18/1.01      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.18/1.01      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.18/1.01      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_1352]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_8,plain,
% 2.18/1.01      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1424,plain,
% 2.18/1.01      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_17,plain,
% 2.18/1.01      ( ~ v1_funct_1(X0)
% 2.18/1.01      | ~ v1_relat_1(X0)
% 2.18/1.01      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.18/1.01      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_24,negated_conjecture,
% 2.18/1.01      ( v1_funct_1(sK3) ),
% 2.18/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_271,plain,
% 2.18/1.01      ( ~ v1_relat_1(X0)
% 2.18/1.01      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.18/1.01      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.18/1.01      | sK3 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_24]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_272,plain,
% 2.18/1.01      ( ~ v1_relat_1(sK3)
% 2.18/1.01      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.18/1.01      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_271]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1097,plain,
% 2.18/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.18/1.01      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_273,plain,
% 2.18/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.18/1.01      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.18/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1566,plain,
% 2.18/1.01      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.18/1.01      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_1097,c_273,c_1229,c_1233]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1567,plain,
% 2.18/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.18/1.01      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.18/1.01      inference(renaming,[status(thm)],[c_1566]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2831,plain,
% 2.18/1.01      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.18/1.01      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2656,c_1567]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_2992,plain,
% 2.18/1.01      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_2838,c_21,c_1229,c_1232,c_1351,c_1423,c_1424,c_2831]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_14,plain,
% 2.18/1.01      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.18/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1101,plain,
% 2.18/1.01      ( k1_relat_1(X0) != k1_xboole_0
% 2.18/1.01      | k1_xboole_0 = X0
% 2.18/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3010,plain,
% 2.18/1.01      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_2992,c_1101]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3076,plain,
% 2.18/1.01      ( sK3 = k1_xboole_0 ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_3010,c_1229,c_1233]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1256,plain,
% 2.18/1.01      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.18/1.01      inference(equality_resolution,[status(thm)],[c_330]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1098,plain,
% 2.18/1.01      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1281,plain,
% 2.18/1.01      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_1256,c_1098]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3086,plain,
% 2.18/1.01      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_3076,c_1281]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_7,plain,
% 2.18/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.18/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_308,plain,
% 2.18/1.01      ( v1_relat_1(X0)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
% 2.18/1.01      | k1_xboole_0 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_309,plain,
% 2.18/1.01      ( v1_relat_1(k1_xboole_0)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_308]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1096,plain,
% 2.18/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2)
% 2.18/1.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1242,plain,
% 2.18/1.01      ( v1_relat_1(k1_xboole_0)
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_309]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1244,plain,
% 2.18/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.18/1.01      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_1242]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1243,plain,
% 2.18/1.01      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.18/1.01      inference(instantiation,[status(thm)],[c_807]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1648,plain,
% 2.18/1.01      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.18/1.01      inference(global_propositional_subsumption,
% 2.18/1.01                [status(thm)],
% 2.18/1.01                [c_1096,c_1244,c_1243]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_9,plain,
% 2.18/1.01      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.18/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1103,plain,
% 2.18/1.01      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.18/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1766,plain,
% 2.18/1.01      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 2.18/1.01      inference(superposition,[status(thm)],[c_1648,c_1103]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_11,plain,
% 2.18/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.18/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_290,plain,
% 2.18/1.01      ( k7_relat_1(X0,X1) = X0
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(X3)
% 2.18/1.01      | k1_xboole_0 != X0 ),
% 2.18/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_255]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_291,plain,
% 2.18/1.01      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 2.18/1.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(X2) ),
% 2.18/1.01      inference(unflattening,[status(thm)],[c_290]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1359,plain,
% 2.18/1.01      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.18/1.01      inference(equality_resolution,[status(thm)],[c_291]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1771,plain,
% 2.18/1.01      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.18/1.01      inference(light_normalisation,[status(thm)],[c_1766,c_11,c_1359]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3100,plain,
% 2.18/1.01      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.18/1.01      inference(demodulation,[status(thm)],[c_3086,c_1771]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3,plain,
% 2.18/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.18/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_1108,plain,
% 2.18/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.18/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.18/1.01  
% 2.18/1.01  cnf(c_3305,plain,
% 2.18/1.01      ( $false ),
% 2.18/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_3100,c_1108]) ).
% 2.18/1.01  
% 2.18/1.01  
% 2.18/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.18/1.01  
% 2.18/1.01  ------                               Statistics
% 2.18/1.01  
% 2.18/1.01  ------ General
% 2.18/1.01  
% 2.18/1.01  abstr_ref_over_cycles:                  0
% 2.18/1.01  abstr_ref_under_cycles:                 0
% 2.18/1.01  gc_basic_clause_elim:                   0
% 2.18/1.01  forced_gc_time:                         0
% 2.18/1.01  parsing_time:                           0.009
% 2.18/1.01  unif_index_cands_time:                  0.
% 2.18/1.01  unif_index_add_time:                    0.
% 2.18/1.01  orderings_time:                         0.
% 2.18/1.01  out_proof_time:                         0.01
% 2.18/1.01  total_time:                             0.135
% 2.18/1.01  num_of_symbols:                         50
% 2.18/1.01  num_of_terms:                           2929
% 2.18/1.01  
% 2.18/1.01  ------ Preprocessing
% 2.18/1.01  
% 2.18/1.01  num_of_splits:                          0
% 2.18/1.01  num_of_split_atoms:                     0
% 2.18/1.01  num_of_reused_defs:                     0
% 2.18/1.01  num_eq_ax_congr_red:                    11
% 2.18/1.01  num_of_sem_filtered_clauses:            1
% 2.18/1.01  num_of_subtypes:                        0
% 2.18/1.01  monotx_restored_types:                  0
% 2.18/1.01  sat_num_of_epr_types:                   0
% 2.18/1.01  sat_num_of_non_cyclic_types:            0
% 2.18/1.01  sat_guarded_non_collapsed_types:        0
% 2.18/1.01  num_pure_diseq_elim:                    0
% 2.18/1.01  simp_replaced_by:                       0
% 2.18/1.01  res_preprocessed:                       120
% 2.18/1.01  prep_upred:                             0
% 2.18/1.01  prep_unflattend:                        31
% 2.18/1.01  smt_new_axioms:                         0
% 2.18/1.01  pred_elim_cands:                        2
% 2.18/1.01  pred_elim:                              3
% 2.18/1.01  pred_elim_cl:                           1
% 2.18/1.01  pred_elim_cycles:                       5
% 2.18/1.01  merged_defs:                            0
% 2.18/1.01  merged_defs_ncl:                        0
% 2.18/1.01  bin_hyper_res:                          0
% 2.18/1.01  prep_cycles:                            4
% 2.18/1.01  pred_elim_time:                         0.008
% 2.18/1.01  splitting_time:                         0.
% 2.18/1.01  sem_filter_time:                        0.
% 2.18/1.01  monotx_time:                            0.001
% 2.18/1.01  subtype_inf_time:                       0.
% 2.18/1.01  
% 2.18/1.01  ------ Problem properties
% 2.18/1.01  
% 2.18/1.01  clauses:                                23
% 2.18/1.01  conjectures:                            2
% 2.18/1.01  epr:                                    4
% 2.18/1.01  horn:                                   22
% 2.18/1.01  ground:                                 4
% 2.18/1.01  unary:                                  8
% 2.18/1.01  binary:                                 10
% 2.18/1.01  lits:                                   43
% 2.18/1.01  lits_eq:                                23
% 2.18/1.01  fd_pure:                                0
% 2.18/1.01  fd_pseudo:                              0
% 2.18/1.01  fd_cond:                                2
% 2.18/1.01  fd_pseudo_cond:                         2
% 2.18/1.01  ac_symbols:                             0
% 2.18/1.01  
% 2.18/1.01  ------ Propositional Solver
% 2.18/1.01  
% 2.18/1.01  prop_solver_calls:                      28
% 2.18/1.01  prop_fast_solver_calls:                 683
% 2.18/1.01  smt_solver_calls:                       0
% 2.18/1.01  smt_fast_solver_calls:                  0
% 2.18/1.01  prop_num_of_clauses:                    1193
% 2.18/1.01  prop_preprocess_simplified:             4377
% 2.18/1.01  prop_fo_subsumed:                       14
% 2.18/1.01  prop_solver_time:                       0.
% 2.18/1.01  smt_solver_time:                        0.
% 2.18/1.01  smt_fast_solver_time:                   0.
% 2.18/1.01  prop_fast_solver_time:                  0.
% 2.18/1.01  prop_unsat_core_time:                   0.
% 2.18/1.01  
% 2.18/1.01  ------ QBF
% 2.18/1.01  
% 2.18/1.01  qbf_q_res:                              0
% 2.18/1.01  qbf_num_tautologies:                    0
% 2.18/1.01  qbf_prep_cycles:                        0
% 2.18/1.01  
% 2.18/1.01  ------ BMC1
% 2.18/1.01  
% 2.18/1.01  bmc1_current_bound:                     -1
% 2.18/1.01  bmc1_last_solved_bound:                 -1
% 2.18/1.01  bmc1_unsat_core_size:                   -1
% 2.18/1.01  bmc1_unsat_core_parents_size:           -1
% 2.18/1.01  bmc1_merge_next_fun:                    0
% 2.18/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.18/1.01  
% 2.18/1.01  ------ Instantiation
% 2.18/1.01  
% 2.18/1.01  inst_num_of_clauses:                    378
% 2.18/1.01  inst_num_in_passive:                    117
% 2.18/1.01  inst_num_in_active:                     210
% 2.18/1.01  inst_num_in_unprocessed:                51
% 2.18/1.01  inst_num_of_loops:                      230
% 2.18/1.01  inst_num_of_learning_restarts:          0
% 2.18/1.01  inst_num_moves_active_passive:          17
% 2.18/1.01  inst_lit_activity:                      0
% 2.18/1.01  inst_lit_activity_moves:                0
% 2.18/1.01  inst_num_tautologies:                   0
% 2.18/1.01  inst_num_prop_implied:                  0
% 2.18/1.02  inst_num_existing_simplified:           0
% 2.18/1.02  inst_num_eq_res_simplified:             0
% 2.18/1.02  inst_num_child_elim:                    0
% 2.18/1.02  inst_num_of_dismatching_blockings:      52
% 2.18/1.02  inst_num_of_non_proper_insts:           319
% 2.18/1.02  inst_num_of_duplicates:                 0
% 2.18/1.02  inst_inst_num_from_inst_to_res:         0
% 2.18/1.02  inst_dismatching_checking_time:         0.
% 2.18/1.02  
% 2.18/1.02  ------ Resolution
% 2.18/1.02  
% 2.18/1.02  res_num_of_clauses:                     0
% 2.18/1.02  res_num_in_passive:                     0
% 2.18/1.02  res_num_in_active:                      0
% 2.18/1.02  res_num_of_loops:                       124
% 2.18/1.02  res_forward_subset_subsumed:            60
% 2.18/1.02  res_backward_subset_subsumed:           2
% 2.18/1.02  res_forward_subsumed:                   0
% 2.18/1.02  res_backward_subsumed:                  0
% 2.18/1.02  res_forward_subsumption_resolution:     0
% 2.18/1.02  res_backward_subsumption_resolution:    0
% 2.18/1.02  res_clause_to_clause_subsumption:       137
% 2.18/1.02  res_orphan_elimination:                 0
% 2.18/1.02  res_tautology_del:                      32
% 2.18/1.02  res_num_eq_res_simplified:              0
% 2.18/1.02  res_num_sel_changes:                    0
% 2.18/1.02  res_moves_from_active_to_pass:          0
% 2.18/1.02  
% 2.18/1.02  ------ Superposition
% 2.18/1.02  
% 2.18/1.02  sup_time_total:                         0.
% 2.18/1.02  sup_time_generating:                    0.
% 2.18/1.02  sup_time_sim_full:                      0.
% 2.18/1.02  sup_time_sim_immed:                     0.
% 2.18/1.02  
% 2.18/1.02  sup_num_of_clauses:                     34
% 2.18/1.02  sup_num_in_active:                      24
% 2.18/1.02  sup_num_in_passive:                     10
% 2.18/1.02  sup_num_of_loops:                       44
% 2.18/1.02  sup_fw_superposition:                   39
% 2.18/1.02  sup_bw_superposition:                   13
% 2.18/1.02  sup_immediate_simplified:               29
% 2.18/1.02  sup_given_eliminated:                   0
% 2.18/1.02  comparisons_done:                       0
% 2.18/1.02  comparisons_avoided:                    0
% 2.18/1.02  
% 2.18/1.02  ------ Simplifications
% 2.18/1.02  
% 2.18/1.02  
% 2.18/1.02  sim_fw_subset_subsumed:                 6
% 2.18/1.02  sim_bw_subset_subsumed:                 2
% 2.18/1.02  sim_fw_subsumed:                        14
% 2.18/1.02  sim_bw_subsumed:                        0
% 2.18/1.02  sim_fw_subsumption_res:                 1
% 2.18/1.02  sim_bw_subsumption_res:                 0
% 2.18/1.02  sim_tautology_del:                      0
% 2.18/1.02  sim_eq_tautology_del:                   11
% 2.18/1.02  sim_eq_res_simp:                        0
% 2.18/1.02  sim_fw_demodulated:                     5
% 2.18/1.02  sim_bw_demodulated:                     19
% 2.18/1.02  sim_light_normalised:                   15
% 2.18/1.02  sim_joinable_taut:                      0
% 2.18/1.02  sim_joinable_simp:                      0
% 2.18/1.02  sim_ac_normalised:                      0
% 2.18/1.02  sim_smt_subsumption:                    0
% 2.18/1.02  
%------------------------------------------------------------------------------
