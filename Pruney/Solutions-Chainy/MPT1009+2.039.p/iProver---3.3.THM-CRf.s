%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:36 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 539 expanded)
%              Number of clauses        :   71 ( 116 expanded)
%              Number of leaves         :   20 ( 135 expanded)
%              Depth                    :   20
%              Number of atoms          :  400 (1319 expanded)
%              Number of equality atoms :  213 ( 632 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f21,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f35])).

fof(f45,plain,
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

fof(f46,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f45])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f84,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f85,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f84])).

fof(f97,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f81,f85])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
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

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
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
    inference(definition_unfolding,[],[f57,f53,f84,f84,f84,f85,f85,f85,f53])).

fof(f83,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f96,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f83,f85,f85])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f74,f85,f85])).

fof(f80,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f79,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f101,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1637,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_26,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_20,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_389,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_26,c_20])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_393,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_25])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_393])).

cnf(c_1634,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_1897,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1637,c_1634])).

cnf(c_15,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1645,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4293,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1897,c_1645])).

cnf(c_4643,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4293,c_1637])).

cnf(c_30,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1818,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1864,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1936,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1864])).

cnf(c_1092,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1847,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_1092])).

cnf(c_1935,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1847])).

cnf(c_2058,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1935])).

cnf(c_21,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2059,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_367,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_368,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_1635,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_368])).

cnf(c_1841,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1635,c_32,c_368,c_1818])).

cnf(c_1842,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1841])).

cnf(c_4635,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4293,c_1842])).

cnf(c_4706,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4643,c_32,c_30,c_1818,c_1936,c_2058,c_2059,c_4635])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_357,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_33])).

cnf(c_358,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_1636,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_35,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_359,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_1819,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1818])).

cnf(c_1824,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1636,c_35,c_359,c_1819])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2188,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1824,c_1642])).

cnf(c_4713,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4706,c_2188])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_4726,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4713,c_5])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1654,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1656,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3254,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1654,c_1656])).

cnf(c_5133,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4726,c_3254])).

cnf(c_1639,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3943,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1637,c_1639])).

cnf(c_1638,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4308,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3943,c_1638])).

cnf(c_5273,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5133,c_4308])).

cnf(c_22,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1641,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3165,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1641])).

cnf(c_1807,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1809,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1807])).

cnf(c_16,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1808,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1811,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1808])).

cnf(c_3170,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3165,c_1809,c_1811])).

cnf(c_3657,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3170,c_3254])).

cnf(c_5289,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5273,c_3657])).

cnf(c_5441,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5289,c_1654])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:34:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.21/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.21/1.03  
% 2.21/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.21/1.03  
% 2.21/1.03  ------  iProver source info
% 2.21/1.03  
% 2.21/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.21/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.21/1.03  git: non_committed_changes: false
% 2.21/1.03  git: last_make_outside_of_git: false
% 2.21/1.03  
% 2.21/1.03  ------ 
% 2.21/1.03  
% 2.21/1.03  ------ Input Options
% 2.21/1.03  
% 2.21/1.03  --out_options                           all
% 2.21/1.03  --tptp_safe_out                         true
% 2.21/1.03  --problem_path                          ""
% 2.21/1.03  --include_path                          ""
% 2.21/1.03  --clausifier                            res/vclausify_rel
% 2.21/1.03  --clausifier_options                    --mode clausify
% 2.21/1.03  --stdin                                 false
% 2.21/1.03  --stats_out                             all
% 2.21/1.03  
% 2.21/1.03  ------ General Options
% 2.21/1.03  
% 2.21/1.03  --fof                                   false
% 2.21/1.03  --time_out_real                         305.
% 2.21/1.03  --time_out_virtual                      -1.
% 2.21/1.03  --symbol_type_check                     false
% 2.21/1.03  --clausify_out                          false
% 2.21/1.03  --sig_cnt_out                           false
% 2.21/1.03  --trig_cnt_out                          false
% 2.21/1.03  --trig_cnt_out_tolerance                1.
% 2.21/1.03  --trig_cnt_out_sk_spl                   false
% 2.21/1.03  --abstr_cl_out                          false
% 2.21/1.03  
% 2.21/1.03  ------ Global Options
% 2.21/1.03  
% 2.21/1.03  --schedule                              default
% 2.21/1.03  --add_important_lit                     false
% 2.21/1.03  --prop_solver_per_cl                    1000
% 2.21/1.03  --min_unsat_core                        false
% 2.21/1.03  --soft_assumptions                      false
% 2.21/1.03  --soft_lemma_size                       3
% 2.21/1.03  --prop_impl_unit_size                   0
% 2.21/1.03  --prop_impl_unit                        []
% 2.21/1.03  --share_sel_clauses                     true
% 2.21/1.03  --reset_solvers                         false
% 2.21/1.03  --bc_imp_inh                            [conj_cone]
% 2.21/1.03  --conj_cone_tolerance                   3.
% 2.21/1.03  --extra_neg_conj                        none
% 2.21/1.03  --large_theory_mode                     true
% 2.21/1.03  --prolific_symb_bound                   200
% 2.21/1.03  --lt_threshold                          2000
% 2.21/1.03  --clause_weak_htbl                      true
% 2.21/1.03  --gc_record_bc_elim                     false
% 2.21/1.03  
% 2.21/1.03  ------ Preprocessing Options
% 2.21/1.03  
% 2.21/1.03  --preprocessing_flag                    true
% 2.21/1.03  --time_out_prep_mult                    0.1
% 2.21/1.03  --splitting_mode                        input
% 2.21/1.03  --splitting_grd                         true
% 2.21/1.03  --splitting_cvd                         false
% 2.21/1.03  --splitting_cvd_svl                     false
% 2.21/1.03  --splitting_nvd                         32
% 2.21/1.03  --sub_typing                            true
% 2.21/1.03  --prep_gs_sim                           true
% 2.21/1.03  --prep_unflatten                        true
% 2.21/1.03  --prep_res_sim                          true
% 2.21/1.03  --prep_upred                            true
% 2.21/1.03  --prep_sem_filter                       exhaustive
% 2.21/1.03  --prep_sem_filter_out                   false
% 2.21/1.03  --pred_elim                             true
% 2.21/1.03  --res_sim_input                         true
% 2.21/1.03  --eq_ax_congr_red                       true
% 2.21/1.03  --pure_diseq_elim                       true
% 2.21/1.03  --brand_transform                       false
% 2.21/1.03  --non_eq_to_eq                          false
% 2.21/1.03  --prep_def_merge                        true
% 2.21/1.03  --prep_def_merge_prop_impl              false
% 2.21/1.03  --prep_def_merge_mbd                    true
% 2.21/1.03  --prep_def_merge_tr_red                 false
% 2.21/1.03  --prep_def_merge_tr_cl                  false
% 2.21/1.03  --smt_preprocessing                     true
% 2.21/1.03  --smt_ac_axioms                         fast
% 2.21/1.03  --preprocessed_out                      false
% 2.21/1.03  --preprocessed_stats                    false
% 2.21/1.03  
% 2.21/1.03  ------ Abstraction refinement Options
% 2.21/1.03  
% 2.21/1.03  --abstr_ref                             []
% 2.21/1.03  --abstr_ref_prep                        false
% 2.21/1.03  --abstr_ref_until_sat                   false
% 2.21/1.03  --abstr_ref_sig_restrict                funpre
% 2.21/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.03  --abstr_ref_under                       []
% 2.21/1.03  
% 2.21/1.03  ------ SAT Options
% 2.21/1.03  
% 2.21/1.03  --sat_mode                              false
% 2.21/1.03  --sat_fm_restart_options                ""
% 2.21/1.03  --sat_gr_def                            false
% 2.21/1.03  --sat_epr_types                         true
% 2.21/1.03  --sat_non_cyclic_types                  false
% 2.21/1.03  --sat_finite_models                     false
% 2.21/1.03  --sat_fm_lemmas                         false
% 2.21/1.03  --sat_fm_prep                           false
% 2.21/1.03  --sat_fm_uc_incr                        true
% 2.21/1.03  --sat_out_model                         small
% 2.21/1.03  --sat_out_clauses                       false
% 2.21/1.03  
% 2.21/1.03  ------ QBF Options
% 2.21/1.03  
% 2.21/1.03  --qbf_mode                              false
% 2.21/1.03  --qbf_elim_univ                         false
% 2.21/1.03  --qbf_dom_inst                          none
% 2.21/1.03  --qbf_dom_pre_inst                      false
% 2.21/1.03  --qbf_sk_in                             false
% 2.21/1.03  --qbf_pred_elim                         true
% 2.21/1.03  --qbf_split                             512
% 2.21/1.03  
% 2.21/1.03  ------ BMC1 Options
% 2.21/1.03  
% 2.21/1.03  --bmc1_incremental                      false
% 2.21/1.03  --bmc1_axioms                           reachable_all
% 2.21/1.03  --bmc1_min_bound                        0
% 2.21/1.03  --bmc1_max_bound                        -1
% 2.21/1.03  --bmc1_max_bound_default                -1
% 2.21/1.03  --bmc1_symbol_reachability              true
% 2.21/1.03  --bmc1_property_lemmas                  false
% 2.21/1.03  --bmc1_k_induction                      false
% 2.21/1.03  --bmc1_non_equiv_states                 false
% 2.21/1.03  --bmc1_deadlock                         false
% 2.21/1.03  --bmc1_ucm                              false
% 2.21/1.03  --bmc1_add_unsat_core                   none
% 2.21/1.03  --bmc1_unsat_core_children              false
% 2.21/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.03  --bmc1_out_stat                         full
% 2.21/1.03  --bmc1_ground_init                      false
% 2.21/1.03  --bmc1_pre_inst_next_state              false
% 2.21/1.03  --bmc1_pre_inst_state                   false
% 2.21/1.03  --bmc1_pre_inst_reach_state             false
% 2.21/1.03  --bmc1_out_unsat_core                   false
% 2.21/1.03  --bmc1_aig_witness_out                  false
% 2.21/1.03  --bmc1_verbose                          false
% 2.21/1.03  --bmc1_dump_clauses_tptp                false
% 2.21/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.03  --bmc1_dump_file                        -
% 2.21/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.03  --bmc1_ucm_extend_mode                  1
% 2.21/1.03  --bmc1_ucm_init_mode                    2
% 2.21/1.03  --bmc1_ucm_cone_mode                    none
% 2.21/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.03  --bmc1_ucm_relax_model                  4
% 2.21/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.03  --bmc1_ucm_layered_model                none
% 2.21/1.03  --bmc1_ucm_max_lemma_size               10
% 2.21/1.03  
% 2.21/1.03  ------ AIG Options
% 2.21/1.03  
% 2.21/1.03  --aig_mode                              false
% 2.21/1.03  
% 2.21/1.03  ------ Instantiation Options
% 2.21/1.03  
% 2.21/1.03  --instantiation_flag                    true
% 2.21/1.03  --inst_sos_flag                         false
% 2.21/1.03  --inst_sos_phase                        true
% 2.21/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.03  --inst_lit_sel_side                     num_symb
% 2.21/1.03  --inst_solver_per_active                1400
% 2.21/1.03  --inst_solver_calls_frac                1.
% 2.21/1.03  --inst_passive_queue_type               priority_queues
% 2.21/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.03  --inst_passive_queues_freq              [25;2]
% 2.21/1.03  --inst_dismatching                      true
% 2.21/1.03  --inst_eager_unprocessed_to_passive     true
% 2.21/1.03  --inst_prop_sim_given                   true
% 2.21/1.03  --inst_prop_sim_new                     false
% 2.21/1.03  --inst_subs_new                         false
% 2.21/1.03  --inst_eq_res_simp                      false
% 2.21/1.03  --inst_subs_given                       false
% 2.21/1.03  --inst_orphan_elimination               true
% 2.21/1.03  --inst_learning_loop_flag               true
% 2.21/1.03  --inst_learning_start                   3000
% 2.21/1.03  --inst_learning_factor                  2
% 2.21/1.03  --inst_start_prop_sim_after_learn       3
% 2.21/1.03  --inst_sel_renew                        solver
% 2.21/1.03  --inst_lit_activity_flag                true
% 2.21/1.03  --inst_restr_to_given                   false
% 2.21/1.03  --inst_activity_threshold               500
% 2.21/1.03  --inst_out_proof                        true
% 2.21/1.03  
% 2.21/1.03  ------ Resolution Options
% 2.21/1.03  
% 2.21/1.03  --resolution_flag                       true
% 2.21/1.03  --res_lit_sel                           adaptive
% 2.21/1.03  --res_lit_sel_side                      none
% 2.21/1.03  --res_ordering                          kbo
% 2.21/1.03  --res_to_prop_solver                    active
% 2.21/1.03  --res_prop_simpl_new                    false
% 2.21/1.03  --res_prop_simpl_given                  true
% 2.21/1.03  --res_passive_queue_type                priority_queues
% 2.21/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.03  --res_passive_queues_freq               [15;5]
% 2.21/1.03  --res_forward_subs                      full
% 2.21/1.03  --res_backward_subs                     full
% 2.21/1.03  --res_forward_subs_resolution           true
% 2.21/1.03  --res_backward_subs_resolution          true
% 2.21/1.03  --res_orphan_elimination                true
% 2.21/1.03  --res_time_limit                        2.
% 2.21/1.03  --res_out_proof                         true
% 2.21/1.03  
% 2.21/1.03  ------ Superposition Options
% 2.21/1.03  
% 2.21/1.03  --superposition_flag                    true
% 2.21/1.03  --sup_passive_queue_type                priority_queues
% 2.21/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.03  --demod_completeness_check              fast
% 2.21/1.03  --demod_use_ground                      true
% 2.21/1.03  --sup_to_prop_solver                    passive
% 2.21/1.03  --sup_prop_simpl_new                    true
% 2.21/1.03  --sup_prop_simpl_given                  true
% 2.21/1.03  --sup_fun_splitting                     false
% 2.21/1.03  --sup_smt_interval                      50000
% 2.21/1.03  
% 2.21/1.03  ------ Superposition Simplification Setup
% 2.21/1.03  
% 2.21/1.03  --sup_indices_passive                   []
% 2.21/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.03  --sup_full_bw                           [BwDemod]
% 2.21/1.03  --sup_immed_triv                        [TrivRules]
% 2.21/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.03  --sup_immed_bw_main                     []
% 2.21/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.04  
% 2.21/1.04  ------ Combination Options
% 2.21/1.04  
% 2.21/1.04  --comb_res_mult                         3
% 2.21/1.04  --comb_sup_mult                         2
% 2.21/1.04  --comb_inst_mult                        10
% 2.21/1.04  
% 2.21/1.04  ------ Debug Options
% 2.21/1.04  
% 2.21/1.04  --dbg_backtrace                         false
% 2.21/1.04  --dbg_dump_prop_clauses                 false
% 2.21/1.04  --dbg_dump_prop_clauses_file            -
% 2.21/1.04  --dbg_out_stat                          false
% 2.21/1.04  ------ Parsing...
% 2.21/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.21/1.04  
% 2.21/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.21/1.04  
% 2.21/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.21/1.04  
% 2.21/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.21/1.04  ------ Proving...
% 2.21/1.04  ------ Problem Properties 
% 2.21/1.04  
% 2.21/1.04  
% 2.21/1.04  clauses                                 29
% 2.21/1.04  conjectures                             3
% 2.21/1.04  EPR                                     4
% 2.21/1.04  Horn                                    27
% 2.21/1.04  unary                                   18
% 2.21/1.04  binary                                  7
% 2.21/1.04  lits                                    50
% 2.21/1.04  lits eq                                 20
% 2.21/1.04  fd_pure                                 0
% 2.21/1.04  fd_pseudo                               0
% 2.21/1.04  fd_cond                                 1
% 2.21/1.04  fd_pseudo_cond                          2
% 2.21/1.04  AC symbols                              0
% 2.21/1.04  
% 2.21/1.04  ------ Schedule dynamic 5 is on 
% 2.21/1.04  
% 2.21/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.21/1.04  
% 2.21/1.04  
% 2.21/1.04  ------ 
% 2.21/1.04  Current options:
% 2.21/1.04  ------ 
% 2.21/1.04  
% 2.21/1.04  ------ Input Options
% 2.21/1.04  
% 2.21/1.04  --out_options                           all
% 2.21/1.04  --tptp_safe_out                         true
% 2.21/1.04  --problem_path                          ""
% 2.21/1.04  --include_path                          ""
% 2.21/1.04  --clausifier                            res/vclausify_rel
% 2.21/1.04  --clausifier_options                    --mode clausify
% 2.21/1.04  --stdin                                 false
% 2.21/1.04  --stats_out                             all
% 2.21/1.04  
% 2.21/1.04  ------ General Options
% 2.21/1.04  
% 2.21/1.04  --fof                                   false
% 2.21/1.04  --time_out_real                         305.
% 2.21/1.04  --time_out_virtual                      -1.
% 2.21/1.04  --symbol_type_check                     false
% 2.21/1.04  --clausify_out                          false
% 2.21/1.04  --sig_cnt_out                           false
% 2.21/1.04  --trig_cnt_out                          false
% 2.21/1.04  --trig_cnt_out_tolerance                1.
% 2.21/1.04  --trig_cnt_out_sk_spl                   false
% 2.21/1.04  --abstr_cl_out                          false
% 2.21/1.04  
% 2.21/1.04  ------ Global Options
% 2.21/1.04  
% 2.21/1.04  --schedule                              default
% 2.21/1.04  --add_important_lit                     false
% 2.21/1.04  --prop_solver_per_cl                    1000
% 2.21/1.04  --min_unsat_core                        false
% 2.21/1.04  --soft_assumptions                      false
% 2.21/1.04  --soft_lemma_size                       3
% 2.21/1.04  --prop_impl_unit_size                   0
% 2.21/1.04  --prop_impl_unit                        []
% 2.21/1.04  --share_sel_clauses                     true
% 2.21/1.04  --reset_solvers                         false
% 2.21/1.04  --bc_imp_inh                            [conj_cone]
% 2.21/1.04  --conj_cone_tolerance                   3.
% 2.21/1.04  --extra_neg_conj                        none
% 2.21/1.04  --large_theory_mode                     true
% 2.21/1.04  --prolific_symb_bound                   200
% 2.21/1.04  --lt_threshold                          2000
% 2.21/1.04  --clause_weak_htbl                      true
% 2.21/1.04  --gc_record_bc_elim                     false
% 2.21/1.04  
% 2.21/1.04  ------ Preprocessing Options
% 2.21/1.04  
% 2.21/1.04  --preprocessing_flag                    true
% 2.21/1.04  --time_out_prep_mult                    0.1
% 2.21/1.04  --splitting_mode                        input
% 2.21/1.04  --splitting_grd                         true
% 2.21/1.04  --splitting_cvd                         false
% 2.21/1.04  --splitting_cvd_svl                     false
% 2.21/1.04  --splitting_nvd                         32
% 2.21/1.04  --sub_typing                            true
% 2.21/1.04  --prep_gs_sim                           true
% 2.21/1.04  --prep_unflatten                        true
% 2.21/1.04  --prep_res_sim                          true
% 2.21/1.04  --prep_upred                            true
% 2.21/1.04  --prep_sem_filter                       exhaustive
% 2.21/1.04  --prep_sem_filter_out                   false
% 2.21/1.04  --pred_elim                             true
% 2.21/1.04  --res_sim_input                         true
% 2.21/1.04  --eq_ax_congr_red                       true
% 2.21/1.04  --pure_diseq_elim                       true
% 2.21/1.04  --brand_transform                       false
% 2.21/1.04  --non_eq_to_eq                          false
% 2.21/1.04  --prep_def_merge                        true
% 2.21/1.04  --prep_def_merge_prop_impl              false
% 2.21/1.04  --prep_def_merge_mbd                    true
% 2.21/1.04  --prep_def_merge_tr_red                 false
% 2.21/1.04  --prep_def_merge_tr_cl                  false
% 2.21/1.04  --smt_preprocessing                     true
% 2.21/1.04  --smt_ac_axioms                         fast
% 2.21/1.04  --preprocessed_out                      false
% 2.21/1.04  --preprocessed_stats                    false
% 2.21/1.04  
% 2.21/1.04  ------ Abstraction refinement Options
% 2.21/1.04  
% 2.21/1.04  --abstr_ref                             []
% 2.21/1.04  --abstr_ref_prep                        false
% 2.21/1.04  --abstr_ref_until_sat                   false
% 2.21/1.04  --abstr_ref_sig_restrict                funpre
% 2.21/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.21/1.04  --abstr_ref_under                       []
% 2.21/1.04  
% 2.21/1.04  ------ SAT Options
% 2.21/1.04  
% 2.21/1.04  --sat_mode                              false
% 2.21/1.04  --sat_fm_restart_options                ""
% 2.21/1.04  --sat_gr_def                            false
% 2.21/1.04  --sat_epr_types                         true
% 2.21/1.04  --sat_non_cyclic_types                  false
% 2.21/1.04  --sat_finite_models                     false
% 2.21/1.04  --sat_fm_lemmas                         false
% 2.21/1.04  --sat_fm_prep                           false
% 2.21/1.04  --sat_fm_uc_incr                        true
% 2.21/1.04  --sat_out_model                         small
% 2.21/1.04  --sat_out_clauses                       false
% 2.21/1.04  
% 2.21/1.04  ------ QBF Options
% 2.21/1.04  
% 2.21/1.04  --qbf_mode                              false
% 2.21/1.04  --qbf_elim_univ                         false
% 2.21/1.04  --qbf_dom_inst                          none
% 2.21/1.04  --qbf_dom_pre_inst                      false
% 2.21/1.04  --qbf_sk_in                             false
% 2.21/1.04  --qbf_pred_elim                         true
% 2.21/1.04  --qbf_split                             512
% 2.21/1.04  
% 2.21/1.04  ------ BMC1 Options
% 2.21/1.04  
% 2.21/1.04  --bmc1_incremental                      false
% 2.21/1.04  --bmc1_axioms                           reachable_all
% 2.21/1.04  --bmc1_min_bound                        0
% 2.21/1.04  --bmc1_max_bound                        -1
% 2.21/1.04  --bmc1_max_bound_default                -1
% 2.21/1.04  --bmc1_symbol_reachability              true
% 2.21/1.04  --bmc1_property_lemmas                  false
% 2.21/1.04  --bmc1_k_induction                      false
% 2.21/1.04  --bmc1_non_equiv_states                 false
% 2.21/1.04  --bmc1_deadlock                         false
% 2.21/1.04  --bmc1_ucm                              false
% 2.21/1.04  --bmc1_add_unsat_core                   none
% 2.21/1.04  --bmc1_unsat_core_children              false
% 2.21/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.21/1.04  --bmc1_out_stat                         full
% 2.21/1.04  --bmc1_ground_init                      false
% 2.21/1.04  --bmc1_pre_inst_next_state              false
% 2.21/1.04  --bmc1_pre_inst_state                   false
% 2.21/1.04  --bmc1_pre_inst_reach_state             false
% 2.21/1.04  --bmc1_out_unsat_core                   false
% 2.21/1.04  --bmc1_aig_witness_out                  false
% 2.21/1.04  --bmc1_verbose                          false
% 2.21/1.04  --bmc1_dump_clauses_tptp                false
% 2.21/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.21/1.04  --bmc1_dump_file                        -
% 2.21/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.21/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.21/1.04  --bmc1_ucm_extend_mode                  1
% 2.21/1.04  --bmc1_ucm_init_mode                    2
% 2.21/1.04  --bmc1_ucm_cone_mode                    none
% 2.21/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.21/1.04  --bmc1_ucm_relax_model                  4
% 2.21/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.21/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.21/1.04  --bmc1_ucm_layered_model                none
% 2.21/1.04  --bmc1_ucm_max_lemma_size               10
% 2.21/1.04  
% 2.21/1.04  ------ AIG Options
% 2.21/1.04  
% 2.21/1.04  --aig_mode                              false
% 2.21/1.04  
% 2.21/1.04  ------ Instantiation Options
% 2.21/1.04  
% 2.21/1.04  --instantiation_flag                    true
% 2.21/1.04  --inst_sos_flag                         false
% 2.21/1.04  --inst_sos_phase                        true
% 2.21/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.21/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.21/1.04  --inst_lit_sel_side                     none
% 2.21/1.04  --inst_solver_per_active                1400
% 2.21/1.04  --inst_solver_calls_frac                1.
% 2.21/1.04  --inst_passive_queue_type               priority_queues
% 2.21/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.21/1.04  --inst_passive_queues_freq              [25;2]
% 2.21/1.04  --inst_dismatching                      true
% 2.21/1.04  --inst_eager_unprocessed_to_passive     true
% 2.21/1.04  --inst_prop_sim_given                   true
% 2.21/1.04  --inst_prop_sim_new                     false
% 2.21/1.04  --inst_subs_new                         false
% 2.21/1.04  --inst_eq_res_simp                      false
% 2.21/1.04  --inst_subs_given                       false
% 2.21/1.04  --inst_orphan_elimination               true
% 2.21/1.04  --inst_learning_loop_flag               true
% 2.21/1.04  --inst_learning_start                   3000
% 2.21/1.04  --inst_learning_factor                  2
% 2.21/1.04  --inst_start_prop_sim_after_learn       3
% 2.21/1.04  --inst_sel_renew                        solver
% 2.21/1.04  --inst_lit_activity_flag                true
% 2.21/1.04  --inst_restr_to_given                   false
% 2.21/1.04  --inst_activity_threshold               500
% 2.21/1.04  --inst_out_proof                        true
% 2.21/1.04  
% 2.21/1.04  ------ Resolution Options
% 2.21/1.04  
% 2.21/1.04  --resolution_flag                       false
% 2.21/1.04  --res_lit_sel                           adaptive
% 2.21/1.04  --res_lit_sel_side                      none
% 2.21/1.04  --res_ordering                          kbo
% 2.21/1.04  --res_to_prop_solver                    active
% 2.21/1.04  --res_prop_simpl_new                    false
% 2.21/1.04  --res_prop_simpl_given                  true
% 2.21/1.04  --res_passive_queue_type                priority_queues
% 2.21/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.21/1.04  --res_passive_queues_freq               [15;5]
% 2.21/1.04  --res_forward_subs                      full
% 2.21/1.04  --res_backward_subs                     full
% 2.21/1.04  --res_forward_subs_resolution           true
% 2.21/1.04  --res_backward_subs_resolution          true
% 2.21/1.04  --res_orphan_elimination                true
% 2.21/1.04  --res_time_limit                        2.
% 2.21/1.04  --res_out_proof                         true
% 2.21/1.04  
% 2.21/1.04  ------ Superposition Options
% 2.21/1.04  
% 2.21/1.04  --superposition_flag                    true
% 2.21/1.04  --sup_passive_queue_type                priority_queues
% 2.21/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.21/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.21/1.04  --demod_completeness_check              fast
% 2.21/1.04  --demod_use_ground                      true
% 2.21/1.04  --sup_to_prop_solver                    passive
% 2.21/1.04  --sup_prop_simpl_new                    true
% 2.21/1.04  --sup_prop_simpl_given                  true
% 2.21/1.04  --sup_fun_splitting                     false
% 2.21/1.04  --sup_smt_interval                      50000
% 2.21/1.04  
% 2.21/1.04  ------ Superposition Simplification Setup
% 2.21/1.04  
% 2.21/1.04  --sup_indices_passive                   []
% 2.21/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.21/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.21/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.04  --sup_full_bw                           [BwDemod]
% 2.21/1.04  --sup_immed_triv                        [TrivRules]
% 2.21/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.21/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.04  --sup_immed_bw_main                     []
% 2.21/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.21/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.21/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.21/1.04  
% 2.21/1.04  ------ Combination Options
% 2.21/1.04  
% 2.21/1.04  --comb_res_mult                         3
% 2.21/1.04  --comb_sup_mult                         2
% 2.21/1.04  --comb_inst_mult                        10
% 2.21/1.04  
% 2.21/1.04  ------ Debug Options
% 2.21/1.04  
% 2.21/1.04  --dbg_backtrace                         false
% 2.21/1.04  --dbg_dump_prop_clauses                 false
% 2.21/1.04  --dbg_dump_prop_clauses_file            -
% 2.21/1.04  --dbg_out_stat                          false
% 2.21/1.04  
% 2.21/1.04  
% 2.21/1.04  
% 2.21/1.04  
% 2.21/1.04  ------ Proving...
% 2.21/1.04  
% 2.21/1.04  
% 2.21/1.04  % SZS status Theorem for theBenchmark.p
% 2.21/1.04  
% 2.21/1.04   Resolution empty clause
% 2.21/1.04  
% 2.21/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 2.21/1.04  
% 2.21/1.04  fof(f19,conjecture,(
% 2.21/1.04    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f20,negated_conjecture,(
% 2.21/1.04    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.21/1.04    inference(negated_conjecture,[],[f19])).
% 2.21/1.04  
% 2.21/1.04  fof(f21,plain,(
% 2.21/1.04    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.21/1.04    inference(pure_predicate_removal,[],[f20])).
% 2.21/1.04  
% 2.21/1.04  fof(f35,plain,(
% 2.21/1.04    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.21/1.04    inference(ennf_transformation,[],[f21])).
% 2.21/1.04  
% 2.21/1.04  fof(f36,plain,(
% 2.21/1.04    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.21/1.04    inference(flattening,[],[f35])).
% 2.21/1.04  
% 2.21/1.04  fof(f45,plain,(
% 2.21/1.04    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.21/1.04    introduced(choice_axiom,[])).
% 2.21/1.04  
% 2.21/1.04  fof(f46,plain,(
% 2.21/1.04    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.21/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f45])).
% 2.21/1.04  
% 2.21/1.04  fof(f81,plain,(
% 2.21/1.04    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.21/1.04    inference(cnf_transformation,[],[f46])).
% 2.21/1.04  
% 2.21/1.04  fof(f3,axiom,(
% 2.21/1.04    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f51,plain,(
% 2.21/1.04    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.21/1.04    inference(cnf_transformation,[],[f3])).
% 2.21/1.04  
% 2.21/1.04  fof(f4,axiom,(
% 2.21/1.04    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f52,plain,(
% 2.21/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.21/1.04    inference(cnf_transformation,[],[f4])).
% 2.21/1.04  
% 2.21/1.04  fof(f5,axiom,(
% 2.21/1.04    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f53,plain,(
% 2.21/1.04    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.21/1.04    inference(cnf_transformation,[],[f5])).
% 2.21/1.04  
% 2.21/1.04  fof(f84,plain,(
% 2.21/1.04    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.21/1.04    inference(definition_unfolding,[],[f52,f53])).
% 2.21/1.04  
% 2.21/1.04  fof(f85,plain,(
% 2.21/1.04    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.21/1.04    inference(definition_unfolding,[],[f51,f84])).
% 2.21/1.04  
% 2.21/1.04  fof(f97,plain,(
% 2.21/1.04    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.21/1.04    inference(definition_unfolding,[],[f81,f85])).
% 2.21/1.04  
% 2.21/1.04  fof(f16,axiom,(
% 2.21/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f23,plain,(
% 2.21/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.21/1.04    inference(pure_predicate_removal,[],[f16])).
% 2.21/1.04  
% 2.21/1.04  fof(f31,plain,(
% 2.21/1.04    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.04    inference(ennf_transformation,[],[f23])).
% 2.21/1.04  
% 2.21/1.04  fof(f76,plain,(
% 2.21/1.04    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.04    inference(cnf_transformation,[],[f31])).
% 2.21/1.04  
% 2.21/1.04  fof(f11,axiom,(
% 2.21/1.04    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f26,plain,(
% 2.21/1.04    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.21/1.04    inference(ennf_transformation,[],[f11])).
% 2.21/1.04  
% 2.21/1.04  fof(f44,plain,(
% 2.21/1.04    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.21/1.04    inference(nnf_transformation,[],[f26])).
% 2.21/1.04  
% 2.21/1.04  fof(f69,plain,(
% 2.21/1.04    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.21/1.04    inference(cnf_transformation,[],[f44])).
% 2.21/1.04  
% 2.21/1.04  fof(f15,axiom,(
% 2.21/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f30,plain,(
% 2.21/1.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.04    inference(ennf_transformation,[],[f15])).
% 2.21/1.04  
% 2.21/1.04  fof(f75,plain,(
% 2.21/1.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.04    inference(cnf_transformation,[],[f30])).
% 2.21/1.04  
% 2.21/1.04  fof(f7,axiom,(
% 2.21/1.04    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f25,plain,(
% 2.21/1.04    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.21/1.04    inference(ennf_transformation,[],[f7])).
% 2.21/1.04  
% 2.21/1.04  fof(f41,plain,(
% 2.21/1.04    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.21/1.04    inference(nnf_transformation,[],[f25])).
% 2.21/1.04  
% 2.21/1.04  fof(f42,plain,(
% 2.21/1.04    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.21/1.04    inference(flattening,[],[f41])).
% 2.21/1.04  
% 2.21/1.04  fof(f57,plain,(
% 2.21/1.04    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.21/1.04    inference(cnf_transformation,[],[f42])).
% 2.21/1.04  
% 2.21/1.04  fof(f94,plain,(
% 2.21/1.04    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 2.21/1.04    inference(definition_unfolding,[],[f57,f53,f84,f84,f84,f85,f85,f85,f53])).
% 2.21/1.04  
% 2.21/1.04  fof(f83,plain,(
% 2.21/1.04    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.21/1.04    inference(cnf_transformation,[],[f46])).
% 2.21/1.04  
% 2.21/1.04  fof(f96,plain,(
% 2.21/1.04    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.21/1.04    inference(definition_unfolding,[],[f83,f85,f85])).
% 2.21/1.04  
% 2.21/1.04  fof(f17,axiom,(
% 2.21/1.04    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f32,plain,(
% 2.21/1.04    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/1.04    inference(ennf_transformation,[],[f17])).
% 2.21/1.04  
% 2.21/1.04  fof(f77,plain,(
% 2.21/1.04    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.21/1.04    inference(cnf_transformation,[],[f32])).
% 2.21/1.04  
% 2.21/1.04  fof(f12,axiom,(
% 2.21/1.04    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f27,plain,(
% 2.21/1.04    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.21/1.04    inference(ennf_transformation,[],[f12])).
% 2.21/1.04  
% 2.21/1.04  fof(f71,plain,(
% 2.21/1.04    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.21/1.04    inference(cnf_transformation,[],[f27])).
% 2.21/1.04  
% 2.21/1.04  fof(f14,axiom,(
% 2.21/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f28,plain,(
% 2.21/1.04    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.21/1.04    inference(ennf_transformation,[],[f14])).
% 2.21/1.04  
% 2.21/1.04  fof(f29,plain,(
% 2.21/1.04    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.21/1.04    inference(flattening,[],[f28])).
% 2.21/1.04  
% 2.21/1.04  fof(f74,plain,(
% 2.21/1.04    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.21/1.04    inference(cnf_transformation,[],[f29])).
% 2.21/1.04  
% 2.21/1.04  fof(f95,plain,(
% 2.21/1.04    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.21/1.04    inference(definition_unfolding,[],[f74,f85,f85])).
% 2.21/1.04  
% 2.21/1.04  fof(f80,plain,(
% 2.21/1.04    v1_funct_1(sK3)),
% 2.21/1.04    inference(cnf_transformation,[],[f46])).
% 2.21/1.04  
% 2.21/1.04  fof(f18,axiom,(
% 2.21/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f22,plain,(
% 2.21/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 2.21/1.04    inference(pure_predicate_removal,[],[f18])).
% 2.21/1.04  
% 2.21/1.04  fof(f33,plain,(
% 2.21/1.04    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.21/1.04    inference(ennf_transformation,[],[f22])).
% 2.21/1.04  
% 2.21/1.04  fof(f34,plain,(
% 2.21/1.04    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/1.04    inference(flattening,[],[f33])).
% 2.21/1.04  
% 2.21/1.04  fof(f79,plain,(
% 2.21/1.04    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.21/1.04    inference(cnf_transformation,[],[f34])).
% 2.21/1.04  
% 2.21/1.04  fof(f9,axiom,(
% 2.21/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f43,plain,(
% 2.21/1.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.21/1.04    inference(nnf_transformation,[],[f9])).
% 2.21/1.04  
% 2.21/1.04  fof(f67,plain,(
% 2.21/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.21/1.04    inference(cnf_transformation,[],[f43])).
% 2.21/1.04  
% 2.21/1.04  fof(f6,axiom,(
% 2.21/1.04    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f39,plain,(
% 2.21/1.04    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.21/1.04    inference(nnf_transformation,[],[f6])).
% 2.21/1.04  
% 2.21/1.04  fof(f40,plain,(
% 2.21/1.04    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.21/1.04    inference(flattening,[],[f39])).
% 2.21/1.04  
% 2.21/1.04  fof(f55,plain,(
% 2.21/1.04    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.21/1.04    inference(cnf_transformation,[],[f40])).
% 2.21/1.04  
% 2.21/1.04  fof(f101,plain,(
% 2.21/1.04    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.21/1.04    inference(equality_resolution,[],[f55])).
% 2.21/1.04  
% 2.21/1.04  fof(f2,axiom,(
% 2.21/1.04    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f50,plain,(
% 2.21/1.04    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.21/1.04    inference(cnf_transformation,[],[f2])).
% 2.21/1.04  
% 2.21/1.04  fof(f1,axiom,(
% 2.21/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f37,plain,(
% 2.21/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/1.04    inference(nnf_transformation,[],[f1])).
% 2.21/1.04  
% 2.21/1.04  fof(f38,plain,(
% 2.21/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.21/1.04    inference(flattening,[],[f37])).
% 2.21/1.04  
% 2.21/1.04  fof(f49,plain,(
% 2.21/1.04    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.21/1.04    inference(cnf_transformation,[],[f38])).
% 2.21/1.04  
% 2.21/1.04  fof(f13,axiom,(
% 2.21/1.04    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f73,plain,(
% 2.21/1.04    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.21/1.04    inference(cnf_transformation,[],[f13])).
% 2.21/1.04  
% 2.21/1.04  fof(f8,axiom,(
% 2.21/1.04    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.21/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.21/1.04  
% 2.21/1.04  fof(f66,plain,(
% 2.21/1.04    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.21/1.04    inference(cnf_transformation,[],[f8])).
% 2.21/1.04  
% 2.21/1.04  cnf(c_32,negated_conjecture,
% 2.21/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.21/1.04      inference(cnf_transformation,[],[f97]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1637,plain,
% 2.21/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_26,plain,
% 2.21/1.04      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.21/1.04      inference(cnf_transformation,[],[f76]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_20,plain,
% 2.21/1.04      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.21/1.04      inference(cnf_transformation,[],[f69]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_389,plain,
% 2.21/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.04      | r1_tarski(k1_relat_1(X0),X1)
% 2.21/1.04      | ~ v1_relat_1(X0) ),
% 2.21/1.04      inference(resolution,[status(thm)],[c_26,c_20]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_25,plain,
% 2.21/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.21/1.04      inference(cnf_transformation,[],[f75]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_393,plain,
% 2.21/1.04      ( r1_tarski(k1_relat_1(X0),X1)
% 2.21/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.21/1.04      inference(global_propositional_subsumption,[status(thm)],[c_389,c_25]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_394,plain,
% 2.21/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.04      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.21/1.04      inference(renaming,[status(thm)],[c_393]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1634,plain,
% 2.21/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.21/1.04      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1897,plain,
% 2.21/1.04      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 2.21/1.04      inference(superposition,[status(thm)],[c_1637,c_1634]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_15,plain,
% 2.21/1.04      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 2.21/1.04      | k2_enumset1(X1,X1,X2,X3) = X0
% 2.21/1.04      | k2_enumset1(X1,X1,X1,X3) = X0
% 2.21/1.04      | k2_enumset1(X2,X2,X2,X3) = X0
% 2.21/1.04      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.21/1.04      | k2_enumset1(X3,X3,X3,X3) = X0
% 2.21/1.04      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.21/1.04      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.21/1.04      | k1_xboole_0 = X0 ),
% 2.21/1.04      inference(cnf_transformation,[],[f94]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1645,plain,
% 2.21/1.04      ( k2_enumset1(X0,X0,X1,X2) = X3
% 2.21/1.04      | k2_enumset1(X0,X0,X0,X2) = X3
% 2.21/1.04      | k2_enumset1(X1,X1,X1,X2) = X3
% 2.21/1.04      | k2_enumset1(X0,X0,X0,X1) = X3
% 2.21/1.04      | k2_enumset1(X2,X2,X2,X2) = X3
% 2.21/1.04      | k2_enumset1(X1,X1,X1,X1) = X3
% 2.21/1.04      | k2_enumset1(X0,X0,X0,X0) = X3
% 2.21/1.04      | k1_xboole_0 = X3
% 2.21/1.04      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_4293,plain,
% 2.21/1.04      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.21/1.04      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.21/1.04      inference(superposition,[status(thm)],[c_1897,c_1645]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_4643,plain,
% 2.21/1.04      ( k1_relat_1(sK3) = k1_xboole_0
% 2.21/1.04      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 2.21/1.04      inference(superposition,[status(thm)],[c_4293,c_1637]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_30,negated_conjecture,
% 2.21/1.04      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.21/1.04      inference(cnf_transformation,[],[f96]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1818,plain,
% 2.21/1.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.21/1.04      | v1_relat_1(sK3) ),
% 2.21/1.04      inference(instantiation,[status(thm)],[c_25]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_27,plain,
% 2.21/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.21/1.04      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.21/1.04      inference(cnf_transformation,[],[f77]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1864,plain,
% 2.21/1.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.21/1.04      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.21/1.04      inference(instantiation,[status(thm)],[c_27]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1936,plain,
% 2.21/1.04      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.21/1.04      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 2.21/1.04      inference(instantiation,[status(thm)],[c_1864]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1092,plain,
% 2.21/1.04      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.21/1.04      theory(equality) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1847,plain,
% 2.21/1.04      ( ~ r1_tarski(X0,X1)
% 2.21/1.04      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.21/1.04      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 2.21/1.04      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 2.21/1.04      inference(instantiation,[status(thm)],[c_1092]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1935,plain,
% 2.21/1.04      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.21/1.04      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 2.21/1.04      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.21/1.04      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 2.21/1.04      inference(instantiation,[status(thm)],[c_1847]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_2058,plain,
% 2.21/1.04      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.21/1.04      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.21/1.04      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.21/1.04      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 2.21/1.04      inference(instantiation,[status(thm)],[c_1935]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_21,plain,
% 2.21/1.04      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.21/1.04      inference(cnf_transformation,[],[f71]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_2059,plain,
% 2.21/1.04      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.21/1.04      inference(instantiation,[status(thm)],[c_21]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_24,plain,
% 2.21/1.04      ( ~ v1_funct_1(X0)
% 2.21/1.04      | ~ v1_relat_1(X0)
% 2.21/1.04      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.21/1.04      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.21/1.04      inference(cnf_transformation,[],[f95]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_33,negated_conjecture,
% 2.21/1.04      ( v1_funct_1(sK3) ),
% 2.21/1.04      inference(cnf_transformation,[],[f80]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_367,plain,
% 2.21/1.04      ( ~ v1_relat_1(X0)
% 2.21/1.04      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.21/1.04      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.21/1.04      | sK3 != X0 ),
% 2.21/1.04      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_368,plain,
% 2.21/1.04      ( ~ v1_relat_1(sK3)
% 2.21/1.04      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.21/1.04      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.21/1.04      inference(unflattening,[status(thm)],[c_367]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1635,plain,
% 2.21/1.04      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.21/1.04      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.21/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_368]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1841,plain,
% 2.21/1.04      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.21/1.04      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 2.21/1.04      inference(global_propositional_subsumption,
% 2.21/1.04                [status(thm)],
% 2.21/1.04                [c_1635,c_32,c_368,c_1818]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1842,plain,
% 2.21/1.04      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.21/1.04      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.21/1.04      inference(renaming,[status(thm)],[c_1841]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_4635,plain,
% 2.21/1.04      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.21/1.04      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.21/1.04      inference(superposition,[status(thm)],[c_4293,c_1842]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_4706,plain,
% 2.21/1.04      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.21/1.04      inference(global_propositional_subsumption,
% 2.21/1.04                [status(thm)],
% 2.21/1.04                [c_4643,c_32,c_30,c_1818,c_1936,c_2058,c_2059,c_4635]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_28,plain,
% 2.21/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.21/1.04      | ~ v1_funct_1(X0)
% 2.21/1.04      | ~ v1_relat_1(X0) ),
% 2.21/1.04      inference(cnf_transformation,[],[f79]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_357,plain,
% 2.21/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.21/1.04      | ~ v1_relat_1(X0)
% 2.21/1.04      | sK3 != X0 ),
% 2.21/1.04      inference(resolution_lifted,[status(thm)],[c_28,c_33]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_358,plain,
% 2.21/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
% 2.21/1.04      | ~ v1_relat_1(sK3) ),
% 2.21/1.04      inference(unflattening,[status(thm)],[c_357]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1636,plain,
% 2.21/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
% 2.21/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_35,plain,
% 2.21/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_359,plain,
% 2.21/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
% 2.21/1.04      | v1_relat_1(sK3) != iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1819,plain,
% 2.21/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 2.21/1.04      | v1_relat_1(sK3) = iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_1818]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1824,plain,
% 2.21/1.04      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top ),
% 2.21/1.04      inference(global_propositional_subsumption,
% 2.21/1.04                [status(thm)],
% 2.21/1.04                [c_1636,c_35,c_359,c_1819]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_18,plain,
% 2.21/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.21/1.04      inference(cnf_transformation,[],[f67]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1642,plain,
% 2.21/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.21/1.04      | r1_tarski(X0,X1) = iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_2188,plain,
% 2.21/1.04      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) = iProver_top ),
% 2.21/1.04      inference(superposition,[status(thm)],[c_1824,c_1642]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_4713,plain,
% 2.21/1.04      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) = iProver_top ),
% 2.21/1.04      inference(demodulation,[status(thm)],[c_4706,c_2188]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_5,plain,
% 2.21/1.04      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.21/1.04      inference(cnf_transformation,[],[f101]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_4726,plain,
% 2.21/1.04      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 2.21/1.04      inference(demodulation,[status(thm)],[c_4713,c_5]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_3,plain,
% 2.21/1.04      ( r1_tarski(k1_xboole_0,X0) ),
% 2.21/1.04      inference(cnf_transformation,[],[f50]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1654,plain,
% 2.21/1.04      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_0,plain,
% 2.21/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.21/1.04      inference(cnf_transformation,[],[f49]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1656,plain,
% 2.21/1.04      ( X0 = X1
% 2.21/1.04      | r1_tarski(X0,X1) != iProver_top
% 2.21/1.04      | r1_tarski(X1,X0) != iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_3254,plain,
% 2.21/1.04      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.21/1.04      inference(superposition,[status(thm)],[c_1654,c_1656]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_5133,plain,
% 2.21/1.04      ( sK3 = k1_xboole_0 ),
% 2.21/1.04      inference(superposition,[status(thm)],[c_4726,c_3254]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1639,plain,
% 2.21/1.04      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.21/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_3943,plain,
% 2.21/1.04      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.21/1.04      inference(superposition,[status(thm)],[c_1637,c_1639]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1638,plain,
% 2.21/1.04      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_4308,plain,
% 2.21/1.04      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.21/1.04      inference(demodulation,[status(thm)],[c_3943,c_1638]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_5273,plain,
% 2.21/1.04      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.21/1.04      inference(demodulation,[status(thm)],[c_5133,c_4308]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_22,plain,
% 2.21/1.04      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.21/1.04      inference(cnf_transformation,[],[f73]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1641,plain,
% 2.21/1.04      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 2.21/1.04      | v1_relat_1(X0) != iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_3165,plain,
% 2.21/1.04      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 2.21/1.04      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.21/1.04      inference(superposition,[status(thm)],[c_22,c_1641]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1807,plain,
% 2.21/1.04      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.21/1.04      | v1_relat_1(k1_xboole_0) ),
% 2.21/1.04      inference(instantiation,[status(thm)],[c_25]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1809,plain,
% 2.21/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.21/1.04      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_1807]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_16,plain,
% 2.21/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.21/1.04      inference(cnf_transformation,[],[f66]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1808,plain,
% 2.21/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.21/1.04      inference(instantiation,[status(thm)],[c_16]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_1811,plain,
% 2.21/1.04      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.21/1.04      inference(predicate_to_equality,[status(thm)],[c_1808]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_3170,plain,
% 2.21/1.04      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 2.21/1.04      inference(global_propositional_subsumption,
% 2.21/1.04                [status(thm)],
% 2.21/1.04                [c_3165,c_1809,c_1811]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_3657,plain,
% 2.21/1.04      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.21/1.04      inference(superposition,[status(thm)],[c_3170,c_3254]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_5289,plain,
% 2.21/1.04      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.21/1.04      inference(demodulation,[status(thm)],[c_5273,c_3657]) ).
% 2.21/1.04  
% 2.21/1.04  cnf(c_5441,plain,
% 2.21/1.04      ( $false ),
% 2.21/1.04      inference(forward_subsumption_resolution,[status(thm)],[c_5289,c_1654]) ).
% 2.21/1.04  
% 2.21/1.04  
% 2.21/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 2.21/1.04  
% 2.21/1.04  ------                               Statistics
% 2.21/1.04  
% 2.21/1.04  ------ General
% 2.21/1.04  
% 2.21/1.04  abstr_ref_over_cycles:                  0
% 2.21/1.04  abstr_ref_under_cycles:                 0
% 2.21/1.04  gc_basic_clause_elim:                   0
% 2.21/1.04  forced_gc_time:                         0
% 2.21/1.04  parsing_time:                           0.011
% 2.21/1.04  unif_index_cands_time:                  0.
% 2.21/1.04  unif_index_add_time:                    0.
% 2.21/1.04  orderings_time:                         0.
% 2.21/1.04  out_proof_time:                         0.033
% 2.21/1.04  total_time:                             0.249
% 2.21/1.04  num_of_symbols:                         49
% 2.21/1.04  num_of_terms:                           4803
% 2.21/1.04  
% 2.21/1.04  ------ Preprocessing
% 2.21/1.04  
% 2.21/1.04  num_of_splits:                          0
% 2.21/1.04  num_of_split_atoms:                     0
% 2.21/1.04  num_of_reused_defs:                     0
% 2.21/1.04  num_eq_ax_congr_red:                    9
% 2.21/1.04  num_of_sem_filtered_clauses:            1
% 2.21/1.04  num_of_subtypes:                        0
% 2.21/1.04  monotx_restored_types:                  0
% 2.21/1.04  sat_num_of_epr_types:                   0
% 2.21/1.04  sat_num_of_non_cyclic_types:            0
% 2.21/1.04  sat_guarded_non_collapsed_types:        0
% 2.21/1.04  num_pure_diseq_elim:                    0
% 2.21/1.04  simp_replaced_by:                       0
% 2.21/1.04  res_preprocessed:                       144
% 2.21/1.04  prep_upred:                             0
% 2.21/1.04  prep_unflattend:                        36
% 2.21/1.04  smt_new_axioms:                         0
% 2.21/1.04  pred_elim_cands:                        3
% 2.21/1.04  pred_elim:                              2
% 2.21/1.04  pred_elim_cl:                           3
% 2.21/1.04  pred_elim_cycles:                       6
% 2.21/1.04  merged_defs:                            8
% 2.21/1.04  merged_defs_ncl:                        0
% 2.21/1.04  bin_hyper_res:                          8
% 2.21/1.04  prep_cycles:                            4
% 2.21/1.04  pred_elim_time:                         0.013
% 2.21/1.04  splitting_time:                         0.
% 2.21/1.04  sem_filter_time:                        0.
% 2.21/1.04  monotx_time:                            0.
% 2.21/1.04  subtype_inf_time:                       0.
% 2.21/1.04  
% 2.21/1.04  ------ Problem properties
% 2.21/1.04  
% 2.21/1.04  clauses:                                29
% 2.21/1.04  conjectures:                            3
% 2.21/1.04  epr:                                    4
% 2.21/1.04  horn:                                   27
% 2.21/1.04  ground:                                 6
% 2.21/1.04  unary:                                  18
% 2.21/1.04  binary:                                 7
% 2.21/1.04  lits:                                   50
% 2.21/1.04  lits_eq:                                20
% 2.21/1.04  fd_pure:                                0
% 2.21/1.04  fd_pseudo:                              0
% 2.21/1.04  fd_cond:                                1
% 2.21/1.04  fd_pseudo_cond:                         2
% 2.21/1.04  ac_symbols:                             0
% 2.21/1.04  
% 2.21/1.04  ------ Propositional Solver
% 2.21/1.04  
% 2.21/1.04  prop_solver_calls:                      28
% 2.21/1.04  prop_fast_solver_calls:                 774
% 2.21/1.04  smt_solver_calls:                       0
% 2.21/1.04  smt_fast_solver_calls:                  0
% 2.21/1.04  prop_num_of_clauses:                    1945
% 2.21/1.04  prop_preprocess_simplified:             6019
% 2.21/1.04  prop_fo_subsumed:                       7
% 2.21/1.04  prop_solver_time:                       0.
% 2.21/1.04  smt_solver_time:                        0.
% 2.21/1.04  smt_fast_solver_time:                   0.
% 2.21/1.04  prop_fast_solver_time:                  0.
% 2.21/1.04  prop_unsat_core_time:                   0.
% 2.21/1.04  
% 2.21/1.04  ------ QBF
% 2.21/1.04  
% 2.21/1.04  qbf_q_res:                              0
% 2.21/1.04  qbf_num_tautologies:                    0
% 2.21/1.04  qbf_prep_cycles:                        0
% 2.21/1.04  
% 2.21/1.04  ------ BMC1
% 2.21/1.04  
% 2.21/1.04  bmc1_current_bound:                     -1
% 2.21/1.04  bmc1_last_solved_bound:                 -1
% 2.21/1.04  bmc1_unsat_core_size:                   -1
% 2.21/1.04  bmc1_unsat_core_parents_size:           -1
% 2.21/1.04  bmc1_merge_next_fun:                    0
% 2.21/1.04  bmc1_unsat_core_clauses_time:           0.
% 2.21/1.04  
% 2.21/1.04  ------ Instantiation
% 2.21/1.04  
% 2.21/1.04  inst_num_of_clauses:                    634
% 2.21/1.04  inst_num_in_passive:                    59
% 2.21/1.04  inst_num_in_active:                     299
% 2.21/1.04  inst_num_in_unprocessed:                276
% 2.21/1.04  inst_num_of_loops:                      320
% 2.21/1.04  inst_num_of_learning_restarts:          0
% 2.21/1.04  inst_num_moves_active_passive:          17
% 2.21/1.04  inst_lit_activity:                      0
% 2.21/1.04  inst_lit_activity_moves:                0
% 2.21/1.04  inst_num_tautologies:                   0
% 2.21/1.04  inst_num_prop_implied:                  0
% 2.21/1.04  inst_num_existing_simplified:           0
% 2.21/1.04  inst_num_eq_res_simplified:             0
% 2.21/1.04  inst_num_child_elim:                    0
% 2.21/1.04  inst_num_of_dismatching_blockings:      189
% 2.21/1.04  inst_num_of_non_proper_insts:           612
% 2.21/1.04  inst_num_of_duplicates:                 0
% 2.21/1.04  inst_inst_num_from_inst_to_res:         0
% 2.21/1.04  inst_dismatching_checking_time:         0.
% 2.21/1.04  
% 2.21/1.04  ------ Resolution
% 2.21/1.04  
% 2.21/1.04  res_num_of_clauses:                     0
% 2.21/1.04  res_num_in_passive:                     0
% 2.21/1.04  res_num_in_active:                      0
% 2.21/1.04  res_num_of_loops:                       148
% 2.21/1.04  res_forward_subset_subsumed:            79
% 2.21/1.04  res_backward_subset_subsumed:           2
% 2.21/1.04  res_forward_subsumed:                   0
% 2.21/1.04  res_backward_subsumed:                  0
% 2.21/1.04  res_forward_subsumption_resolution:     0
% 2.21/1.04  res_backward_subsumption_resolution:    0
% 2.21/1.04  res_clause_to_clause_subsumption:       378
% 2.21/1.04  res_orphan_elimination:                 0
% 2.21/1.04  res_tautology_del:                      38
% 2.21/1.04  res_num_eq_res_simplified:              0
% 2.21/1.04  res_num_sel_changes:                    0
% 2.21/1.04  res_moves_from_active_to_pass:          0
% 2.21/1.04  
% 2.21/1.04  ------ Superposition
% 2.21/1.04  
% 2.21/1.04  sup_time_total:                         0.
% 2.21/1.04  sup_time_generating:                    0.
% 2.21/1.04  sup_time_sim_full:                      0.
% 2.21/1.04  sup_time_sim_immed:                     0.
% 2.21/1.04  
% 2.21/1.04  sup_num_of_clauses:                     68
% 2.21/1.04  sup_num_in_active:                      40
% 2.21/1.04  sup_num_in_passive:                     28
% 2.21/1.04  sup_num_of_loops:                       62
% 2.21/1.04  sup_fw_superposition:                   83
% 2.21/1.04  sup_bw_superposition:                   40
% 2.21/1.04  sup_immediate_simplified:               27
% 2.21/1.04  sup_given_eliminated:                   1
% 2.21/1.04  comparisons_done:                       0
% 2.21/1.04  comparisons_avoided:                    0
% 2.21/1.04  
% 2.21/1.04  ------ Simplifications
% 2.21/1.04  
% 2.21/1.04  
% 2.21/1.04  sim_fw_subset_subsumed:                 4
% 2.21/1.04  sim_bw_subset_subsumed:                 7
% 2.21/1.04  sim_fw_subsumed:                        15
% 2.21/1.04  sim_bw_subsumed:                        0
% 2.21/1.04  sim_fw_subsumption_res:                 1
% 2.21/1.04  sim_bw_subsumption_res:                 0
% 2.21/1.04  sim_tautology_del:                      1
% 2.21/1.04  sim_eq_tautology_del:                   14
% 2.21/1.04  sim_eq_res_simp:                        0
% 2.21/1.04  sim_fw_demodulated:                     7
% 2.21/1.04  sim_bw_demodulated:                     22
% 2.21/1.04  sim_light_normalised:                   6
% 2.21/1.04  sim_joinable_taut:                      0
% 2.21/1.04  sim_joinable_simp:                      0
% 2.21/1.04  sim_ac_normalised:                      0
% 2.21/1.04  sim_smt_subsumption:                    0
% 2.21/1.04  
%------------------------------------------------------------------------------
