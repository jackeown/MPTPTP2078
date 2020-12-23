%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:34 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 913 expanded)
%              Number of clauses        :   74 ( 200 expanded)
%              Number of leaves         :   20 ( 220 expanded)
%              Depth                    :   22
%              Number of atoms          :  365 (2223 expanded)
%              Number of equality atoms :  176 ( 955 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f77,plain,(
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

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f77,f81])).

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

fof(f72,plain,(
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

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f54,f80,f81,f81,f80])).

fof(f79,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f79,f81,f81])).

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

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f70,f81,f81])).

fof(f76,plain,(
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

fof(f75,plain,(
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

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f41])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f97,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f60])).

cnf(c_18,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_17,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1493,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2418,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1493])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1631,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1633,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1631])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1632,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1635,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1632])).

cnf(c_2862,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2418,c_1633,c_1635])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1502,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1504,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3220,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1502,c_1504])).

cnf(c_5704,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2862,c_3220])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1489,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_345,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_16])).

cnf(c_349,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_345,c_21])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_349])).

cnf(c_1486,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_350])).

cnf(c_1765,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1489,c_1486])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1497,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | k2_enumset1(X1,X1,X1,X1) = X2
    | k2_enumset1(X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3209,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1765,c_1497])).

cnf(c_3648,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3209,c_1489])).

cnf(c_26,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1642,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1688,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1738,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_1016,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1664,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_1016])).

cnf(c_1737,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1664])).

cnf(c_1872,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1737])).

cnf(c_1873,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_323,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_324,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_1487,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_324])).

cnf(c_1670,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1487,c_28,c_324,c_1642])).

cnf(c_1671,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1670])).

cnf(c_3641,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3209,c_1671])).

cnf(c_3858,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3648,c_28,c_26,c_1642,c_1738,c_1872,c_1873,c_3641])).

cnf(c_24,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_313,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_314,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_313])).

cnf(c_1488,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_315,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_314])).

cnf(c_1643,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1642])).

cnf(c_1648,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1488,c_31,c_315,c_1643])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1494,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2079,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1648,c_1494])).

cnf(c_3864,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3858,c_2079])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3877,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3864,c_10])).

cnf(c_3933,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3877,c_1504])).

cnf(c_3939,plain,
    ( ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3933])).

cnf(c_4614,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4994,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3933,c_3939,c_4614])).

cnf(c_1491,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3345,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1489,c_1491])).

cnf(c_1490,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3455,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3345,c_1490])).

cnf(c_5005,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4994,c_3455])).

cnf(c_5808,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5704,c_5005])).

cnf(c_5933,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5808,c_1502])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:21:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.09/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.00  
% 3.09/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.09/1.00  
% 3.09/1.00  ------  iProver source info
% 3.09/1.00  
% 3.09/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.09/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.09/1.00  git: non_committed_changes: false
% 3.09/1.00  git: last_make_outside_of_git: false
% 3.09/1.00  
% 3.09/1.00  ------ 
% 3.09/1.00  
% 3.09/1.00  ------ Input Options
% 3.09/1.00  
% 3.09/1.00  --out_options                           all
% 3.09/1.00  --tptp_safe_out                         true
% 3.09/1.00  --problem_path                          ""
% 3.09/1.00  --include_path                          ""
% 3.09/1.00  --clausifier                            res/vclausify_rel
% 3.09/1.00  --clausifier_options                    --mode clausify
% 3.09/1.00  --stdin                                 false
% 3.09/1.00  --stats_out                             all
% 3.09/1.00  
% 3.09/1.00  ------ General Options
% 3.09/1.00  
% 3.09/1.00  --fof                                   false
% 3.09/1.00  --time_out_real                         305.
% 3.09/1.00  --time_out_virtual                      -1.
% 3.09/1.00  --symbol_type_check                     false
% 3.09/1.00  --clausify_out                          false
% 3.09/1.00  --sig_cnt_out                           false
% 3.09/1.00  --trig_cnt_out                          false
% 3.09/1.00  --trig_cnt_out_tolerance                1.
% 3.09/1.00  --trig_cnt_out_sk_spl                   false
% 3.09/1.00  --abstr_cl_out                          false
% 3.09/1.00  
% 3.09/1.00  ------ Global Options
% 3.09/1.00  
% 3.09/1.00  --schedule                              default
% 3.09/1.00  --add_important_lit                     false
% 3.09/1.00  --prop_solver_per_cl                    1000
% 3.09/1.00  --min_unsat_core                        false
% 3.09/1.00  --soft_assumptions                      false
% 3.09/1.00  --soft_lemma_size                       3
% 3.09/1.00  --prop_impl_unit_size                   0
% 3.09/1.00  --prop_impl_unit                        []
% 3.09/1.00  --share_sel_clauses                     true
% 3.09/1.00  --reset_solvers                         false
% 3.09/1.00  --bc_imp_inh                            [conj_cone]
% 3.09/1.00  --conj_cone_tolerance                   3.
% 3.09/1.00  --extra_neg_conj                        none
% 3.09/1.00  --large_theory_mode                     true
% 3.09/1.00  --prolific_symb_bound                   200
% 3.09/1.00  --lt_threshold                          2000
% 3.09/1.00  --clause_weak_htbl                      true
% 3.09/1.00  --gc_record_bc_elim                     false
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing Options
% 3.09/1.00  
% 3.09/1.00  --preprocessing_flag                    true
% 3.09/1.00  --time_out_prep_mult                    0.1
% 3.09/1.00  --splitting_mode                        input
% 3.09/1.00  --splitting_grd                         true
% 3.09/1.00  --splitting_cvd                         false
% 3.09/1.00  --splitting_cvd_svl                     false
% 3.09/1.00  --splitting_nvd                         32
% 3.09/1.00  --sub_typing                            true
% 3.09/1.00  --prep_gs_sim                           true
% 3.09/1.00  --prep_unflatten                        true
% 3.09/1.00  --prep_res_sim                          true
% 3.09/1.00  --prep_upred                            true
% 3.09/1.00  --prep_sem_filter                       exhaustive
% 3.09/1.00  --prep_sem_filter_out                   false
% 3.09/1.00  --pred_elim                             true
% 3.09/1.00  --res_sim_input                         true
% 3.09/1.00  --eq_ax_congr_red                       true
% 3.09/1.00  --pure_diseq_elim                       true
% 3.09/1.00  --brand_transform                       false
% 3.09/1.00  --non_eq_to_eq                          false
% 3.09/1.00  --prep_def_merge                        true
% 3.09/1.00  --prep_def_merge_prop_impl              false
% 3.09/1.00  --prep_def_merge_mbd                    true
% 3.09/1.00  --prep_def_merge_tr_red                 false
% 3.09/1.00  --prep_def_merge_tr_cl                  false
% 3.09/1.00  --smt_preprocessing                     true
% 3.09/1.00  --smt_ac_axioms                         fast
% 3.09/1.00  --preprocessed_out                      false
% 3.09/1.00  --preprocessed_stats                    false
% 3.09/1.00  
% 3.09/1.00  ------ Abstraction refinement Options
% 3.09/1.00  
% 3.09/1.00  --abstr_ref                             []
% 3.09/1.00  --abstr_ref_prep                        false
% 3.09/1.00  --abstr_ref_until_sat                   false
% 3.09/1.00  --abstr_ref_sig_restrict                funpre
% 3.09/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/1.00  --abstr_ref_under                       []
% 3.09/1.00  
% 3.09/1.00  ------ SAT Options
% 3.09/1.00  
% 3.09/1.00  --sat_mode                              false
% 3.09/1.00  --sat_fm_restart_options                ""
% 3.09/1.00  --sat_gr_def                            false
% 3.09/1.00  --sat_epr_types                         true
% 3.09/1.00  --sat_non_cyclic_types                  false
% 3.09/1.00  --sat_finite_models                     false
% 3.09/1.00  --sat_fm_lemmas                         false
% 3.09/1.00  --sat_fm_prep                           false
% 3.09/1.00  --sat_fm_uc_incr                        true
% 3.09/1.00  --sat_out_model                         small
% 3.09/1.00  --sat_out_clauses                       false
% 3.09/1.00  
% 3.09/1.00  ------ QBF Options
% 3.09/1.00  
% 3.09/1.00  --qbf_mode                              false
% 3.09/1.00  --qbf_elim_univ                         false
% 3.09/1.00  --qbf_dom_inst                          none
% 3.09/1.00  --qbf_dom_pre_inst                      false
% 3.09/1.00  --qbf_sk_in                             false
% 3.09/1.00  --qbf_pred_elim                         true
% 3.09/1.00  --qbf_split                             512
% 3.09/1.00  
% 3.09/1.00  ------ BMC1 Options
% 3.09/1.00  
% 3.09/1.00  --bmc1_incremental                      false
% 3.09/1.00  --bmc1_axioms                           reachable_all
% 3.09/1.00  --bmc1_min_bound                        0
% 3.09/1.00  --bmc1_max_bound                        -1
% 3.09/1.00  --bmc1_max_bound_default                -1
% 3.09/1.00  --bmc1_symbol_reachability              true
% 3.09/1.00  --bmc1_property_lemmas                  false
% 3.09/1.00  --bmc1_k_induction                      false
% 3.09/1.00  --bmc1_non_equiv_states                 false
% 3.09/1.00  --bmc1_deadlock                         false
% 3.09/1.00  --bmc1_ucm                              false
% 3.09/1.00  --bmc1_add_unsat_core                   none
% 3.09/1.00  --bmc1_unsat_core_children              false
% 3.09/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/1.00  --bmc1_out_stat                         full
% 3.09/1.00  --bmc1_ground_init                      false
% 3.09/1.00  --bmc1_pre_inst_next_state              false
% 3.09/1.00  --bmc1_pre_inst_state                   false
% 3.09/1.00  --bmc1_pre_inst_reach_state             false
% 3.09/1.00  --bmc1_out_unsat_core                   false
% 3.09/1.00  --bmc1_aig_witness_out                  false
% 3.09/1.00  --bmc1_verbose                          false
% 3.09/1.00  --bmc1_dump_clauses_tptp                false
% 3.09/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.09/1.00  --bmc1_dump_file                        -
% 3.09/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.09/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.09/1.00  --bmc1_ucm_extend_mode                  1
% 3.09/1.00  --bmc1_ucm_init_mode                    2
% 3.09/1.00  --bmc1_ucm_cone_mode                    none
% 3.09/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.09/1.00  --bmc1_ucm_relax_model                  4
% 3.09/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.09/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/1.00  --bmc1_ucm_layered_model                none
% 3.09/1.00  --bmc1_ucm_max_lemma_size               10
% 3.09/1.00  
% 3.09/1.00  ------ AIG Options
% 3.09/1.00  
% 3.09/1.00  --aig_mode                              false
% 3.09/1.00  
% 3.09/1.00  ------ Instantiation Options
% 3.09/1.00  
% 3.09/1.00  --instantiation_flag                    true
% 3.09/1.00  --inst_sos_flag                         false
% 3.09/1.00  --inst_sos_phase                        true
% 3.09/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel_side                     num_symb
% 3.09/1.00  --inst_solver_per_active                1400
% 3.09/1.00  --inst_solver_calls_frac                1.
% 3.09/1.00  --inst_passive_queue_type               priority_queues
% 3.09/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/1.00  --inst_passive_queues_freq              [25;2]
% 3.09/1.00  --inst_dismatching                      true
% 3.09/1.00  --inst_eager_unprocessed_to_passive     true
% 3.09/1.00  --inst_prop_sim_given                   true
% 3.09/1.00  --inst_prop_sim_new                     false
% 3.09/1.00  --inst_subs_new                         false
% 3.09/1.00  --inst_eq_res_simp                      false
% 3.09/1.00  --inst_subs_given                       false
% 3.09/1.00  --inst_orphan_elimination               true
% 3.09/1.00  --inst_learning_loop_flag               true
% 3.09/1.00  --inst_learning_start                   3000
% 3.09/1.00  --inst_learning_factor                  2
% 3.09/1.00  --inst_start_prop_sim_after_learn       3
% 3.09/1.00  --inst_sel_renew                        solver
% 3.09/1.00  --inst_lit_activity_flag                true
% 3.09/1.00  --inst_restr_to_given                   false
% 3.09/1.00  --inst_activity_threshold               500
% 3.09/1.00  --inst_out_proof                        true
% 3.09/1.00  
% 3.09/1.00  ------ Resolution Options
% 3.09/1.00  
% 3.09/1.00  --resolution_flag                       true
% 3.09/1.00  --res_lit_sel                           adaptive
% 3.09/1.00  --res_lit_sel_side                      none
% 3.09/1.00  --res_ordering                          kbo
% 3.09/1.00  --res_to_prop_solver                    active
% 3.09/1.00  --res_prop_simpl_new                    false
% 3.09/1.00  --res_prop_simpl_given                  true
% 3.09/1.00  --res_passive_queue_type                priority_queues
% 3.09/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/1.00  --res_passive_queues_freq               [15;5]
% 3.09/1.00  --res_forward_subs                      full
% 3.09/1.00  --res_backward_subs                     full
% 3.09/1.00  --res_forward_subs_resolution           true
% 3.09/1.00  --res_backward_subs_resolution          true
% 3.09/1.00  --res_orphan_elimination                true
% 3.09/1.00  --res_time_limit                        2.
% 3.09/1.00  --res_out_proof                         true
% 3.09/1.00  
% 3.09/1.00  ------ Superposition Options
% 3.09/1.00  
% 3.09/1.00  --superposition_flag                    true
% 3.09/1.00  --sup_passive_queue_type                priority_queues
% 3.09/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.09/1.00  --demod_completeness_check              fast
% 3.09/1.00  --demod_use_ground                      true
% 3.09/1.00  --sup_to_prop_solver                    passive
% 3.09/1.00  --sup_prop_simpl_new                    true
% 3.09/1.00  --sup_prop_simpl_given                  true
% 3.09/1.00  --sup_fun_splitting                     false
% 3.09/1.00  --sup_smt_interval                      50000
% 3.09/1.00  
% 3.09/1.00  ------ Superposition Simplification Setup
% 3.09/1.00  
% 3.09/1.00  --sup_indices_passive                   []
% 3.09/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_full_bw                           [BwDemod]
% 3.09/1.00  --sup_immed_triv                        [TrivRules]
% 3.09/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_immed_bw_main                     []
% 3.09/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.00  
% 3.09/1.00  ------ Combination Options
% 3.09/1.00  
% 3.09/1.00  --comb_res_mult                         3
% 3.09/1.00  --comb_sup_mult                         2
% 3.09/1.00  --comb_inst_mult                        10
% 3.09/1.00  
% 3.09/1.00  ------ Debug Options
% 3.09/1.00  
% 3.09/1.00  --dbg_backtrace                         false
% 3.09/1.00  --dbg_dump_prop_clauses                 false
% 3.09/1.00  --dbg_dump_prop_clauses_file            -
% 3.09/1.00  --dbg_out_stat                          false
% 3.09/1.00  ------ Parsing...
% 3.09/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.09/1.00  ------ Proving...
% 3.09/1.00  ------ Problem Properties 
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  clauses                                 25
% 3.09/1.00  conjectures                             3
% 3.09/1.00  EPR                                     4
% 3.09/1.00  Horn                                    23
% 3.09/1.00  unary                                   14
% 3.09/1.00  binary                                  7
% 3.09/1.00  lits                                    42
% 3.09/1.00  lits eq                                 16
% 3.09/1.00  fd_pure                                 0
% 3.09/1.00  fd_pseudo                               0
% 3.09/1.00  fd_cond                                 1
% 3.09/1.00  fd_pseudo_cond                          2
% 3.09/1.00  AC symbols                              0
% 3.09/1.00  
% 3.09/1.00  ------ Schedule dynamic 5 is on 
% 3.09/1.00  
% 3.09/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  ------ 
% 3.09/1.00  Current options:
% 3.09/1.00  ------ 
% 3.09/1.00  
% 3.09/1.00  ------ Input Options
% 3.09/1.00  
% 3.09/1.00  --out_options                           all
% 3.09/1.00  --tptp_safe_out                         true
% 3.09/1.00  --problem_path                          ""
% 3.09/1.00  --include_path                          ""
% 3.09/1.00  --clausifier                            res/vclausify_rel
% 3.09/1.00  --clausifier_options                    --mode clausify
% 3.09/1.00  --stdin                                 false
% 3.09/1.00  --stats_out                             all
% 3.09/1.00  
% 3.09/1.00  ------ General Options
% 3.09/1.00  
% 3.09/1.00  --fof                                   false
% 3.09/1.00  --time_out_real                         305.
% 3.09/1.00  --time_out_virtual                      -1.
% 3.09/1.00  --symbol_type_check                     false
% 3.09/1.00  --clausify_out                          false
% 3.09/1.00  --sig_cnt_out                           false
% 3.09/1.00  --trig_cnt_out                          false
% 3.09/1.00  --trig_cnt_out_tolerance                1.
% 3.09/1.00  --trig_cnt_out_sk_spl                   false
% 3.09/1.00  --abstr_cl_out                          false
% 3.09/1.00  
% 3.09/1.00  ------ Global Options
% 3.09/1.00  
% 3.09/1.00  --schedule                              default
% 3.09/1.00  --add_important_lit                     false
% 3.09/1.00  --prop_solver_per_cl                    1000
% 3.09/1.00  --min_unsat_core                        false
% 3.09/1.00  --soft_assumptions                      false
% 3.09/1.00  --soft_lemma_size                       3
% 3.09/1.00  --prop_impl_unit_size                   0
% 3.09/1.00  --prop_impl_unit                        []
% 3.09/1.00  --share_sel_clauses                     true
% 3.09/1.00  --reset_solvers                         false
% 3.09/1.00  --bc_imp_inh                            [conj_cone]
% 3.09/1.00  --conj_cone_tolerance                   3.
% 3.09/1.00  --extra_neg_conj                        none
% 3.09/1.00  --large_theory_mode                     true
% 3.09/1.00  --prolific_symb_bound                   200
% 3.09/1.00  --lt_threshold                          2000
% 3.09/1.00  --clause_weak_htbl                      true
% 3.09/1.00  --gc_record_bc_elim                     false
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing Options
% 3.09/1.00  
% 3.09/1.00  --preprocessing_flag                    true
% 3.09/1.00  --time_out_prep_mult                    0.1
% 3.09/1.00  --splitting_mode                        input
% 3.09/1.00  --splitting_grd                         true
% 3.09/1.00  --splitting_cvd                         false
% 3.09/1.00  --splitting_cvd_svl                     false
% 3.09/1.00  --splitting_nvd                         32
% 3.09/1.00  --sub_typing                            true
% 3.09/1.00  --prep_gs_sim                           true
% 3.09/1.00  --prep_unflatten                        true
% 3.09/1.00  --prep_res_sim                          true
% 3.09/1.00  --prep_upred                            true
% 3.09/1.00  --prep_sem_filter                       exhaustive
% 3.09/1.00  --prep_sem_filter_out                   false
% 3.09/1.00  --pred_elim                             true
% 3.09/1.00  --res_sim_input                         true
% 3.09/1.00  --eq_ax_congr_red                       true
% 3.09/1.00  --pure_diseq_elim                       true
% 3.09/1.00  --brand_transform                       false
% 3.09/1.00  --non_eq_to_eq                          false
% 3.09/1.00  --prep_def_merge                        true
% 3.09/1.00  --prep_def_merge_prop_impl              false
% 3.09/1.00  --prep_def_merge_mbd                    true
% 3.09/1.00  --prep_def_merge_tr_red                 false
% 3.09/1.00  --prep_def_merge_tr_cl                  false
% 3.09/1.00  --smt_preprocessing                     true
% 3.09/1.00  --smt_ac_axioms                         fast
% 3.09/1.00  --preprocessed_out                      false
% 3.09/1.00  --preprocessed_stats                    false
% 3.09/1.00  
% 3.09/1.00  ------ Abstraction refinement Options
% 3.09/1.00  
% 3.09/1.00  --abstr_ref                             []
% 3.09/1.00  --abstr_ref_prep                        false
% 3.09/1.00  --abstr_ref_until_sat                   false
% 3.09/1.00  --abstr_ref_sig_restrict                funpre
% 3.09/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/1.00  --abstr_ref_under                       []
% 3.09/1.00  
% 3.09/1.00  ------ SAT Options
% 3.09/1.00  
% 3.09/1.00  --sat_mode                              false
% 3.09/1.00  --sat_fm_restart_options                ""
% 3.09/1.00  --sat_gr_def                            false
% 3.09/1.00  --sat_epr_types                         true
% 3.09/1.00  --sat_non_cyclic_types                  false
% 3.09/1.00  --sat_finite_models                     false
% 3.09/1.00  --sat_fm_lemmas                         false
% 3.09/1.00  --sat_fm_prep                           false
% 3.09/1.00  --sat_fm_uc_incr                        true
% 3.09/1.00  --sat_out_model                         small
% 3.09/1.00  --sat_out_clauses                       false
% 3.09/1.00  
% 3.09/1.00  ------ QBF Options
% 3.09/1.00  
% 3.09/1.00  --qbf_mode                              false
% 3.09/1.00  --qbf_elim_univ                         false
% 3.09/1.00  --qbf_dom_inst                          none
% 3.09/1.00  --qbf_dom_pre_inst                      false
% 3.09/1.00  --qbf_sk_in                             false
% 3.09/1.00  --qbf_pred_elim                         true
% 3.09/1.00  --qbf_split                             512
% 3.09/1.00  
% 3.09/1.00  ------ BMC1 Options
% 3.09/1.00  
% 3.09/1.00  --bmc1_incremental                      false
% 3.09/1.00  --bmc1_axioms                           reachable_all
% 3.09/1.00  --bmc1_min_bound                        0
% 3.09/1.00  --bmc1_max_bound                        -1
% 3.09/1.00  --bmc1_max_bound_default                -1
% 3.09/1.00  --bmc1_symbol_reachability              true
% 3.09/1.00  --bmc1_property_lemmas                  false
% 3.09/1.00  --bmc1_k_induction                      false
% 3.09/1.00  --bmc1_non_equiv_states                 false
% 3.09/1.00  --bmc1_deadlock                         false
% 3.09/1.00  --bmc1_ucm                              false
% 3.09/1.00  --bmc1_add_unsat_core                   none
% 3.09/1.00  --bmc1_unsat_core_children              false
% 3.09/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/1.00  --bmc1_out_stat                         full
% 3.09/1.00  --bmc1_ground_init                      false
% 3.09/1.00  --bmc1_pre_inst_next_state              false
% 3.09/1.00  --bmc1_pre_inst_state                   false
% 3.09/1.00  --bmc1_pre_inst_reach_state             false
% 3.09/1.00  --bmc1_out_unsat_core                   false
% 3.09/1.00  --bmc1_aig_witness_out                  false
% 3.09/1.00  --bmc1_verbose                          false
% 3.09/1.00  --bmc1_dump_clauses_tptp                false
% 3.09/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.09/1.00  --bmc1_dump_file                        -
% 3.09/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.09/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.09/1.00  --bmc1_ucm_extend_mode                  1
% 3.09/1.00  --bmc1_ucm_init_mode                    2
% 3.09/1.00  --bmc1_ucm_cone_mode                    none
% 3.09/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.09/1.00  --bmc1_ucm_relax_model                  4
% 3.09/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.09/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/1.00  --bmc1_ucm_layered_model                none
% 3.09/1.00  --bmc1_ucm_max_lemma_size               10
% 3.09/1.00  
% 3.09/1.00  ------ AIG Options
% 3.09/1.00  
% 3.09/1.00  --aig_mode                              false
% 3.09/1.00  
% 3.09/1.00  ------ Instantiation Options
% 3.09/1.00  
% 3.09/1.00  --instantiation_flag                    true
% 3.09/1.00  --inst_sos_flag                         false
% 3.09/1.00  --inst_sos_phase                        true
% 3.09/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/1.00  --inst_lit_sel_side                     none
% 3.09/1.00  --inst_solver_per_active                1400
% 3.09/1.00  --inst_solver_calls_frac                1.
% 3.09/1.00  --inst_passive_queue_type               priority_queues
% 3.09/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/1.00  --inst_passive_queues_freq              [25;2]
% 3.09/1.00  --inst_dismatching                      true
% 3.09/1.00  --inst_eager_unprocessed_to_passive     true
% 3.09/1.00  --inst_prop_sim_given                   true
% 3.09/1.00  --inst_prop_sim_new                     false
% 3.09/1.00  --inst_subs_new                         false
% 3.09/1.00  --inst_eq_res_simp                      false
% 3.09/1.00  --inst_subs_given                       false
% 3.09/1.00  --inst_orphan_elimination               true
% 3.09/1.00  --inst_learning_loop_flag               true
% 3.09/1.00  --inst_learning_start                   3000
% 3.09/1.00  --inst_learning_factor                  2
% 3.09/1.00  --inst_start_prop_sim_after_learn       3
% 3.09/1.00  --inst_sel_renew                        solver
% 3.09/1.00  --inst_lit_activity_flag                true
% 3.09/1.00  --inst_restr_to_given                   false
% 3.09/1.00  --inst_activity_threshold               500
% 3.09/1.00  --inst_out_proof                        true
% 3.09/1.00  
% 3.09/1.00  ------ Resolution Options
% 3.09/1.00  
% 3.09/1.00  --resolution_flag                       false
% 3.09/1.00  --res_lit_sel                           adaptive
% 3.09/1.00  --res_lit_sel_side                      none
% 3.09/1.00  --res_ordering                          kbo
% 3.09/1.00  --res_to_prop_solver                    active
% 3.09/1.00  --res_prop_simpl_new                    false
% 3.09/1.00  --res_prop_simpl_given                  true
% 3.09/1.00  --res_passive_queue_type                priority_queues
% 3.09/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/1.00  --res_passive_queues_freq               [15;5]
% 3.09/1.00  --res_forward_subs                      full
% 3.09/1.00  --res_backward_subs                     full
% 3.09/1.00  --res_forward_subs_resolution           true
% 3.09/1.00  --res_backward_subs_resolution          true
% 3.09/1.00  --res_orphan_elimination                true
% 3.09/1.00  --res_time_limit                        2.
% 3.09/1.00  --res_out_proof                         true
% 3.09/1.00  
% 3.09/1.00  ------ Superposition Options
% 3.09/1.00  
% 3.09/1.00  --superposition_flag                    true
% 3.09/1.00  --sup_passive_queue_type                priority_queues
% 3.09/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.09/1.00  --demod_completeness_check              fast
% 3.09/1.00  --demod_use_ground                      true
% 3.09/1.00  --sup_to_prop_solver                    passive
% 3.09/1.00  --sup_prop_simpl_new                    true
% 3.09/1.00  --sup_prop_simpl_given                  true
% 3.09/1.00  --sup_fun_splitting                     false
% 3.09/1.00  --sup_smt_interval                      50000
% 3.09/1.00  
% 3.09/1.00  ------ Superposition Simplification Setup
% 3.09/1.00  
% 3.09/1.00  --sup_indices_passive                   []
% 3.09/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_full_bw                           [BwDemod]
% 3.09/1.00  --sup_immed_triv                        [TrivRules]
% 3.09/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_immed_bw_main                     []
% 3.09/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/1.00  
% 3.09/1.00  ------ Combination Options
% 3.09/1.00  
% 3.09/1.00  --comb_res_mult                         3
% 3.09/1.00  --comb_sup_mult                         2
% 3.09/1.00  --comb_inst_mult                        10
% 3.09/1.00  
% 3.09/1.00  ------ Debug Options
% 3.09/1.00  
% 3.09/1.00  --dbg_backtrace                         false
% 3.09/1.00  --dbg_dump_prop_clauses                 false
% 3.09/1.00  --dbg_dump_prop_clauses_file            -
% 3.09/1.00  --dbg_out_stat                          false
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  ------ Proving...
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  % SZS status Theorem for theBenchmark.p
% 3.09/1.00  
% 3.09/1.00   Resolution empty clause
% 3.09/1.00  
% 3.09/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.09/1.00  
% 3.09/1.00  fof(f13,axiom,(
% 3.09/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f69,plain,(
% 3.09/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.09/1.00    inference(cnf_transformation,[],[f13])).
% 3.09/1.00  
% 3.09/1.00  fof(f12,axiom,(
% 3.09/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f27,plain,(
% 3.09/1.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.09/1.00    inference(ennf_transformation,[],[f12])).
% 3.09/1.00  
% 3.09/1.00  fof(f67,plain,(
% 3.09/1.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f27])).
% 3.09/1.00  
% 3.09/1.00  fof(f15,axiom,(
% 3.09/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f30,plain,(
% 3.09/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.00    inference(ennf_transformation,[],[f15])).
% 3.09/1.00  
% 3.09/1.00  fof(f71,plain,(
% 3.09/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f30])).
% 3.09/1.00  
% 3.09/1.00  fof(f8,axiom,(
% 3.09/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f62,plain,(
% 3.09/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f8])).
% 3.09/1.00  
% 3.09/1.00  fof(f2,axiom,(
% 3.09/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f50,plain,(
% 3.09/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f2])).
% 3.09/1.00  
% 3.09/1.00  fof(f1,axiom,(
% 3.09/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f37,plain,(
% 3.09/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/1.00    inference(nnf_transformation,[],[f1])).
% 3.09/1.00  
% 3.09/1.00  fof(f38,plain,(
% 3.09/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.09/1.00    inference(flattening,[],[f37])).
% 3.09/1.00  
% 3.09/1.00  fof(f49,plain,(
% 3.09/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f38])).
% 3.09/1.00  
% 3.09/1.00  fof(f19,conjecture,(
% 3.09/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f20,negated_conjecture,(
% 3.09/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.09/1.00    inference(negated_conjecture,[],[f19])).
% 3.09/1.00  
% 3.09/1.00  fof(f21,plain,(
% 3.09/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.09/1.00    inference(pure_predicate_removal,[],[f20])).
% 3.09/1.00  
% 3.09/1.00  fof(f35,plain,(
% 3.09/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 3.09/1.00    inference(ennf_transformation,[],[f21])).
% 3.09/1.00  
% 3.09/1.00  fof(f36,plain,(
% 3.09/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 3.09/1.00    inference(flattening,[],[f35])).
% 3.09/1.00  
% 3.09/1.00  fof(f45,plain,(
% 3.09/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 3.09/1.00    introduced(choice_axiom,[])).
% 3.09/1.00  
% 3.09/1.00  fof(f46,plain,(
% 3.09/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 3.09/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f36,f45])).
% 3.09/1.00  
% 3.09/1.00  fof(f77,plain,(
% 3.09/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.09/1.00    inference(cnf_transformation,[],[f46])).
% 3.09/1.00  
% 3.09/1.00  fof(f3,axiom,(
% 3.09/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f51,plain,(
% 3.09/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f3])).
% 3.09/1.00  
% 3.09/1.00  fof(f4,axiom,(
% 3.09/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f52,plain,(
% 3.09/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f4])).
% 3.09/1.00  
% 3.09/1.00  fof(f5,axiom,(
% 3.09/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f53,plain,(
% 3.09/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f5])).
% 3.09/1.00  
% 3.09/1.00  fof(f80,plain,(
% 3.09/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.09/1.00    inference(definition_unfolding,[],[f52,f53])).
% 3.09/1.00  
% 3.09/1.00  fof(f81,plain,(
% 3.09/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.09/1.00    inference(definition_unfolding,[],[f51,f80])).
% 3.09/1.00  
% 3.09/1.00  fof(f89,plain,(
% 3.09/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 3.09/1.00    inference(definition_unfolding,[],[f77,f81])).
% 3.09/1.00  
% 3.09/1.00  fof(f16,axiom,(
% 3.09/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f23,plain,(
% 3.09/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.09/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.09/1.00  
% 3.09/1.00  fof(f31,plain,(
% 3.09/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.00    inference(ennf_transformation,[],[f23])).
% 3.09/1.00  
% 3.09/1.00  fof(f72,plain,(
% 3.09/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f31])).
% 3.09/1.00  
% 3.09/1.00  fof(f11,axiom,(
% 3.09/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f26,plain,(
% 3.09/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.09/1.00    inference(ennf_transformation,[],[f11])).
% 3.09/1.00  
% 3.09/1.00  fof(f44,plain,(
% 3.09/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.09/1.00    inference(nnf_transformation,[],[f26])).
% 3.09/1.00  
% 3.09/1.00  fof(f65,plain,(
% 3.09/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f44])).
% 3.09/1.00  
% 3.09/1.00  fof(f6,axiom,(
% 3.09/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f25,plain,(
% 3.09/1.00    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.09/1.00    inference(ennf_transformation,[],[f6])).
% 3.09/1.00  
% 3.09/1.00  fof(f39,plain,(
% 3.09/1.00    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.09/1.00    inference(nnf_transformation,[],[f25])).
% 3.09/1.00  
% 3.09/1.00  fof(f40,plain,(
% 3.09/1.00    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.09/1.00    inference(flattening,[],[f39])).
% 3.09/1.00  
% 3.09/1.00  fof(f54,plain,(
% 3.09/1.00    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f40])).
% 3.09/1.00  
% 3.09/1.00  fof(f86,plain,(
% 3.09/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 3.09/1.00    inference(definition_unfolding,[],[f54,f80,f81,f81,f80])).
% 3.09/1.00  
% 3.09/1.00  fof(f79,plain,(
% 3.09/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 3.09/1.00    inference(cnf_transformation,[],[f46])).
% 3.09/1.00  
% 3.09/1.00  fof(f88,plain,(
% 3.09/1.00    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 3.09/1.00    inference(definition_unfolding,[],[f79,f81,f81])).
% 3.09/1.00  
% 3.09/1.00  fof(f17,axiom,(
% 3.09/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f32,plain,(
% 3.09/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/1.00    inference(ennf_transformation,[],[f17])).
% 3.09/1.00  
% 3.09/1.00  fof(f73,plain,(
% 3.09/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f32])).
% 3.09/1.00  
% 3.09/1.00  fof(f14,axiom,(
% 3.09/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f28,plain,(
% 3.09/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.09/1.00    inference(ennf_transformation,[],[f14])).
% 3.09/1.00  
% 3.09/1.00  fof(f29,plain,(
% 3.09/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.09/1.00    inference(flattening,[],[f28])).
% 3.09/1.00  
% 3.09/1.00  fof(f70,plain,(
% 3.09/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f29])).
% 3.09/1.00  
% 3.09/1.00  fof(f87,plain,(
% 3.09/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.09/1.00    inference(definition_unfolding,[],[f70,f81,f81])).
% 3.09/1.00  
% 3.09/1.00  fof(f76,plain,(
% 3.09/1.00    v1_funct_1(sK3)),
% 3.09/1.00    inference(cnf_transformation,[],[f46])).
% 3.09/1.00  
% 3.09/1.00  fof(f18,axiom,(
% 3.09/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f22,plain,(
% 3.09/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 3.09/1.00    inference(pure_predicate_removal,[],[f18])).
% 3.09/1.00  
% 3.09/1.00  fof(f33,plain,(
% 3.09/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.09/1.00    inference(ennf_transformation,[],[f22])).
% 3.09/1.00  
% 3.09/1.00  fof(f34,plain,(
% 3.09/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.09/1.00    inference(flattening,[],[f33])).
% 3.09/1.00  
% 3.09/1.00  fof(f75,plain,(
% 3.09/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/1.00    inference(cnf_transformation,[],[f34])).
% 3.09/1.00  
% 3.09/1.00  fof(f9,axiom,(
% 3.09/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f43,plain,(
% 3.09/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.09/1.00    inference(nnf_transformation,[],[f9])).
% 3.09/1.00  
% 3.09/1.00  fof(f63,plain,(
% 3.09/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.09/1.00    inference(cnf_transformation,[],[f43])).
% 3.09/1.00  
% 3.09/1.00  fof(f7,axiom,(
% 3.09/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.09/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/1.00  
% 3.09/1.00  fof(f41,plain,(
% 3.09/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.09/1.00    inference(nnf_transformation,[],[f7])).
% 3.09/1.00  
% 3.09/1.00  fof(f42,plain,(
% 3.09/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.09/1.00    inference(flattening,[],[f41])).
% 3.09/1.00  
% 3.09/1.00  fof(f60,plain,(
% 3.09/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.09/1.00    inference(cnf_transformation,[],[f42])).
% 3.09/1.00  
% 3.09/1.00  fof(f97,plain,(
% 3.09/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.09/1.00    inference(equality_resolution,[],[f60])).
% 3.09/1.00  
% 3.09/1.00  cnf(c_18,plain,
% 3.09/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.09/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_17,plain,
% 3.09/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1493,plain,
% 3.09/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 3.09/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2418,plain,
% 3.09/1.00      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.09/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_18,c_1493]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_21,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1631,plain,
% 3.09/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.09/1.00      | v1_relat_1(k1_xboole_0) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1633,plain,
% 3.09/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.09/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_1631]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_12,plain,
% 3.09/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.09/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1632,plain,
% 3.09/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1635,plain,
% 3.09/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_1632]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2862,plain,
% 3.09/1.00      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_2418,c_1633,c_1635]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3,plain,
% 3.09/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f50]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1502,plain,
% 3.09/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_0,plain,
% 3.09/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.09/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1504,plain,
% 3.09/1.00      ( X0 = X1
% 3.09/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.09/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3220,plain,
% 3.09/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_1502,c_1504]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_5704,plain,
% 3.09/1.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_2862,c_3220]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_28,negated_conjecture,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 3.09/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1489,plain,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_22,plain,
% 3.09/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.09/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_16,plain,
% 3.09/1.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_345,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.09/1.00      | ~ v1_relat_1(X0) ),
% 3.09/1.00      inference(resolution,[status(thm)],[c_22,c_16]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_349,plain,
% 3.09/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.09/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.09/1.00      inference(global_propositional_subsumption,[status(thm)],[c_345,c_21]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_350,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.09/1.00      inference(renaming,[status(thm)],[c_349]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1486,plain,
% 3.09/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.09/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_350]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1765,plain,
% 3.09/1.00      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_1489,c_1486]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_8,plain,
% 3.09/1.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 3.09/1.00      | k2_enumset1(X1,X1,X1,X2) = X0
% 3.09/1.00      | k2_enumset1(X2,X2,X2,X2) = X0
% 3.09/1.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.09/1.00      | k1_xboole_0 = X0 ),
% 3.09/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1497,plain,
% 3.09/1.00      ( k2_enumset1(X0,X0,X0,X1) = X2
% 3.09/1.00      | k2_enumset1(X1,X1,X1,X1) = X2
% 3.09/1.00      | k2_enumset1(X0,X0,X0,X0) = X2
% 3.09/1.00      | k1_xboole_0 = X2
% 3.09/1.00      | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3209,plain,
% 3.09/1.00      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.09/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_1765,c_1497]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3648,plain,
% 3.09/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.09/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_3209,c_1489]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_26,negated_conjecture,
% 3.09/1.00      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.09/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1642,plain,
% 3.09/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.09/1.00      | v1_relat_1(sK3) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_23,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.09/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1688,plain,
% 3.09/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.09/1.00      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1738,plain,
% 3.09/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.09/1.00      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_1688]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1016,plain,
% 3.09/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.09/1.00      theory(equality) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1664,plain,
% 3.09/1.00      ( ~ r1_tarski(X0,X1)
% 3.09/1.00      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.09/1.00      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 3.09/1.00      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_1016]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1737,plain,
% 3.09/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.09/1.00      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 3.09/1.00      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.09/1.00      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_1664]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1872,plain,
% 3.09/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.09/1.00      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 3.09/1.00      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.09/1.00      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_1737]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1873,plain,
% 3.09/1.00      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_20,plain,
% 3.09/1.00      ( ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v1_relat_1(X0)
% 3.09/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.09/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_29,negated_conjecture,
% 3.09/1.00      ( v1_funct_1(sK3) ),
% 3.09/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_323,plain,
% 3.09/1.00      ( ~ v1_relat_1(X0)
% 3.09/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.09/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.09/1.00      | sK3 != X0 ),
% 3.09/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_324,plain,
% 3.09/1.00      ( ~ v1_relat_1(sK3)
% 3.09/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.09/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.09/1.00      inference(unflattening,[status(thm)],[c_323]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1487,plain,
% 3.09/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.09/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.09/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_324]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1670,plain,
% 3.09/1.00      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.09/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_1487,c_28,c_324,c_1642]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1671,plain,
% 3.09/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.09/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.09/1.00      inference(renaming,[status(thm)],[c_1670]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3641,plain,
% 3.09/1.00      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.09/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_3209,c_1671]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3858,plain,
% 3.09/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_3648,c_28,c_26,c_1642,c_1738,c_1872,c_1873,c_3641]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_24,plain,
% 3.09/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.09/1.00      | ~ v1_funct_1(X0)
% 3.09/1.00      | ~ v1_relat_1(X0) ),
% 3.09/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_313,plain,
% 3.09/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.09/1.00      | ~ v1_relat_1(X0)
% 3.09/1.00      | sK3 != X0 ),
% 3.09/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_314,plain,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
% 3.09/1.00      | ~ v1_relat_1(sK3) ),
% 3.09/1.00      inference(unflattening,[status(thm)],[c_313]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1488,plain,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
% 3.09/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_31,plain,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_315,plain,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
% 3.09/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_314]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1643,plain,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 3.09/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_1642]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1648,plain,
% 3.09/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_1488,c_31,c_315,c_1643]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_14,plain,
% 3.09/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.09/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1494,plain,
% 3.09/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.09/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_2079,plain,
% 3.09/1.00      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) = iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_1648,c_1494]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3864,plain,
% 3.09/1.00      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) = iProver_top ),
% 3.09/1.00      inference(demodulation,[status(thm)],[c_3858,c_2079]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_10,plain,
% 3.09/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.09/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3877,plain,
% 3.09/1.00      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.09/1.00      inference(demodulation,[status(thm)],[c_3864,c_10]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3933,plain,
% 3.09/1.00      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_3877,c_1504]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3939,plain,
% 3.09/1.00      ( ~ r1_tarski(k1_xboole_0,sK3) | sK3 = k1_xboole_0 ),
% 3.09/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3933]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_4614,plain,
% 3.09/1.00      ( r1_tarski(k1_xboole_0,sK3) ),
% 3.09/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_4994,plain,
% 3.09/1.00      ( sK3 = k1_xboole_0 ),
% 3.09/1.00      inference(global_propositional_subsumption,
% 3.09/1.00                [status(thm)],
% 3.09/1.00                [c_3933,c_3939,c_4614]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1491,plain,
% 3.09/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.09/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3345,plain,
% 3.09/1.00      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.09/1.00      inference(superposition,[status(thm)],[c_1489,c_1491]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_1490,plain,
% 3.09/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.09/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_3455,plain,
% 3.09/1.00      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.09/1.00      inference(demodulation,[status(thm)],[c_3345,c_1490]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_5005,plain,
% 3.09/1.00      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.09/1.00      inference(demodulation,[status(thm)],[c_4994,c_3455]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_5808,plain,
% 3.09/1.00      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.09/1.00      inference(demodulation,[status(thm)],[c_5704,c_5005]) ).
% 3.09/1.00  
% 3.09/1.00  cnf(c_5933,plain,
% 3.09/1.00      ( $false ),
% 3.09/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5808,c_1502]) ).
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.09/1.00  
% 3.09/1.00  ------                               Statistics
% 3.09/1.00  
% 3.09/1.00  ------ General
% 3.09/1.00  
% 3.09/1.00  abstr_ref_over_cycles:                  0
% 3.09/1.00  abstr_ref_under_cycles:                 0
% 3.09/1.00  gc_basic_clause_elim:                   0
% 3.09/1.00  forced_gc_time:                         0
% 3.09/1.00  parsing_time:                           0.01
% 3.09/1.00  unif_index_cands_time:                  0.
% 3.09/1.00  unif_index_add_time:                    0.
% 3.09/1.00  orderings_time:                         0.
% 3.09/1.00  out_proof_time:                         0.028
% 3.09/1.00  total_time:                             0.235
% 3.09/1.00  num_of_symbols:                         49
% 3.09/1.00  num_of_terms:                           4681
% 3.09/1.00  
% 3.09/1.00  ------ Preprocessing
% 3.09/1.00  
% 3.09/1.00  num_of_splits:                          0
% 3.09/1.00  num_of_split_atoms:                     0
% 3.09/1.00  num_of_reused_defs:                     0
% 3.09/1.00  num_eq_ax_congr_red:                    9
% 3.09/1.00  num_of_sem_filtered_clauses:            1
% 3.09/1.00  num_of_subtypes:                        0
% 3.09/1.00  monotx_restored_types:                  0
% 3.09/1.00  sat_num_of_epr_types:                   0
% 3.09/1.00  sat_num_of_non_cyclic_types:            0
% 3.09/1.00  sat_guarded_non_collapsed_types:        0
% 3.09/1.00  num_pure_diseq_elim:                    0
% 3.09/1.00  simp_replaced_by:                       0
% 3.09/1.00  res_preprocessed:                       128
% 3.09/1.00  prep_upred:                             0
% 3.09/1.00  prep_unflattend:                        36
% 3.09/1.00  smt_new_axioms:                         0
% 3.09/1.00  pred_elim_cands:                        3
% 3.09/1.00  pred_elim:                              2
% 3.09/1.00  pred_elim_cl:                           3
% 3.09/1.00  pred_elim_cycles:                       6
% 3.09/1.00  merged_defs:                            8
% 3.09/1.00  merged_defs_ncl:                        0
% 3.09/1.00  bin_hyper_res:                          8
% 3.09/1.00  prep_cycles:                            4
% 3.09/1.00  pred_elim_time:                         0.008
% 3.09/1.00  splitting_time:                         0.
% 3.09/1.00  sem_filter_time:                        0.
% 3.09/1.00  monotx_time:                            0.001
% 3.09/1.00  subtype_inf_time:                       0.
% 3.09/1.00  
% 3.09/1.00  ------ Problem properties
% 3.09/1.00  
% 3.09/1.00  clauses:                                25
% 3.09/1.00  conjectures:                            3
% 3.09/1.00  epr:                                    4
% 3.09/1.00  horn:                                   23
% 3.09/1.00  ground:                                 6
% 3.09/1.00  unary:                                  14
% 3.09/1.00  binary:                                 7
% 3.09/1.00  lits:                                   42
% 3.09/1.00  lits_eq:                                16
% 3.09/1.00  fd_pure:                                0
% 3.09/1.00  fd_pseudo:                              0
% 3.09/1.00  fd_cond:                                1
% 3.09/1.00  fd_pseudo_cond:                         2
% 3.09/1.00  ac_symbols:                             0
% 3.09/1.00  
% 3.09/1.00  ------ Propositional Solver
% 3.09/1.00  
% 3.09/1.00  prop_solver_calls:                      28
% 3.09/1.00  prop_fast_solver_calls:                 725
% 3.09/1.00  smt_solver_calls:                       0
% 3.09/1.00  smt_fast_solver_calls:                  0
% 3.09/1.00  prop_num_of_clauses:                    2052
% 3.09/1.00  prop_preprocess_simplified:             7220
% 3.09/1.00  prop_fo_subsumed:                       13
% 3.09/1.00  prop_solver_time:                       0.
% 3.09/1.00  smt_solver_time:                        0.
% 3.09/1.00  smt_fast_solver_time:                   0.
% 3.09/1.00  prop_fast_solver_time:                  0.
% 3.09/1.00  prop_unsat_core_time:                   0.
% 3.09/1.00  
% 3.09/1.00  ------ QBF
% 3.09/1.00  
% 3.09/1.00  qbf_q_res:                              0
% 3.09/1.00  qbf_num_tautologies:                    0
% 3.09/1.00  qbf_prep_cycles:                        0
% 3.09/1.00  
% 3.09/1.00  ------ BMC1
% 3.09/1.00  
% 3.09/1.00  bmc1_current_bound:                     -1
% 3.09/1.00  bmc1_last_solved_bound:                 -1
% 3.09/1.00  bmc1_unsat_core_size:                   -1
% 3.09/1.00  bmc1_unsat_core_parents_size:           -1
% 3.09/1.00  bmc1_merge_next_fun:                    0
% 3.09/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.09/1.00  
% 3.09/1.00  ------ Instantiation
% 3.09/1.00  
% 3.09/1.00  inst_num_of_clauses:                    683
% 3.09/1.00  inst_num_in_passive:                    335
% 3.09/1.00  inst_num_in_active:                     307
% 3.09/1.00  inst_num_in_unprocessed:                41
% 3.09/1.00  inst_num_of_loops:                      330
% 3.09/1.00  inst_num_of_learning_restarts:          0
% 3.09/1.00  inst_num_moves_active_passive:          21
% 3.09/1.00  inst_lit_activity:                      0
% 3.09/1.00  inst_lit_activity_moves:                0
% 3.09/1.00  inst_num_tautologies:                   0
% 3.09/1.00  inst_num_prop_implied:                  0
% 3.09/1.00  inst_num_existing_simplified:           0
% 3.09/1.00  inst_num_eq_res_simplified:             0
% 3.09/1.00  inst_num_child_elim:                    0
% 3.09/1.00  inst_num_of_dismatching_blockings:      208
% 3.09/1.00  inst_num_of_non_proper_insts:           634
% 3.09/1.00  inst_num_of_duplicates:                 0
% 3.09/1.00  inst_inst_num_from_inst_to_res:         0
% 3.09/1.00  inst_dismatching_checking_time:         0.
% 3.09/1.00  
% 3.09/1.00  ------ Resolution
% 3.09/1.00  
% 3.09/1.00  res_num_of_clauses:                     0
% 3.09/1.00  res_num_in_passive:                     0
% 3.09/1.00  res_num_in_active:                      0
% 3.09/1.00  res_num_of_loops:                       132
% 3.09/1.00  res_forward_subset_subsumed:            78
% 3.09/1.00  res_backward_subset_subsumed:           2
% 3.09/1.00  res_forward_subsumed:                   0
% 3.09/1.00  res_backward_subsumed:                  0
% 3.09/1.00  res_forward_subsumption_resolution:     0
% 3.09/1.00  res_backward_subsumption_resolution:    0
% 3.09/1.00  res_clause_to_clause_subsumption:       300
% 3.09/1.00  res_orphan_elimination:                 0
% 3.09/1.00  res_tautology_del:                      38
% 3.09/1.00  res_num_eq_res_simplified:              0
% 3.09/1.00  res_num_sel_changes:                    0
% 3.09/1.00  res_moves_from_active_to_pass:          0
% 3.09/1.00  
% 3.09/1.00  ------ Superposition
% 3.09/1.00  
% 3.09/1.00  sup_time_total:                         0.
% 3.09/1.00  sup_time_generating:                    0.
% 3.09/1.00  sup_time_sim_full:                      0.
% 3.09/1.00  sup_time_sim_immed:                     0.
% 3.09/1.00  
% 3.09/1.00  sup_num_of_clauses:                     64
% 3.09/1.00  sup_num_in_active:                      39
% 3.09/1.00  sup_num_in_passive:                     25
% 3.09/1.00  sup_num_of_loops:                       64
% 3.09/1.00  sup_fw_superposition:                   83
% 3.09/1.00  sup_bw_superposition:                   36
% 3.09/1.00  sup_immediate_simplified:               24
% 3.09/1.00  sup_given_eliminated:                   0
% 3.09/1.00  comparisons_done:                       0
% 3.09/1.00  comparisons_avoided:                    0
% 3.09/1.00  
% 3.09/1.00  ------ Simplifications
% 3.09/1.00  
% 3.09/1.00  
% 3.09/1.00  sim_fw_subset_subsumed:                 4
% 3.09/1.00  sim_bw_subset_subsumed:                 6
% 3.09/1.00  sim_fw_subsumed:                        16
% 3.09/1.00  sim_bw_subsumed:                        0
% 3.09/1.00  sim_fw_subsumption_res:                 1
% 3.09/1.00  sim_bw_subsumption_res:                 0
% 3.09/1.00  sim_tautology_del:                      2
% 3.09/1.00  sim_eq_tautology_del:                   10
% 3.09/1.00  sim_eq_res_simp:                        0
% 3.09/1.00  sim_fw_demodulated:                     4
% 3.09/1.00  sim_bw_demodulated:                     25
% 3.09/1.00  sim_light_normalised:                   11
% 3.09/1.00  sim_joinable_taut:                      0
% 3.09/1.00  sim_joinable_simp:                      0
% 3.09/1.00  sim_ac_normalised:                      0
% 3.09/1.00  sim_smt_subsumption:                    0
% 3.09/1.00  
%------------------------------------------------------------------------------
