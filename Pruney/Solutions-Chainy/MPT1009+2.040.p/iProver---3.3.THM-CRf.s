%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:36 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 724 expanded)
%              Number of clauses        :   70 ( 147 expanded)
%              Number of leaves         :   20 ( 190 expanded)
%              Depth                    :   19
%              Number of atoms          :  376 (1737 expanded)
%              Number of equality atoms :  220 ( 919 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f39,plain,
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

fof(f40,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f39])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f73])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f70,f74])).

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

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f6,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f48,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
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
    inference(definition_unfolding,[],[f48,f47,f73,f73,f73,f74,f74,f74,f47])).

fof(f72,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f72,f74,f74])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f65,f74,f74])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1191,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_15])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_381,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_22])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_381])).

cnf(c_1189,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_1494,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1191,c_1189])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1199,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2762,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1494,c_1199])).

cnf(c_2870,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2762,c_1191])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1359,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1399,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1445,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1399])).

cnf(c_812,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1380,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_812])).

cnf(c_1444,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1380])).

cnf(c_1601,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_16,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1602,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_280,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_281,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_280])).

cnf(c_1190,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_282,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_281])).

cnf(c_1360,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1359])).

cnf(c_1373,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1190,c_30,c_282,c_1360])).

cnf(c_1374,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1373])).

cnf(c_2864,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2762,c_1374])).

cnf(c_2932,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2870,c_27,c_25,c_1359,c_1445,c_1601,c_1602,c_2864])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1195,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2950,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2932,c_1195])).

cnf(c_1459,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_810,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1472,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_810])).

cnf(c_811,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1733,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(c_2286,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_1733])).

cnf(c_2287,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_2286])).

cnf(c_3100,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2950,c_27,c_25,c_1359,c_1445,c_1459,c_1472,c_1601,c_1602,c_2287,c_2864])).

cnf(c_1193,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2532,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1191,c_1193])).

cnf(c_1192,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2541,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2532,c_1192])).

cnf(c_3104,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3100,c_2541])).

cnf(c_17,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1197,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1932,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_1197])).

cnf(c_1351,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1353,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1351])).

cnf(c_13,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1352,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1355,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1352])).

cnf(c_2063,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1932,c_1353,c_1355])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1208,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1210,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2166,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1208,c_1210])).

cnf(c_2347,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2063,c_2166])).

cnf(c_3112,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3104,c_2347])).

cnf(c_3153,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3112,c_1208])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:40:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.33/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.99  
% 2.33/0.99  ------  iProver source info
% 2.33/0.99  
% 2.33/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.99  git: non_committed_changes: false
% 2.33/0.99  git: last_make_outside_of_git: false
% 2.33/0.99  
% 2.33/0.99  ------ 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options
% 2.33/0.99  
% 2.33/0.99  --out_options                           all
% 2.33/0.99  --tptp_safe_out                         true
% 2.33/0.99  --problem_path                          ""
% 2.33/0.99  --include_path                          ""
% 2.33/0.99  --clausifier                            res/vclausify_rel
% 2.33/0.99  --clausifier_options                    --mode clausify
% 2.33/0.99  --stdin                                 false
% 2.33/0.99  --stats_out                             all
% 2.33/0.99  
% 2.33/0.99  ------ General Options
% 2.33/0.99  
% 2.33/0.99  --fof                                   false
% 2.33/0.99  --time_out_real                         305.
% 2.33/0.99  --time_out_virtual                      -1.
% 2.33/0.99  --symbol_type_check                     false
% 2.33/0.99  --clausify_out                          false
% 2.33/0.99  --sig_cnt_out                           false
% 2.33/0.99  --trig_cnt_out                          false
% 2.33/0.99  --trig_cnt_out_tolerance                1.
% 2.33/0.99  --trig_cnt_out_sk_spl                   false
% 2.33/0.99  --abstr_cl_out                          false
% 2.33/0.99  
% 2.33/0.99  ------ Global Options
% 2.33/0.99  
% 2.33/0.99  --schedule                              default
% 2.33/0.99  --add_important_lit                     false
% 2.33/0.99  --prop_solver_per_cl                    1000
% 2.33/0.99  --min_unsat_core                        false
% 2.33/0.99  --soft_assumptions                      false
% 2.33/0.99  --soft_lemma_size                       3
% 2.33/0.99  --prop_impl_unit_size                   0
% 2.33/0.99  --prop_impl_unit                        []
% 2.33/0.99  --share_sel_clauses                     true
% 2.33/0.99  --reset_solvers                         false
% 2.33/0.99  --bc_imp_inh                            [conj_cone]
% 2.33/0.99  --conj_cone_tolerance                   3.
% 2.33/0.99  --extra_neg_conj                        none
% 2.33/0.99  --large_theory_mode                     true
% 2.33/0.99  --prolific_symb_bound                   200
% 2.33/0.99  --lt_threshold                          2000
% 2.33/0.99  --clause_weak_htbl                      true
% 2.33/0.99  --gc_record_bc_elim                     false
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing Options
% 2.33/0.99  
% 2.33/0.99  --preprocessing_flag                    true
% 2.33/0.99  --time_out_prep_mult                    0.1
% 2.33/0.99  --splitting_mode                        input
% 2.33/0.99  --splitting_grd                         true
% 2.33/0.99  --splitting_cvd                         false
% 2.33/0.99  --splitting_cvd_svl                     false
% 2.33/0.99  --splitting_nvd                         32
% 2.33/0.99  --sub_typing                            true
% 2.33/0.99  --prep_gs_sim                           true
% 2.33/0.99  --prep_unflatten                        true
% 2.33/0.99  --prep_res_sim                          true
% 2.33/0.99  --prep_upred                            true
% 2.33/0.99  --prep_sem_filter                       exhaustive
% 2.33/0.99  --prep_sem_filter_out                   false
% 2.33/0.99  --pred_elim                             true
% 2.33/0.99  --res_sim_input                         true
% 2.33/0.99  --eq_ax_congr_red                       true
% 2.33/0.99  --pure_diseq_elim                       true
% 2.33/0.99  --brand_transform                       false
% 2.33/0.99  --non_eq_to_eq                          false
% 2.33/0.99  --prep_def_merge                        true
% 2.33/0.99  --prep_def_merge_prop_impl              false
% 2.33/0.99  --prep_def_merge_mbd                    true
% 2.33/0.99  --prep_def_merge_tr_red                 false
% 2.33/0.99  --prep_def_merge_tr_cl                  false
% 2.33/0.99  --smt_preprocessing                     true
% 2.33/0.99  --smt_ac_axioms                         fast
% 2.33/0.99  --preprocessed_out                      false
% 2.33/0.99  --preprocessed_stats                    false
% 2.33/0.99  
% 2.33/0.99  ------ Abstraction refinement Options
% 2.33/0.99  
% 2.33/0.99  --abstr_ref                             []
% 2.33/0.99  --abstr_ref_prep                        false
% 2.33/0.99  --abstr_ref_until_sat                   false
% 2.33/0.99  --abstr_ref_sig_restrict                funpre
% 2.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.99  --abstr_ref_under                       []
% 2.33/0.99  
% 2.33/0.99  ------ SAT Options
% 2.33/0.99  
% 2.33/0.99  --sat_mode                              false
% 2.33/0.99  --sat_fm_restart_options                ""
% 2.33/0.99  --sat_gr_def                            false
% 2.33/0.99  --sat_epr_types                         true
% 2.33/0.99  --sat_non_cyclic_types                  false
% 2.33/0.99  --sat_finite_models                     false
% 2.33/0.99  --sat_fm_lemmas                         false
% 2.33/0.99  --sat_fm_prep                           false
% 2.33/0.99  --sat_fm_uc_incr                        true
% 2.33/0.99  --sat_out_model                         small
% 2.33/0.99  --sat_out_clauses                       false
% 2.33/0.99  
% 2.33/0.99  ------ QBF Options
% 2.33/0.99  
% 2.33/0.99  --qbf_mode                              false
% 2.33/0.99  --qbf_elim_univ                         false
% 2.33/0.99  --qbf_dom_inst                          none
% 2.33/0.99  --qbf_dom_pre_inst                      false
% 2.33/0.99  --qbf_sk_in                             false
% 2.33/0.99  --qbf_pred_elim                         true
% 2.33/0.99  --qbf_split                             512
% 2.33/0.99  
% 2.33/0.99  ------ BMC1 Options
% 2.33/0.99  
% 2.33/0.99  --bmc1_incremental                      false
% 2.33/0.99  --bmc1_axioms                           reachable_all
% 2.33/0.99  --bmc1_min_bound                        0
% 2.33/0.99  --bmc1_max_bound                        -1
% 2.33/0.99  --bmc1_max_bound_default                -1
% 2.33/0.99  --bmc1_symbol_reachability              true
% 2.33/0.99  --bmc1_property_lemmas                  false
% 2.33/0.99  --bmc1_k_induction                      false
% 2.33/0.99  --bmc1_non_equiv_states                 false
% 2.33/0.99  --bmc1_deadlock                         false
% 2.33/0.99  --bmc1_ucm                              false
% 2.33/0.99  --bmc1_add_unsat_core                   none
% 2.33/0.99  --bmc1_unsat_core_children              false
% 2.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.99  --bmc1_out_stat                         full
% 2.33/0.99  --bmc1_ground_init                      false
% 2.33/0.99  --bmc1_pre_inst_next_state              false
% 2.33/0.99  --bmc1_pre_inst_state                   false
% 2.33/0.99  --bmc1_pre_inst_reach_state             false
% 2.33/0.99  --bmc1_out_unsat_core                   false
% 2.33/0.99  --bmc1_aig_witness_out                  false
% 2.33/0.99  --bmc1_verbose                          false
% 2.33/0.99  --bmc1_dump_clauses_tptp                false
% 2.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.99  --bmc1_dump_file                        -
% 2.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.99  --bmc1_ucm_extend_mode                  1
% 2.33/0.99  --bmc1_ucm_init_mode                    2
% 2.33/0.99  --bmc1_ucm_cone_mode                    none
% 2.33/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.99  --bmc1_ucm_relax_model                  4
% 2.33/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.99  --bmc1_ucm_layered_model                none
% 2.33/0.99  --bmc1_ucm_max_lemma_size               10
% 2.33/0.99  
% 2.33/0.99  ------ AIG Options
% 2.33/0.99  
% 2.33/0.99  --aig_mode                              false
% 2.33/0.99  
% 2.33/0.99  ------ Instantiation Options
% 2.33/0.99  
% 2.33/0.99  --instantiation_flag                    true
% 2.33/0.99  --inst_sos_flag                         false
% 2.33/0.99  --inst_sos_phase                        true
% 2.33/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel_side                     num_symb
% 2.33/0.99  --inst_solver_per_active                1400
% 2.33/0.99  --inst_solver_calls_frac                1.
% 2.33/0.99  --inst_passive_queue_type               priority_queues
% 2.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.99  --inst_passive_queues_freq              [25;2]
% 2.33/0.99  --inst_dismatching                      true
% 2.33/0.99  --inst_eager_unprocessed_to_passive     true
% 2.33/0.99  --inst_prop_sim_given                   true
% 2.33/0.99  --inst_prop_sim_new                     false
% 2.33/0.99  --inst_subs_new                         false
% 2.33/0.99  --inst_eq_res_simp                      false
% 2.33/0.99  --inst_subs_given                       false
% 2.33/0.99  --inst_orphan_elimination               true
% 2.33/0.99  --inst_learning_loop_flag               true
% 2.33/0.99  --inst_learning_start                   3000
% 2.33/0.99  --inst_learning_factor                  2
% 2.33/0.99  --inst_start_prop_sim_after_learn       3
% 2.33/0.99  --inst_sel_renew                        solver
% 2.33/0.99  --inst_lit_activity_flag                true
% 2.33/0.99  --inst_restr_to_given                   false
% 2.33/0.99  --inst_activity_threshold               500
% 2.33/0.99  --inst_out_proof                        true
% 2.33/0.99  
% 2.33/0.99  ------ Resolution Options
% 2.33/0.99  
% 2.33/0.99  --resolution_flag                       true
% 2.33/0.99  --res_lit_sel                           adaptive
% 2.33/0.99  --res_lit_sel_side                      none
% 2.33/0.99  --res_ordering                          kbo
% 2.33/0.99  --res_to_prop_solver                    active
% 2.33/0.99  --res_prop_simpl_new                    false
% 2.33/0.99  --res_prop_simpl_given                  true
% 2.33/0.99  --res_passive_queue_type                priority_queues
% 2.33/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.99  --res_passive_queues_freq               [15;5]
% 2.33/0.99  --res_forward_subs                      full
% 2.33/0.99  --res_backward_subs                     full
% 2.33/0.99  --res_forward_subs_resolution           true
% 2.33/0.99  --res_backward_subs_resolution          true
% 2.33/0.99  --res_orphan_elimination                true
% 2.33/0.99  --res_time_limit                        2.
% 2.33/0.99  --res_out_proof                         true
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Options
% 2.33/0.99  
% 2.33/0.99  --superposition_flag                    true
% 2.33/0.99  --sup_passive_queue_type                priority_queues
% 2.33/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.99  --demod_completeness_check              fast
% 2.33/0.99  --demod_use_ground                      true
% 2.33/0.99  --sup_to_prop_solver                    passive
% 2.33/0.99  --sup_prop_simpl_new                    true
% 2.33/0.99  --sup_prop_simpl_given                  true
% 2.33/0.99  --sup_fun_splitting                     false
% 2.33/0.99  --sup_smt_interval                      50000
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Simplification Setup
% 2.33/0.99  
% 2.33/0.99  --sup_indices_passive                   []
% 2.33/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_full_bw                           [BwDemod]
% 2.33/0.99  --sup_immed_triv                        [TrivRules]
% 2.33/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_immed_bw_main                     []
% 2.33/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  
% 2.33/0.99  ------ Combination Options
% 2.33/0.99  
% 2.33/0.99  --comb_res_mult                         3
% 2.33/0.99  --comb_sup_mult                         2
% 2.33/0.99  --comb_inst_mult                        10
% 2.33/0.99  
% 2.33/0.99  ------ Debug Options
% 2.33/0.99  
% 2.33/0.99  --dbg_backtrace                         false
% 2.33/0.99  --dbg_dump_prop_clauses                 false
% 2.33/0.99  --dbg_dump_prop_clauses_file            -
% 2.33/0.99  --dbg_out_stat                          false
% 2.33/0.99  ------ Parsing...
% 2.33/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.99  ------ Proving...
% 2.33/0.99  ------ Problem Properties 
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  clauses                                 25
% 2.33/0.99  conjectures                             3
% 2.33/0.99  EPR                                     4
% 2.33/0.99  Horn                                    24
% 2.33/0.99  unary                                   16
% 2.33/0.99  binary                                  4
% 2.33/0.99  lits                                    45
% 2.33/0.99  lits eq                                 19
% 2.33/0.99  fd_pure                                 0
% 2.33/0.99  fd_pseudo                               0
% 2.33/0.99  fd_cond                                 2
% 2.33/0.99  fd_pseudo_cond                          2
% 2.33/0.99  AC symbols                              0
% 2.33/0.99  
% 2.33/0.99  ------ Schedule dynamic 5 is on 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  ------ 
% 2.33/0.99  Current options:
% 2.33/0.99  ------ 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options
% 2.33/0.99  
% 2.33/0.99  --out_options                           all
% 2.33/0.99  --tptp_safe_out                         true
% 2.33/0.99  --problem_path                          ""
% 2.33/0.99  --include_path                          ""
% 2.33/0.99  --clausifier                            res/vclausify_rel
% 2.33/0.99  --clausifier_options                    --mode clausify
% 2.33/0.99  --stdin                                 false
% 2.33/0.99  --stats_out                             all
% 2.33/1.00  
% 2.33/1.00  ------ General Options
% 2.33/1.00  
% 2.33/1.00  --fof                                   false
% 2.33/1.00  --time_out_real                         305.
% 2.33/1.00  --time_out_virtual                      -1.
% 2.33/1.00  --symbol_type_check                     false
% 2.33/1.00  --clausify_out                          false
% 2.33/1.00  --sig_cnt_out                           false
% 2.33/1.00  --trig_cnt_out                          false
% 2.33/1.00  --trig_cnt_out_tolerance                1.
% 2.33/1.00  --trig_cnt_out_sk_spl                   false
% 2.33/1.00  --abstr_cl_out                          false
% 2.33/1.00  
% 2.33/1.00  ------ Global Options
% 2.33/1.00  
% 2.33/1.00  --schedule                              default
% 2.33/1.00  --add_important_lit                     false
% 2.33/1.00  --prop_solver_per_cl                    1000
% 2.33/1.00  --min_unsat_core                        false
% 2.33/1.00  --soft_assumptions                      false
% 2.33/1.00  --soft_lemma_size                       3
% 2.33/1.00  --prop_impl_unit_size                   0
% 2.33/1.00  --prop_impl_unit                        []
% 2.33/1.00  --share_sel_clauses                     true
% 2.33/1.00  --reset_solvers                         false
% 2.33/1.00  --bc_imp_inh                            [conj_cone]
% 2.33/1.00  --conj_cone_tolerance                   3.
% 2.33/1.00  --extra_neg_conj                        none
% 2.33/1.00  --large_theory_mode                     true
% 2.33/1.00  --prolific_symb_bound                   200
% 2.33/1.00  --lt_threshold                          2000
% 2.33/1.00  --clause_weak_htbl                      true
% 2.33/1.00  --gc_record_bc_elim                     false
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing Options
% 2.33/1.00  
% 2.33/1.00  --preprocessing_flag                    true
% 2.33/1.00  --time_out_prep_mult                    0.1
% 2.33/1.00  --splitting_mode                        input
% 2.33/1.00  --splitting_grd                         true
% 2.33/1.00  --splitting_cvd                         false
% 2.33/1.00  --splitting_cvd_svl                     false
% 2.33/1.00  --splitting_nvd                         32
% 2.33/1.00  --sub_typing                            true
% 2.33/1.00  --prep_gs_sim                           true
% 2.33/1.00  --prep_unflatten                        true
% 2.33/1.00  --prep_res_sim                          true
% 2.33/1.00  --prep_upred                            true
% 2.33/1.00  --prep_sem_filter                       exhaustive
% 2.33/1.00  --prep_sem_filter_out                   false
% 2.33/1.00  --pred_elim                             true
% 2.33/1.00  --res_sim_input                         true
% 2.33/1.00  --eq_ax_congr_red                       true
% 2.33/1.00  --pure_diseq_elim                       true
% 2.33/1.00  --brand_transform                       false
% 2.33/1.00  --non_eq_to_eq                          false
% 2.33/1.00  --prep_def_merge                        true
% 2.33/1.00  --prep_def_merge_prop_impl              false
% 2.33/1.00  --prep_def_merge_mbd                    true
% 2.33/1.00  --prep_def_merge_tr_red                 false
% 2.33/1.00  --prep_def_merge_tr_cl                  false
% 2.33/1.00  --smt_preprocessing                     true
% 2.33/1.00  --smt_ac_axioms                         fast
% 2.33/1.00  --preprocessed_out                      false
% 2.33/1.00  --preprocessed_stats                    false
% 2.33/1.00  
% 2.33/1.00  ------ Abstraction refinement Options
% 2.33/1.00  
% 2.33/1.00  --abstr_ref                             []
% 2.33/1.00  --abstr_ref_prep                        false
% 2.33/1.00  --abstr_ref_until_sat                   false
% 2.33/1.00  --abstr_ref_sig_restrict                funpre
% 2.33/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/1.00  --abstr_ref_under                       []
% 2.33/1.00  
% 2.33/1.00  ------ SAT Options
% 2.33/1.00  
% 2.33/1.00  --sat_mode                              false
% 2.33/1.00  --sat_fm_restart_options                ""
% 2.33/1.00  --sat_gr_def                            false
% 2.33/1.00  --sat_epr_types                         true
% 2.33/1.00  --sat_non_cyclic_types                  false
% 2.33/1.00  --sat_finite_models                     false
% 2.33/1.00  --sat_fm_lemmas                         false
% 2.33/1.00  --sat_fm_prep                           false
% 2.33/1.00  --sat_fm_uc_incr                        true
% 2.33/1.00  --sat_out_model                         small
% 2.33/1.00  --sat_out_clauses                       false
% 2.33/1.00  
% 2.33/1.00  ------ QBF Options
% 2.33/1.00  
% 2.33/1.00  --qbf_mode                              false
% 2.33/1.00  --qbf_elim_univ                         false
% 2.33/1.00  --qbf_dom_inst                          none
% 2.33/1.00  --qbf_dom_pre_inst                      false
% 2.33/1.00  --qbf_sk_in                             false
% 2.33/1.00  --qbf_pred_elim                         true
% 2.33/1.00  --qbf_split                             512
% 2.33/1.00  
% 2.33/1.00  ------ BMC1 Options
% 2.33/1.00  
% 2.33/1.00  --bmc1_incremental                      false
% 2.33/1.00  --bmc1_axioms                           reachable_all
% 2.33/1.00  --bmc1_min_bound                        0
% 2.33/1.00  --bmc1_max_bound                        -1
% 2.33/1.00  --bmc1_max_bound_default                -1
% 2.33/1.00  --bmc1_symbol_reachability              true
% 2.33/1.00  --bmc1_property_lemmas                  false
% 2.33/1.00  --bmc1_k_induction                      false
% 2.33/1.00  --bmc1_non_equiv_states                 false
% 2.33/1.00  --bmc1_deadlock                         false
% 2.33/1.00  --bmc1_ucm                              false
% 2.33/1.00  --bmc1_add_unsat_core                   none
% 2.33/1.00  --bmc1_unsat_core_children              false
% 2.33/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/1.00  --bmc1_out_stat                         full
% 2.33/1.00  --bmc1_ground_init                      false
% 2.33/1.00  --bmc1_pre_inst_next_state              false
% 2.33/1.00  --bmc1_pre_inst_state                   false
% 2.33/1.00  --bmc1_pre_inst_reach_state             false
% 2.33/1.00  --bmc1_out_unsat_core                   false
% 2.33/1.00  --bmc1_aig_witness_out                  false
% 2.33/1.00  --bmc1_verbose                          false
% 2.33/1.00  --bmc1_dump_clauses_tptp                false
% 2.33/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.33/1.00  --bmc1_dump_file                        -
% 2.33/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.33/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.33/1.00  --bmc1_ucm_extend_mode                  1
% 2.33/1.00  --bmc1_ucm_init_mode                    2
% 2.33/1.00  --bmc1_ucm_cone_mode                    none
% 2.33/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.33/1.00  --bmc1_ucm_relax_model                  4
% 2.33/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.33/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/1.00  --bmc1_ucm_layered_model                none
% 2.33/1.00  --bmc1_ucm_max_lemma_size               10
% 2.33/1.00  
% 2.33/1.00  ------ AIG Options
% 2.33/1.00  
% 2.33/1.00  --aig_mode                              false
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation Options
% 2.33/1.00  
% 2.33/1.00  --instantiation_flag                    true
% 2.33/1.00  --inst_sos_flag                         false
% 2.33/1.00  --inst_sos_phase                        true
% 2.33/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/1.00  --inst_lit_sel_side                     none
% 2.33/1.00  --inst_solver_per_active                1400
% 2.33/1.00  --inst_solver_calls_frac                1.
% 2.33/1.00  --inst_passive_queue_type               priority_queues
% 2.33/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/1.00  --inst_passive_queues_freq              [25;2]
% 2.33/1.00  --inst_dismatching                      true
% 2.33/1.00  --inst_eager_unprocessed_to_passive     true
% 2.33/1.00  --inst_prop_sim_given                   true
% 2.33/1.00  --inst_prop_sim_new                     false
% 2.33/1.00  --inst_subs_new                         false
% 2.33/1.00  --inst_eq_res_simp                      false
% 2.33/1.00  --inst_subs_given                       false
% 2.33/1.00  --inst_orphan_elimination               true
% 2.33/1.00  --inst_learning_loop_flag               true
% 2.33/1.00  --inst_learning_start                   3000
% 2.33/1.00  --inst_learning_factor                  2
% 2.33/1.00  --inst_start_prop_sim_after_learn       3
% 2.33/1.00  --inst_sel_renew                        solver
% 2.33/1.00  --inst_lit_activity_flag                true
% 2.33/1.00  --inst_restr_to_given                   false
% 2.33/1.00  --inst_activity_threshold               500
% 2.33/1.00  --inst_out_proof                        true
% 2.33/1.00  
% 2.33/1.00  ------ Resolution Options
% 2.33/1.00  
% 2.33/1.00  --resolution_flag                       false
% 2.33/1.00  --res_lit_sel                           adaptive
% 2.33/1.00  --res_lit_sel_side                      none
% 2.33/1.00  --res_ordering                          kbo
% 2.33/1.00  --res_to_prop_solver                    active
% 2.33/1.00  --res_prop_simpl_new                    false
% 2.33/1.00  --res_prop_simpl_given                  true
% 2.33/1.00  --res_passive_queue_type                priority_queues
% 2.33/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/1.00  --res_passive_queues_freq               [15;5]
% 2.33/1.00  --res_forward_subs                      full
% 2.33/1.00  --res_backward_subs                     full
% 2.33/1.00  --res_forward_subs_resolution           true
% 2.33/1.00  --res_backward_subs_resolution          true
% 2.33/1.00  --res_orphan_elimination                true
% 2.33/1.00  --res_time_limit                        2.
% 2.33/1.00  --res_out_proof                         true
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Options
% 2.33/1.00  
% 2.33/1.00  --superposition_flag                    true
% 2.33/1.00  --sup_passive_queue_type                priority_queues
% 2.33/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.33/1.00  --demod_completeness_check              fast
% 2.33/1.00  --demod_use_ground                      true
% 2.33/1.00  --sup_to_prop_solver                    passive
% 2.33/1.00  --sup_prop_simpl_new                    true
% 2.33/1.00  --sup_prop_simpl_given                  true
% 2.33/1.00  --sup_fun_splitting                     false
% 2.33/1.00  --sup_smt_interval                      50000
% 2.33/1.00  
% 2.33/1.00  ------ Superposition Simplification Setup
% 2.33/1.00  
% 2.33/1.00  --sup_indices_passive                   []
% 2.33/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_full_bw                           [BwDemod]
% 2.33/1.00  --sup_immed_triv                        [TrivRules]
% 2.33/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_immed_bw_main                     []
% 2.33/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/1.00  
% 2.33/1.00  ------ Combination Options
% 2.33/1.00  
% 2.33/1.00  --comb_res_mult                         3
% 2.33/1.00  --comb_sup_mult                         2
% 2.33/1.00  --comb_inst_mult                        10
% 2.33/1.00  
% 2.33/1.00  ------ Debug Options
% 2.33/1.00  
% 2.33/1.00  --dbg_backtrace                         false
% 2.33/1.00  --dbg_dump_prop_clauses                 false
% 2.33/1.00  --dbg_dump_prop_clauses_file            -
% 2.33/1.00  --dbg_out_stat                          false
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  ------ Proving...
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  % SZS status Theorem for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00   Resolution empty clause
% 2.33/1.00  
% 2.33/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  fof(f17,conjecture,(
% 2.33/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f18,negated_conjecture,(
% 2.33/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.33/1.00    inference(negated_conjecture,[],[f17])).
% 2.33/1.00  
% 2.33/1.00  fof(f19,plain,(
% 2.33/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.33/1.00    inference(pure_predicate_removal,[],[f18])).
% 2.33/1.00  
% 2.33/1.00  fof(f32,plain,(
% 2.33/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.33/1.00    inference(ennf_transformation,[],[f19])).
% 2.33/1.00  
% 2.33/1.00  fof(f33,plain,(
% 2.33/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.33/1.00    inference(flattening,[],[f32])).
% 2.33/1.00  
% 2.33/1.00  fof(f39,plain,(
% 2.33/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.33/1.00    introduced(choice_axiom,[])).
% 2.33/1.00  
% 2.33/1.00  fof(f40,plain,(
% 2.33/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.33/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f39])).
% 2.33/1.00  
% 2.33/1.00  fof(f70,plain,(
% 2.33/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.33/1.00    inference(cnf_transformation,[],[f40])).
% 2.33/1.00  
% 2.33/1.00  fof(f3,axiom,(
% 2.33/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f45,plain,(
% 2.33/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f3])).
% 2.33/1.00  
% 2.33/1.00  fof(f4,axiom,(
% 2.33/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f46,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f4])).
% 2.33/1.00  
% 2.33/1.00  fof(f5,axiom,(
% 2.33/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f47,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f5])).
% 2.33/1.00  
% 2.33/1.00  fof(f73,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.33/1.00    inference(definition_unfolding,[],[f46,f47])).
% 2.33/1.00  
% 2.33/1.00  fof(f74,plain,(
% 2.33/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.33/1.00    inference(definition_unfolding,[],[f45,f73])).
% 2.33/1.00  
% 2.33/1.00  fof(f86,plain,(
% 2.33/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.33/1.00    inference(definition_unfolding,[],[f70,f74])).
% 2.33/1.00  
% 2.33/1.00  fof(f15,axiom,(
% 2.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f20,plain,(
% 2.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.33/1.00    inference(pure_predicate_removal,[],[f15])).
% 2.33/1.00  
% 2.33/1.00  fof(f30,plain,(
% 2.33/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/1.00    inference(ennf_transformation,[],[f20])).
% 2.33/1.00  
% 2.33/1.00  fof(f67,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f30])).
% 2.33/1.00  
% 2.33/1.00  fof(f9,axiom,(
% 2.33/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f23,plain,(
% 2.33/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.33/1.00    inference(ennf_transformation,[],[f9])).
% 2.33/1.00  
% 2.33/1.00  fof(f38,plain,(
% 2.33/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.33/1.00    inference(nnf_transformation,[],[f23])).
% 2.33/1.00  
% 2.33/1.00  fof(f58,plain,(
% 2.33/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f38])).
% 2.33/1.00  
% 2.33/1.00  fof(f14,axiom,(
% 2.33/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f29,plain,(
% 2.33/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/1.00    inference(ennf_transformation,[],[f14])).
% 2.33/1.00  
% 2.33/1.00  fof(f66,plain,(
% 2.33/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f29])).
% 2.33/1.00  
% 2.33/1.00  fof(f6,axiom,(
% 2.33/1.00    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f22,plain,(
% 2.33/1.00    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.33/1.00    inference(ennf_transformation,[],[f6])).
% 2.33/1.00  
% 2.33/1.00  fof(f36,plain,(
% 2.33/1.00    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.33/1.00    inference(nnf_transformation,[],[f22])).
% 2.33/1.00  
% 2.33/1.00  fof(f37,plain,(
% 2.33/1.00    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.33/1.00    inference(flattening,[],[f36])).
% 2.33/1.00  
% 2.33/1.00  fof(f48,plain,(
% 2.33/1.00    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f37])).
% 2.33/1.00  
% 2.33/1.00  fof(f83,plain,(
% 2.33/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 2.33/1.00    inference(definition_unfolding,[],[f48,f47,f73,f73,f73,f74,f74,f74,f47])).
% 2.33/1.00  
% 2.33/1.00  fof(f72,plain,(
% 2.33/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.33/1.00    inference(cnf_transformation,[],[f40])).
% 2.33/1.00  
% 2.33/1.00  fof(f85,plain,(
% 2.33/1.00    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.33/1.00    inference(definition_unfolding,[],[f72,f74,f74])).
% 2.33/1.00  
% 2.33/1.00  fof(f16,axiom,(
% 2.33/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f31,plain,(
% 2.33/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/1.00    inference(ennf_transformation,[],[f16])).
% 2.33/1.00  
% 2.33/1.00  fof(f68,plain,(
% 2.33/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f31])).
% 2.33/1.00  
% 2.33/1.00  fof(f10,axiom,(
% 2.33/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f24,plain,(
% 2.33/1.00    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.33/1.00    inference(ennf_transformation,[],[f10])).
% 2.33/1.00  
% 2.33/1.00  fof(f60,plain,(
% 2.33/1.00    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f24])).
% 2.33/1.00  
% 2.33/1.00  fof(f13,axiom,(
% 2.33/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f27,plain,(
% 2.33/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.33/1.00    inference(ennf_transformation,[],[f13])).
% 2.33/1.00  
% 2.33/1.00  fof(f28,plain,(
% 2.33/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.33/1.00    inference(flattening,[],[f27])).
% 2.33/1.00  
% 2.33/1.00  fof(f65,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f28])).
% 2.33/1.00  
% 2.33/1.00  fof(f84,plain,(
% 2.33/1.00    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.33/1.00    inference(definition_unfolding,[],[f65,f74,f74])).
% 2.33/1.00  
% 2.33/1.00  fof(f69,plain,(
% 2.33/1.00    v1_funct_1(sK3)),
% 2.33/1.00    inference(cnf_transformation,[],[f40])).
% 2.33/1.00  
% 2.33/1.00  fof(f12,axiom,(
% 2.33/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f25,plain,(
% 2.33/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.33/1.00    inference(ennf_transformation,[],[f12])).
% 2.33/1.00  
% 2.33/1.00  fof(f26,plain,(
% 2.33/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.33/1.00    inference(flattening,[],[f25])).
% 2.33/1.00  
% 2.33/1.00  fof(f63,plain,(
% 2.33/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f26])).
% 2.33/1.00  
% 2.33/1.00  fof(f11,axiom,(
% 2.33/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f62,plain,(
% 2.33/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.33/1.00    inference(cnf_transformation,[],[f11])).
% 2.33/1.00  
% 2.33/1.00  fof(f7,axiom,(
% 2.33/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f57,plain,(
% 2.33/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.33/1.00    inference(cnf_transformation,[],[f7])).
% 2.33/1.00  
% 2.33/1.00  fof(f2,axiom,(
% 2.33/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f44,plain,(
% 2.33/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f2])).
% 2.33/1.00  
% 2.33/1.00  fof(f1,axiom,(
% 2.33/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.33/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.33/1.00  
% 2.33/1.00  fof(f34,plain,(
% 2.33/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/1.00    inference(nnf_transformation,[],[f1])).
% 2.33/1.00  
% 2.33/1.00  fof(f35,plain,(
% 2.33/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.33/1.00    inference(flattening,[],[f34])).
% 2.33/1.00  
% 2.33/1.00  fof(f43,plain,(
% 2.33/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.33/1.00    inference(cnf_transformation,[],[f35])).
% 2.33/1.00  
% 2.33/1.00  cnf(c_27,negated_conjecture,
% 2.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.33/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1191,plain,
% 2.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_23,plain,
% 2.33/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.33/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_15,plain,
% 2.33/1.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_377,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 2.33/1.00      | ~ v1_relat_1(X0) ),
% 2.33/1.00      inference(resolution,[status(thm)],[c_23,c_15]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_22,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_381,plain,
% 2.33/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.33/1.00      inference(global_propositional_subsumption,[status(thm)],[c_377,c_22]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_382,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_381]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1189,plain,
% 2.33/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.33/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1494,plain,
% 2.33/1.00      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_1191,c_1189]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_12,plain,
% 2.33/1.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 2.33/1.00      | k2_enumset1(X1,X1,X2,X3) = X0
% 2.33/1.00      | k2_enumset1(X1,X1,X1,X3) = X0
% 2.33/1.00      | k2_enumset1(X2,X2,X2,X3) = X0
% 2.33/1.00      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.33/1.00      | k2_enumset1(X3,X3,X3,X3) = X0
% 2.33/1.00      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.33/1.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.33/1.00      | k1_xboole_0 = X0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1199,plain,
% 2.33/1.00      ( k2_enumset1(X0,X0,X1,X2) = X3
% 2.33/1.00      | k2_enumset1(X0,X0,X0,X2) = X3
% 2.33/1.00      | k2_enumset1(X1,X1,X1,X2) = X3
% 2.33/1.00      | k2_enumset1(X0,X0,X0,X1) = X3
% 2.33/1.00      | k2_enumset1(X2,X2,X2,X2) = X3
% 2.33/1.00      | k2_enumset1(X1,X1,X1,X1) = X3
% 2.33/1.00      | k2_enumset1(X0,X0,X0,X0) = X3
% 2.33/1.00      | k1_xboole_0 = X3
% 2.33/1.00      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2762,plain,
% 2.33/1.00      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.33/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_1494,c_1199]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2870,plain,
% 2.33/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 2.33/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2762,c_1191]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_25,negated_conjecture,
% 2.33/1.00      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.33/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1359,plain,
% 2.33/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.33/1.00      | v1_relat_1(sK3) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_24,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.33/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1399,plain,
% 2.33/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.33/1.00      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1445,plain,
% 2.33/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.33/1.00      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_1399]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_812,plain,
% 2.33/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.33/1.00      theory(equality) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1380,plain,
% 2.33/1.00      ( ~ r1_tarski(X0,X1)
% 2.33/1.00      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.33/1.00      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 2.33/1.00      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_812]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1444,plain,
% 2.33/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.33/1.00      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 2.33/1.00      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.33/1.00      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_1380]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1601,plain,
% 2.33/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.33/1.00      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.33/1.00      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.33/1.00      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_1444]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_16,plain,
% 2.33/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1602,plain,
% 2.33/1.00      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_21,plain,
% 2.33/1.00      ( ~ v1_funct_1(X0)
% 2.33/1.00      | ~ v1_relat_1(X0)
% 2.33/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.33/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_28,negated_conjecture,
% 2.33/1.00      ( v1_funct_1(sK3) ),
% 2.33/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_280,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0)
% 2.33/1.00      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.33/1.00      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.33/1.00      | sK3 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_281,plain,
% 2.33/1.00      ( ~ v1_relat_1(sK3)
% 2.33/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.33/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_280]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1190,plain,
% 2.33/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.33/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.33/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_30,plain,
% 2.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_282,plain,
% 2.33/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.33/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.33/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_281]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1360,plain,
% 2.33/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 2.33/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1359]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1373,plain,
% 2.33/1.00      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.33/1.00      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_1190,c_30,c_282,c_1360]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1374,plain,
% 2.33/1.00      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.33/1.00      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_1373]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2864,plain,
% 2.33/1.00      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.33/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2762,c_1374]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2932,plain,
% 2.33/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_2870,c_27,c_25,c_1359,c_1445,c_1601,c_1602,c_2864]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_20,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1195,plain,
% 2.33/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 2.33/1.00      | k1_xboole_0 = X0
% 2.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2950,plain,
% 2.33/1.00      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2932,c_1195]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1459,plain,
% 2.33/1.00      ( ~ v1_relat_1(sK3)
% 2.33/1.00      | k1_relat_1(sK3) != k1_xboole_0
% 2.33/1.00      | k1_xboole_0 = sK3 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_20]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_810,plain,( X0 = X0 ),theory(equality) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1472,plain,
% 2.33/1.00      ( sK3 = sK3 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_810]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_811,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1733,plain,
% 2.33/1.00      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_811]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2286,plain,
% 2.33/1.00      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_1733]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2287,plain,
% 2.33/1.00      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_2286]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3100,plain,
% 2.33/1.00      ( sK3 = k1_xboole_0 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_2950,c_27,c_25,c_1359,c_1445,c_1459,c_1472,c_1601,c_1602,
% 2.33/1.00                 c_2287,c_2864]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1193,plain,
% 2.33/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.33/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2532,plain,
% 2.33/1.00      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_1191,c_1193]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1192,plain,
% 2.33/1.00      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2541,plain,
% 2.33/1.00      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_2532,c_1192]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3104,plain,
% 2.33/1.00      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_3100,c_2541]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_17,plain,
% 2.33/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1197,plain,
% 2.33/1.00      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 2.33/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1932,plain,
% 2.33/1.00      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 2.33/1.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_17,c_1197]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1351,plain,
% 2.33/1.00      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.33/1.00      | v1_relat_1(k1_xboole_0) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1353,plain,
% 2.33/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.33/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1351]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_13,plain,
% 2.33/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.33/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1352,plain,
% 2.33/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1355,plain,
% 2.33/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1352]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2063,plain,
% 2.33/1.00      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_1932,c_1353,c_1355]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3,plain,
% 2.33/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1208,plain,
% 2.33/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_0,plain,
% 2.33/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.33/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1210,plain,
% 2.33/1.00      ( X0 = X1
% 2.33/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.33/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2166,plain,
% 2.33/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_1208,c_1210]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2347,plain,
% 2.33/1.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2063,c_2166]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3112,plain,
% 2.33/1.00      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_3104,c_2347]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3153,plain,
% 2.33/1.00      ( $false ),
% 2.33/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3112,c_1208]) ).
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  ------                               Statistics
% 2.33/1.00  
% 2.33/1.00  ------ General
% 2.33/1.00  
% 2.33/1.00  abstr_ref_over_cycles:                  0
% 2.33/1.00  abstr_ref_under_cycles:                 0
% 2.33/1.00  gc_basic_clause_elim:                   0
% 2.33/1.00  forced_gc_time:                         0
% 2.33/1.00  parsing_time:                           0.009
% 2.33/1.00  unif_index_cands_time:                  0.
% 2.33/1.00  unif_index_add_time:                    0.
% 2.33/1.00  orderings_time:                         0.
% 2.33/1.00  out_proof_time:                         0.024
% 2.33/1.00  total_time:                             0.148
% 2.33/1.00  num_of_symbols:                         49
% 2.33/1.00  num_of_terms:                           2762
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing
% 2.33/1.00  
% 2.33/1.00  num_of_splits:                          0
% 2.33/1.00  num_of_split_atoms:                     0
% 2.33/1.00  num_of_reused_defs:                     0
% 2.33/1.00  num_eq_ax_congr_red:                    9
% 2.33/1.00  num_of_sem_filtered_clauses:            1
% 2.33/1.00  num_of_subtypes:                        0
% 2.33/1.00  monotx_restored_types:                  0
% 2.33/1.00  sat_num_of_epr_types:                   0
% 2.33/1.00  sat_num_of_non_cyclic_types:            0
% 2.33/1.00  sat_guarded_non_collapsed_types:        0
% 2.33/1.00  num_pure_diseq_elim:                    0
% 2.33/1.00  simp_replaced_by:                       0
% 2.33/1.00  res_preprocessed:                       128
% 2.33/1.00  prep_upred:                             0
% 2.33/1.00  prep_unflattend:                        21
% 2.33/1.00  smt_new_axioms:                         0
% 2.33/1.00  pred_elim_cands:                        3
% 2.33/1.00  pred_elim:                              2
% 2.33/1.00  pred_elim_cl:                           3
% 2.33/1.00  pred_elim_cycles:                       7
% 2.33/1.00  merged_defs:                            0
% 2.33/1.00  merged_defs_ncl:                        0
% 2.33/1.00  bin_hyper_res:                          0
% 2.33/1.00  prep_cycles:                            4
% 2.33/1.00  pred_elim_time:                         0.006
% 2.33/1.00  splitting_time:                         0.
% 2.33/1.00  sem_filter_time:                        0.
% 2.33/1.00  monotx_time:                            0.
% 2.33/1.00  subtype_inf_time:                       0.
% 2.33/1.00  
% 2.33/1.00  ------ Problem properties
% 2.33/1.00  
% 2.33/1.00  clauses:                                25
% 2.33/1.00  conjectures:                            3
% 2.33/1.00  epr:                                    4
% 2.33/1.00  horn:                                   24
% 2.33/1.00  ground:                                 5
% 2.33/1.00  unary:                                  16
% 2.33/1.00  binary:                                 4
% 2.33/1.00  lits:                                   45
% 2.33/1.00  lits_eq:                                19
% 2.33/1.00  fd_pure:                                0
% 2.33/1.00  fd_pseudo:                              0
% 2.33/1.00  fd_cond:                                2
% 2.33/1.00  fd_pseudo_cond:                         2
% 2.33/1.00  ac_symbols:                             0
% 2.33/1.00  
% 2.33/1.00  ------ Propositional Solver
% 2.33/1.00  
% 2.33/1.00  prop_solver_calls:                      27
% 2.33/1.00  prop_fast_solver_calls:                 675
% 2.33/1.00  smt_solver_calls:                       0
% 2.33/1.00  smt_fast_solver_calls:                  0
% 2.33/1.00  prop_num_of_clauses:                    1070
% 2.33/1.00  prop_preprocess_simplified:             4676
% 2.33/1.00  prop_fo_subsumed:                       7
% 2.33/1.00  prop_solver_time:                       0.
% 2.33/1.00  smt_solver_time:                        0.
% 2.33/1.00  smt_fast_solver_time:                   0.
% 2.33/1.00  prop_fast_solver_time:                  0.
% 2.33/1.00  prop_unsat_core_time:                   0.
% 2.33/1.00  
% 2.33/1.00  ------ QBF
% 2.33/1.00  
% 2.33/1.00  qbf_q_res:                              0
% 2.33/1.00  qbf_num_tautologies:                    0
% 2.33/1.00  qbf_prep_cycles:                        0
% 2.33/1.00  
% 2.33/1.00  ------ BMC1
% 2.33/1.00  
% 2.33/1.00  bmc1_current_bound:                     -1
% 2.33/1.00  bmc1_last_solved_bound:                 -1
% 2.33/1.00  bmc1_unsat_core_size:                   -1
% 2.33/1.00  bmc1_unsat_core_parents_size:           -1
% 2.33/1.00  bmc1_merge_next_fun:                    0
% 2.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation
% 2.33/1.00  
% 2.33/1.00  inst_num_of_clauses:                    342
% 2.33/1.00  inst_num_in_passive:                    150
% 2.33/1.00  inst_num_in_active:                     186
% 2.33/1.00  inst_num_in_unprocessed:                6
% 2.33/1.00  inst_num_of_loops:                      200
% 2.33/1.00  inst_num_of_learning_restarts:          0
% 2.33/1.00  inst_num_moves_active_passive:          11
% 2.33/1.00  inst_lit_activity:                      0
% 2.33/1.00  inst_lit_activity_moves:                0
% 2.33/1.00  inst_num_tautologies:                   0
% 2.33/1.00  inst_num_prop_implied:                  0
% 2.33/1.00  inst_num_existing_simplified:           0
% 2.33/1.00  inst_num_eq_res_simplified:             0
% 2.33/1.00  inst_num_child_elim:                    0
% 2.33/1.00  inst_num_of_dismatching_blockings:      49
% 2.33/1.00  inst_num_of_non_proper_insts:           286
% 2.33/1.00  inst_num_of_duplicates:                 0
% 2.33/1.00  inst_inst_num_from_inst_to_res:         0
% 2.33/1.00  inst_dismatching_checking_time:         0.
% 2.33/1.00  
% 2.33/1.00  ------ Resolution
% 2.33/1.00  
% 2.33/1.00  res_num_of_clauses:                     0
% 2.33/1.00  res_num_in_passive:                     0
% 2.33/1.00  res_num_in_active:                      0
% 2.33/1.00  res_num_of_loops:                       132
% 2.33/1.00  res_forward_subset_subsumed:            51
% 2.33/1.00  res_backward_subset_subsumed:           0
% 2.33/1.00  res_forward_subsumed:                   0
% 2.33/1.00  res_backward_subsumed:                  0
% 2.33/1.00  res_forward_subsumption_resolution:     0
% 2.33/1.00  res_backward_subsumption_resolution:    0
% 2.33/1.00  res_clause_to_clause_subsumption:       226
% 2.33/1.00  res_orphan_elimination:                 0
% 2.33/1.00  res_tautology_del:                      19
% 2.33/1.00  res_num_eq_res_simplified:              0
% 2.33/1.00  res_num_sel_changes:                    0
% 2.33/1.00  res_moves_from_active_to_pass:          0
% 2.33/1.00  
% 2.33/1.00  ------ Superposition
% 2.33/1.00  
% 2.33/1.00  sup_time_total:                         0.
% 2.33/1.00  sup_time_generating:                    0.
% 2.33/1.00  sup_time_sim_full:                      0.
% 2.33/1.00  sup_time_sim_immed:                     0.
% 2.33/1.00  
% 2.33/1.00  sup_num_of_clauses:                     38
% 2.33/1.00  sup_num_in_active:                      28
% 2.33/1.00  sup_num_in_passive:                     10
% 2.33/1.00  sup_num_of_loops:                       39
% 2.33/1.00  sup_fw_superposition:                   38
% 2.33/1.00  sup_bw_superposition:                   23
% 2.33/1.00  sup_immediate_simplified:               13
% 2.33/1.00  sup_given_eliminated:                   0
% 2.33/1.00  comparisons_done:                       0
% 2.33/1.00  comparisons_avoided:                    0
% 2.33/1.00  
% 2.33/1.00  ------ Simplifications
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  sim_fw_subset_subsumed:                 1
% 2.33/1.00  sim_bw_subset_subsumed:                 5
% 2.33/1.00  sim_fw_subsumed:                        11
% 2.33/1.00  sim_bw_subsumed:                        0
% 2.33/1.00  sim_fw_subsumption_res:                 1
% 2.33/1.00  sim_bw_subsumption_res:                 0
% 2.33/1.00  sim_tautology_del:                      0
% 2.33/1.00  sim_eq_tautology_del:                   15
% 2.33/1.00  sim_eq_res_simp:                        0
% 2.33/1.00  sim_fw_demodulated:                     2
% 2.33/1.00  sim_bw_demodulated:                     11
% 2.33/1.00  sim_light_normalised:                   4
% 2.33/1.00  sim_joinable_taut:                      0
% 2.33/1.00  sim_joinable_simp:                      0
% 2.33/1.00  sim_ac_normalised:                      0
% 2.33/1.00  sim_smt_subsumption:                    0
% 2.33/1.00  
%------------------------------------------------------------------------------
