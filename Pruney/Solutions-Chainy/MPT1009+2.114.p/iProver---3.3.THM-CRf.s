%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:51 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  163 (1026 expanded)
%              Number of clauses        :   86 ( 300 expanded)
%              Number of leaves         :   19 ( 227 expanded)
%              Depth                    :   26
%              Number of atoms          :  405 (2428 expanded)
%              Number of equality atoms :  179 ( 932 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f47])).

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

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f45])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f79,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f80,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f79])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f76,f80])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f80,f80])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f69,f80,f80])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f78,f80,f80])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_1(X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f92,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1543,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_16,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_16])).

cnf(c_1531,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_384])).

cnf(c_2174,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_1531])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1540,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2047,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1540])).

cnf(c_2223,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2174,c_2047])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1541,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2233,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1543,c_1541])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1548,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3309,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2233,c_1548])).

cnf(c_3442,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2223,c_3309])).

cnf(c_18,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1539,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5940,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3442,c_1539])).

cnf(c_6692,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5940,c_2047])).

cnf(c_6704,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6692,c_3309])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1547,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1536,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_21,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_21,c_14])).

cnf(c_1532,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_365])).

cnf(c_2463,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1536,c_1532])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_1837,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2077,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1837])).

cnf(c_2078,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2077])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_200,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_201,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_200])).

cnf(c_245,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_201])).

cnf(c_1684,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_245])).

cnf(c_2156,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1684])).

cnf(c_2157,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2156])).

cnf(c_2262,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2263,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2262])).

cnf(c_2705,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2463,c_30,c_2078,c_2157,c_2263])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1544,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4207,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2705,c_1544])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_342,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_343,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_1533,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_4555,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4207,c_1533])).

cnf(c_4598,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4555])).

cnf(c_4689,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4555,c_27,c_2077,c_2156,c_2262,c_4598])).

cnf(c_4690,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4689])).

cnf(c_4695,plain,
    ( k2_enumset1(k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0))) = k2_relat_1(sK3)
    | k2_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4690,c_1533])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1538,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3567,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1536,c_1538])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1537,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3793,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3567,c_1537])).

cnf(c_4696,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4690,c_3793])).

cnf(c_4858,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1539,c_4696])).

cnf(c_4861,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4695,c_30,c_2078,c_2157,c_2263,c_4858])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_327,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_328,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_327])).

cnf(c_1534,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_328])).

cnf(c_2235,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1534,c_1541])).

cnf(c_2365,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2235,c_30,c_2078,c_2157,c_2263])).

cnf(c_2366,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2365])).

cnf(c_2658,plain,
    ( k2_zfmisc_1(k1_relat_1(sK3),X0) = sK3
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),X0),sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2366,c_1548])).

cnf(c_4869,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = sK3
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,X0),sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4861,c_2658])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4901,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4869,c_7])).

cnf(c_5172,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4901,c_2233])).

cnf(c_5176,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1547,c_5172])).

cnf(c_5332,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5176,c_3793])).

cnf(c_7124,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6704,c_5332])).

cnf(c_7135,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_7124,c_2233])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.00/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.00/1.01  
% 3.00/1.01  ------  iProver source info
% 3.00/1.01  
% 3.00/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.00/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.00/1.01  git: non_committed_changes: false
% 3.00/1.01  git: last_make_outside_of_git: false
% 3.00/1.01  
% 3.00/1.01  ------ 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options
% 3.00/1.01  
% 3.00/1.01  --out_options                           all
% 3.00/1.01  --tptp_safe_out                         true
% 3.00/1.01  --problem_path                          ""
% 3.00/1.01  --include_path                          ""
% 3.00/1.01  --clausifier                            res/vclausify_rel
% 3.00/1.01  --clausifier_options                    --mode clausify
% 3.00/1.01  --stdin                                 false
% 3.00/1.01  --stats_out                             all
% 3.00/1.01  
% 3.00/1.01  ------ General Options
% 3.00/1.01  
% 3.00/1.01  --fof                                   false
% 3.00/1.01  --time_out_real                         305.
% 3.00/1.01  --time_out_virtual                      -1.
% 3.00/1.01  --symbol_type_check                     false
% 3.00/1.01  --clausify_out                          false
% 3.00/1.01  --sig_cnt_out                           false
% 3.00/1.01  --trig_cnt_out                          false
% 3.00/1.01  --trig_cnt_out_tolerance                1.
% 3.00/1.01  --trig_cnt_out_sk_spl                   false
% 3.00/1.01  --abstr_cl_out                          false
% 3.00/1.01  
% 3.00/1.01  ------ Global Options
% 3.00/1.01  
% 3.00/1.01  --schedule                              default
% 3.00/1.01  --add_important_lit                     false
% 3.00/1.01  --prop_solver_per_cl                    1000
% 3.00/1.01  --min_unsat_core                        false
% 3.00/1.01  --soft_assumptions                      false
% 3.00/1.01  --soft_lemma_size                       3
% 3.00/1.01  --prop_impl_unit_size                   0
% 3.00/1.01  --prop_impl_unit                        []
% 3.00/1.01  --share_sel_clauses                     true
% 3.00/1.01  --reset_solvers                         false
% 3.00/1.01  --bc_imp_inh                            [conj_cone]
% 3.00/1.01  --conj_cone_tolerance                   3.
% 3.00/1.01  --extra_neg_conj                        none
% 3.00/1.01  --large_theory_mode                     true
% 3.00/1.01  --prolific_symb_bound                   200
% 3.00/1.01  --lt_threshold                          2000
% 3.00/1.01  --clause_weak_htbl                      true
% 3.00/1.01  --gc_record_bc_elim                     false
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing Options
% 3.00/1.01  
% 3.00/1.01  --preprocessing_flag                    true
% 3.00/1.01  --time_out_prep_mult                    0.1
% 3.00/1.01  --splitting_mode                        input
% 3.00/1.01  --splitting_grd                         true
% 3.00/1.01  --splitting_cvd                         false
% 3.00/1.01  --splitting_cvd_svl                     false
% 3.00/1.01  --splitting_nvd                         32
% 3.00/1.01  --sub_typing                            true
% 3.00/1.01  --prep_gs_sim                           true
% 3.00/1.01  --prep_unflatten                        true
% 3.00/1.01  --prep_res_sim                          true
% 3.00/1.01  --prep_upred                            true
% 3.00/1.01  --prep_sem_filter                       exhaustive
% 3.00/1.01  --prep_sem_filter_out                   false
% 3.00/1.01  --pred_elim                             true
% 3.00/1.01  --res_sim_input                         true
% 3.00/1.01  --eq_ax_congr_red                       true
% 3.00/1.01  --pure_diseq_elim                       true
% 3.00/1.01  --brand_transform                       false
% 3.00/1.01  --non_eq_to_eq                          false
% 3.00/1.01  --prep_def_merge                        true
% 3.00/1.01  --prep_def_merge_prop_impl              false
% 3.00/1.01  --prep_def_merge_mbd                    true
% 3.00/1.01  --prep_def_merge_tr_red                 false
% 3.00/1.01  --prep_def_merge_tr_cl                  false
% 3.00/1.01  --smt_preprocessing                     true
% 3.00/1.01  --smt_ac_axioms                         fast
% 3.00/1.01  --preprocessed_out                      false
% 3.00/1.01  --preprocessed_stats                    false
% 3.00/1.01  
% 3.00/1.01  ------ Abstraction refinement Options
% 3.00/1.01  
% 3.00/1.01  --abstr_ref                             []
% 3.00/1.01  --abstr_ref_prep                        false
% 3.00/1.01  --abstr_ref_until_sat                   false
% 3.00/1.01  --abstr_ref_sig_restrict                funpre
% 3.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.01  --abstr_ref_under                       []
% 3.00/1.01  
% 3.00/1.01  ------ SAT Options
% 3.00/1.01  
% 3.00/1.01  --sat_mode                              false
% 3.00/1.01  --sat_fm_restart_options                ""
% 3.00/1.01  --sat_gr_def                            false
% 3.00/1.01  --sat_epr_types                         true
% 3.00/1.01  --sat_non_cyclic_types                  false
% 3.00/1.01  --sat_finite_models                     false
% 3.00/1.01  --sat_fm_lemmas                         false
% 3.00/1.01  --sat_fm_prep                           false
% 3.00/1.01  --sat_fm_uc_incr                        true
% 3.00/1.01  --sat_out_model                         small
% 3.00/1.01  --sat_out_clauses                       false
% 3.00/1.01  
% 3.00/1.01  ------ QBF Options
% 3.00/1.01  
% 3.00/1.01  --qbf_mode                              false
% 3.00/1.01  --qbf_elim_univ                         false
% 3.00/1.01  --qbf_dom_inst                          none
% 3.00/1.01  --qbf_dom_pre_inst                      false
% 3.00/1.01  --qbf_sk_in                             false
% 3.00/1.01  --qbf_pred_elim                         true
% 3.00/1.01  --qbf_split                             512
% 3.00/1.01  
% 3.00/1.01  ------ BMC1 Options
% 3.00/1.01  
% 3.00/1.01  --bmc1_incremental                      false
% 3.00/1.01  --bmc1_axioms                           reachable_all
% 3.00/1.01  --bmc1_min_bound                        0
% 3.00/1.01  --bmc1_max_bound                        -1
% 3.00/1.01  --bmc1_max_bound_default                -1
% 3.00/1.01  --bmc1_symbol_reachability              true
% 3.00/1.01  --bmc1_property_lemmas                  false
% 3.00/1.01  --bmc1_k_induction                      false
% 3.00/1.01  --bmc1_non_equiv_states                 false
% 3.00/1.01  --bmc1_deadlock                         false
% 3.00/1.01  --bmc1_ucm                              false
% 3.00/1.01  --bmc1_add_unsat_core                   none
% 3.00/1.01  --bmc1_unsat_core_children              false
% 3.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.01  --bmc1_out_stat                         full
% 3.00/1.01  --bmc1_ground_init                      false
% 3.00/1.01  --bmc1_pre_inst_next_state              false
% 3.00/1.01  --bmc1_pre_inst_state                   false
% 3.00/1.01  --bmc1_pre_inst_reach_state             false
% 3.00/1.01  --bmc1_out_unsat_core                   false
% 3.00/1.01  --bmc1_aig_witness_out                  false
% 3.00/1.01  --bmc1_verbose                          false
% 3.00/1.01  --bmc1_dump_clauses_tptp                false
% 3.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.01  --bmc1_dump_file                        -
% 3.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.01  --bmc1_ucm_extend_mode                  1
% 3.00/1.01  --bmc1_ucm_init_mode                    2
% 3.00/1.01  --bmc1_ucm_cone_mode                    none
% 3.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.01  --bmc1_ucm_relax_model                  4
% 3.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.01  --bmc1_ucm_layered_model                none
% 3.00/1.01  --bmc1_ucm_max_lemma_size               10
% 3.00/1.01  
% 3.00/1.01  ------ AIG Options
% 3.00/1.01  
% 3.00/1.01  --aig_mode                              false
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation Options
% 3.00/1.01  
% 3.00/1.01  --instantiation_flag                    true
% 3.00/1.01  --inst_sos_flag                         false
% 3.00/1.01  --inst_sos_phase                        true
% 3.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel_side                     num_symb
% 3.00/1.01  --inst_solver_per_active                1400
% 3.00/1.01  --inst_solver_calls_frac                1.
% 3.00/1.01  --inst_passive_queue_type               priority_queues
% 3.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.01  --inst_passive_queues_freq              [25;2]
% 3.00/1.01  --inst_dismatching                      true
% 3.00/1.01  --inst_eager_unprocessed_to_passive     true
% 3.00/1.01  --inst_prop_sim_given                   true
% 3.00/1.01  --inst_prop_sim_new                     false
% 3.00/1.01  --inst_subs_new                         false
% 3.00/1.01  --inst_eq_res_simp                      false
% 3.00/1.01  --inst_subs_given                       false
% 3.00/1.01  --inst_orphan_elimination               true
% 3.00/1.01  --inst_learning_loop_flag               true
% 3.00/1.01  --inst_learning_start                   3000
% 3.00/1.01  --inst_learning_factor                  2
% 3.00/1.01  --inst_start_prop_sim_after_learn       3
% 3.00/1.01  --inst_sel_renew                        solver
% 3.00/1.01  --inst_lit_activity_flag                true
% 3.00/1.01  --inst_restr_to_given                   false
% 3.00/1.01  --inst_activity_threshold               500
% 3.00/1.01  --inst_out_proof                        true
% 3.00/1.01  
% 3.00/1.01  ------ Resolution Options
% 3.00/1.01  
% 3.00/1.01  --resolution_flag                       true
% 3.00/1.01  --res_lit_sel                           adaptive
% 3.00/1.01  --res_lit_sel_side                      none
% 3.00/1.01  --res_ordering                          kbo
% 3.00/1.01  --res_to_prop_solver                    active
% 3.00/1.01  --res_prop_simpl_new                    false
% 3.00/1.01  --res_prop_simpl_given                  true
% 3.00/1.01  --res_passive_queue_type                priority_queues
% 3.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.01  --res_passive_queues_freq               [15;5]
% 3.00/1.01  --res_forward_subs                      full
% 3.00/1.01  --res_backward_subs                     full
% 3.00/1.01  --res_forward_subs_resolution           true
% 3.00/1.01  --res_backward_subs_resolution          true
% 3.00/1.01  --res_orphan_elimination                true
% 3.00/1.01  --res_time_limit                        2.
% 3.00/1.01  --res_out_proof                         true
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Options
% 3.00/1.01  
% 3.00/1.01  --superposition_flag                    true
% 3.00/1.01  --sup_passive_queue_type                priority_queues
% 3.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.01  --demod_completeness_check              fast
% 3.00/1.01  --demod_use_ground                      true
% 3.00/1.01  --sup_to_prop_solver                    passive
% 3.00/1.01  --sup_prop_simpl_new                    true
% 3.00/1.01  --sup_prop_simpl_given                  true
% 3.00/1.01  --sup_fun_splitting                     false
% 3.00/1.01  --sup_smt_interval                      50000
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Simplification Setup
% 3.00/1.01  
% 3.00/1.01  --sup_indices_passive                   []
% 3.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_full_bw                           [BwDemod]
% 3.00/1.01  --sup_immed_triv                        [TrivRules]
% 3.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_immed_bw_main                     []
% 3.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  
% 3.00/1.01  ------ Combination Options
% 3.00/1.01  
% 3.00/1.01  --comb_res_mult                         3
% 3.00/1.01  --comb_sup_mult                         2
% 3.00/1.01  --comb_inst_mult                        10
% 3.00/1.01  
% 3.00/1.01  ------ Debug Options
% 3.00/1.01  
% 3.00/1.01  --dbg_backtrace                         false
% 3.00/1.01  --dbg_dump_prop_clauses                 false
% 3.00/1.01  --dbg_dump_prop_clauses_file            -
% 3.00/1.01  --dbg_out_stat                          false
% 3.00/1.01  ------ Parsing...
% 3.00/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.00/1.01  ------ Proving...
% 3.00/1.01  ------ Problem Properties 
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  clauses                                 22
% 3.00/1.01  conjectures                             3
% 3.00/1.01  EPR                                     4
% 3.00/1.01  Horn                                    20
% 3.00/1.01  unary                                   10
% 3.00/1.01  binary                                  4
% 3.00/1.01  lits                                    42
% 3.00/1.01  lits eq                                 12
% 3.00/1.01  fd_pure                                 0
% 3.00/1.01  fd_pseudo                               0
% 3.00/1.01  fd_cond                                 1
% 3.00/1.01  fd_pseudo_cond                          2
% 3.00/1.01  AC symbols                              0
% 3.00/1.01  
% 3.00/1.01  ------ Schedule dynamic 5 is on 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  ------ 
% 3.00/1.01  Current options:
% 3.00/1.01  ------ 
% 3.00/1.01  
% 3.00/1.01  ------ Input Options
% 3.00/1.01  
% 3.00/1.01  --out_options                           all
% 3.00/1.01  --tptp_safe_out                         true
% 3.00/1.01  --problem_path                          ""
% 3.00/1.01  --include_path                          ""
% 3.00/1.01  --clausifier                            res/vclausify_rel
% 3.00/1.01  --clausifier_options                    --mode clausify
% 3.00/1.01  --stdin                                 false
% 3.00/1.01  --stats_out                             all
% 3.00/1.01  
% 3.00/1.01  ------ General Options
% 3.00/1.01  
% 3.00/1.01  --fof                                   false
% 3.00/1.01  --time_out_real                         305.
% 3.00/1.01  --time_out_virtual                      -1.
% 3.00/1.01  --symbol_type_check                     false
% 3.00/1.01  --clausify_out                          false
% 3.00/1.01  --sig_cnt_out                           false
% 3.00/1.01  --trig_cnt_out                          false
% 3.00/1.01  --trig_cnt_out_tolerance                1.
% 3.00/1.01  --trig_cnt_out_sk_spl                   false
% 3.00/1.01  --abstr_cl_out                          false
% 3.00/1.01  
% 3.00/1.01  ------ Global Options
% 3.00/1.01  
% 3.00/1.01  --schedule                              default
% 3.00/1.01  --add_important_lit                     false
% 3.00/1.01  --prop_solver_per_cl                    1000
% 3.00/1.01  --min_unsat_core                        false
% 3.00/1.01  --soft_assumptions                      false
% 3.00/1.01  --soft_lemma_size                       3
% 3.00/1.01  --prop_impl_unit_size                   0
% 3.00/1.01  --prop_impl_unit                        []
% 3.00/1.01  --share_sel_clauses                     true
% 3.00/1.01  --reset_solvers                         false
% 3.00/1.01  --bc_imp_inh                            [conj_cone]
% 3.00/1.01  --conj_cone_tolerance                   3.
% 3.00/1.01  --extra_neg_conj                        none
% 3.00/1.01  --large_theory_mode                     true
% 3.00/1.01  --prolific_symb_bound                   200
% 3.00/1.01  --lt_threshold                          2000
% 3.00/1.01  --clause_weak_htbl                      true
% 3.00/1.01  --gc_record_bc_elim                     false
% 3.00/1.01  
% 3.00/1.01  ------ Preprocessing Options
% 3.00/1.01  
% 3.00/1.01  --preprocessing_flag                    true
% 3.00/1.01  --time_out_prep_mult                    0.1
% 3.00/1.01  --splitting_mode                        input
% 3.00/1.01  --splitting_grd                         true
% 3.00/1.01  --splitting_cvd                         false
% 3.00/1.01  --splitting_cvd_svl                     false
% 3.00/1.01  --splitting_nvd                         32
% 3.00/1.01  --sub_typing                            true
% 3.00/1.01  --prep_gs_sim                           true
% 3.00/1.01  --prep_unflatten                        true
% 3.00/1.01  --prep_res_sim                          true
% 3.00/1.01  --prep_upred                            true
% 3.00/1.01  --prep_sem_filter                       exhaustive
% 3.00/1.01  --prep_sem_filter_out                   false
% 3.00/1.01  --pred_elim                             true
% 3.00/1.01  --res_sim_input                         true
% 3.00/1.01  --eq_ax_congr_red                       true
% 3.00/1.01  --pure_diseq_elim                       true
% 3.00/1.01  --brand_transform                       false
% 3.00/1.01  --non_eq_to_eq                          false
% 3.00/1.01  --prep_def_merge                        true
% 3.00/1.01  --prep_def_merge_prop_impl              false
% 3.00/1.01  --prep_def_merge_mbd                    true
% 3.00/1.01  --prep_def_merge_tr_red                 false
% 3.00/1.01  --prep_def_merge_tr_cl                  false
% 3.00/1.01  --smt_preprocessing                     true
% 3.00/1.01  --smt_ac_axioms                         fast
% 3.00/1.01  --preprocessed_out                      false
% 3.00/1.01  --preprocessed_stats                    false
% 3.00/1.01  
% 3.00/1.01  ------ Abstraction refinement Options
% 3.00/1.01  
% 3.00/1.01  --abstr_ref                             []
% 3.00/1.01  --abstr_ref_prep                        false
% 3.00/1.01  --abstr_ref_until_sat                   false
% 3.00/1.01  --abstr_ref_sig_restrict                funpre
% 3.00/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.00/1.01  --abstr_ref_under                       []
% 3.00/1.01  
% 3.00/1.01  ------ SAT Options
% 3.00/1.01  
% 3.00/1.01  --sat_mode                              false
% 3.00/1.01  --sat_fm_restart_options                ""
% 3.00/1.01  --sat_gr_def                            false
% 3.00/1.01  --sat_epr_types                         true
% 3.00/1.01  --sat_non_cyclic_types                  false
% 3.00/1.01  --sat_finite_models                     false
% 3.00/1.01  --sat_fm_lemmas                         false
% 3.00/1.01  --sat_fm_prep                           false
% 3.00/1.01  --sat_fm_uc_incr                        true
% 3.00/1.01  --sat_out_model                         small
% 3.00/1.01  --sat_out_clauses                       false
% 3.00/1.01  
% 3.00/1.01  ------ QBF Options
% 3.00/1.01  
% 3.00/1.01  --qbf_mode                              false
% 3.00/1.01  --qbf_elim_univ                         false
% 3.00/1.01  --qbf_dom_inst                          none
% 3.00/1.01  --qbf_dom_pre_inst                      false
% 3.00/1.01  --qbf_sk_in                             false
% 3.00/1.01  --qbf_pred_elim                         true
% 3.00/1.01  --qbf_split                             512
% 3.00/1.01  
% 3.00/1.01  ------ BMC1 Options
% 3.00/1.01  
% 3.00/1.01  --bmc1_incremental                      false
% 3.00/1.01  --bmc1_axioms                           reachable_all
% 3.00/1.01  --bmc1_min_bound                        0
% 3.00/1.01  --bmc1_max_bound                        -1
% 3.00/1.01  --bmc1_max_bound_default                -1
% 3.00/1.01  --bmc1_symbol_reachability              true
% 3.00/1.01  --bmc1_property_lemmas                  false
% 3.00/1.01  --bmc1_k_induction                      false
% 3.00/1.01  --bmc1_non_equiv_states                 false
% 3.00/1.01  --bmc1_deadlock                         false
% 3.00/1.01  --bmc1_ucm                              false
% 3.00/1.01  --bmc1_add_unsat_core                   none
% 3.00/1.01  --bmc1_unsat_core_children              false
% 3.00/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.00/1.01  --bmc1_out_stat                         full
% 3.00/1.01  --bmc1_ground_init                      false
% 3.00/1.01  --bmc1_pre_inst_next_state              false
% 3.00/1.01  --bmc1_pre_inst_state                   false
% 3.00/1.01  --bmc1_pre_inst_reach_state             false
% 3.00/1.01  --bmc1_out_unsat_core                   false
% 3.00/1.01  --bmc1_aig_witness_out                  false
% 3.00/1.01  --bmc1_verbose                          false
% 3.00/1.01  --bmc1_dump_clauses_tptp                false
% 3.00/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.00/1.01  --bmc1_dump_file                        -
% 3.00/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.00/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.00/1.01  --bmc1_ucm_extend_mode                  1
% 3.00/1.01  --bmc1_ucm_init_mode                    2
% 3.00/1.01  --bmc1_ucm_cone_mode                    none
% 3.00/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.00/1.01  --bmc1_ucm_relax_model                  4
% 3.00/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.00/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.00/1.01  --bmc1_ucm_layered_model                none
% 3.00/1.01  --bmc1_ucm_max_lemma_size               10
% 3.00/1.01  
% 3.00/1.01  ------ AIG Options
% 3.00/1.01  
% 3.00/1.01  --aig_mode                              false
% 3.00/1.01  
% 3.00/1.01  ------ Instantiation Options
% 3.00/1.01  
% 3.00/1.01  --instantiation_flag                    true
% 3.00/1.01  --inst_sos_flag                         false
% 3.00/1.01  --inst_sos_phase                        true
% 3.00/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.00/1.01  --inst_lit_sel_side                     none
% 3.00/1.01  --inst_solver_per_active                1400
% 3.00/1.01  --inst_solver_calls_frac                1.
% 3.00/1.01  --inst_passive_queue_type               priority_queues
% 3.00/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.00/1.01  --inst_passive_queues_freq              [25;2]
% 3.00/1.01  --inst_dismatching                      true
% 3.00/1.01  --inst_eager_unprocessed_to_passive     true
% 3.00/1.01  --inst_prop_sim_given                   true
% 3.00/1.01  --inst_prop_sim_new                     false
% 3.00/1.01  --inst_subs_new                         false
% 3.00/1.01  --inst_eq_res_simp                      false
% 3.00/1.01  --inst_subs_given                       false
% 3.00/1.01  --inst_orphan_elimination               true
% 3.00/1.01  --inst_learning_loop_flag               true
% 3.00/1.01  --inst_learning_start                   3000
% 3.00/1.01  --inst_learning_factor                  2
% 3.00/1.01  --inst_start_prop_sim_after_learn       3
% 3.00/1.01  --inst_sel_renew                        solver
% 3.00/1.01  --inst_lit_activity_flag                true
% 3.00/1.01  --inst_restr_to_given                   false
% 3.00/1.01  --inst_activity_threshold               500
% 3.00/1.01  --inst_out_proof                        true
% 3.00/1.01  
% 3.00/1.01  ------ Resolution Options
% 3.00/1.01  
% 3.00/1.01  --resolution_flag                       false
% 3.00/1.01  --res_lit_sel                           adaptive
% 3.00/1.01  --res_lit_sel_side                      none
% 3.00/1.01  --res_ordering                          kbo
% 3.00/1.01  --res_to_prop_solver                    active
% 3.00/1.01  --res_prop_simpl_new                    false
% 3.00/1.01  --res_prop_simpl_given                  true
% 3.00/1.01  --res_passive_queue_type                priority_queues
% 3.00/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.00/1.01  --res_passive_queues_freq               [15;5]
% 3.00/1.01  --res_forward_subs                      full
% 3.00/1.01  --res_backward_subs                     full
% 3.00/1.01  --res_forward_subs_resolution           true
% 3.00/1.01  --res_backward_subs_resolution          true
% 3.00/1.01  --res_orphan_elimination                true
% 3.00/1.01  --res_time_limit                        2.
% 3.00/1.01  --res_out_proof                         true
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Options
% 3.00/1.01  
% 3.00/1.01  --superposition_flag                    true
% 3.00/1.01  --sup_passive_queue_type                priority_queues
% 3.00/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.00/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.00/1.01  --demod_completeness_check              fast
% 3.00/1.01  --demod_use_ground                      true
% 3.00/1.01  --sup_to_prop_solver                    passive
% 3.00/1.01  --sup_prop_simpl_new                    true
% 3.00/1.01  --sup_prop_simpl_given                  true
% 3.00/1.01  --sup_fun_splitting                     false
% 3.00/1.01  --sup_smt_interval                      50000
% 3.00/1.01  
% 3.00/1.01  ------ Superposition Simplification Setup
% 3.00/1.01  
% 3.00/1.01  --sup_indices_passive                   []
% 3.00/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.00/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.00/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_full_bw                           [BwDemod]
% 3.00/1.01  --sup_immed_triv                        [TrivRules]
% 3.00/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.00/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_immed_bw_main                     []
% 3.00/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.00/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.00/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.00/1.01  
% 3.00/1.01  ------ Combination Options
% 3.00/1.01  
% 3.00/1.01  --comb_res_mult                         3
% 3.00/1.01  --comb_sup_mult                         2
% 3.00/1.01  --comb_inst_mult                        10
% 3.00/1.01  
% 3.00/1.01  ------ Debug Options
% 3.00/1.01  
% 3.00/1.01  --dbg_backtrace                         false
% 3.00/1.01  --dbg_dump_prop_clauses                 false
% 3.00/1.01  --dbg_dump_prop_clauses_file            -
% 3.00/1.01  --dbg_out_stat                          false
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  ------ Proving...
% 3.00/1.01  
% 3.00/1.01  
% 3.00/1.01  % SZS status Theorem for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01   Resolution empty clause
% 3.00/1.01  
% 3.00/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.00/1.01  
% 3.00/1.01  fof(f7,axiom,(
% 3.00/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f59,plain,(
% 3.00/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f7])).
% 3.00/1.01  
% 3.00/1.01  fof(f16,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f30,plain,(
% 3.00/1.01    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(ennf_transformation,[],[f16])).
% 3.00/1.01  
% 3.00/1.01  fof(f71,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f30])).
% 3.00/1.01  
% 3.00/1.01  fof(f12,axiom,(
% 3.00/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f26,plain,(
% 3.00/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.00/1.01    inference(ennf_transformation,[],[f12])).
% 3.00/1.01  
% 3.00/1.01  fof(f44,plain,(
% 3.00/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.00/1.01    inference(nnf_transformation,[],[f26])).
% 3.00/1.01  
% 3.00/1.01  fof(f65,plain,(
% 3.00/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f44])).
% 3.00/1.01  
% 3.00/1.01  fof(f6,axiom,(
% 3.00/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f40,plain,(
% 3.00/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.00/1.01    inference(nnf_transformation,[],[f6])).
% 3.00/1.01  
% 3.00/1.01  fof(f41,plain,(
% 3.00/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.00/1.01    inference(flattening,[],[f40])).
% 3.00/1.01  
% 3.00/1.01  fof(f58,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.00/1.01    inference(cnf_transformation,[],[f41])).
% 3.00/1.01  
% 3.00/1.01  fof(f91,plain,(
% 3.00/1.01    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.00/1.01    inference(equality_resolution,[],[f58])).
% 3.00/1.01  
% 3.00/1.01  fof(f13,axiom,(
% 3.00/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f67,plain,(
% 3.00/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f13])).
% 3.00/1.01  
% 3.00/1.01  fof(f8,axiom,(
% 3.00/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f42,plain,(
% 3.00/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.00/1.01    inference(nnf_transformation,[],[f8])).
% 3.00/1.01  
% 3.00/1.01  fof(f60,plain,(
% 3.00/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f42])).
% 3.00/1.01  
% 3.00/1.01  fof(f1,axiom,(
% 3.00/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f36,plain,(
% 3.00/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/1.01    inference(nnf_transformation,[],[f1])).
% 3.00/1.01  
% 3.00/1.01  fof(f37,plain,(
% 3.00/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.00/1.01    inference(flattening,[],[f36])).
% 3.00/1.01  
% 3.00/1.01  fof(f49,plain,(
% 3.00/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f37])).
% 3.00/1.01  
% 3.00/1.01  fof(f14,axiom,(
% 3.00/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f27,plain,(
% 3.00/1.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.00/1.01    inference(ennf_transformation,[],[f14])).
% 3.00/1.01  
% 3.00/1.01  fof(f68,plain,(
% 3.00/1.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f27])).
% 3.00/1.01  
% 3.00/1.01  fof(f47,plain,(
% 3.00/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.00/1.01    inference(cnf_transformation,[],[f37])).
% 3.00/1.01  
% 3.00/1.01  fof(f88,plain,(
% 3.00/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.00/1.01    inference(equality_resolution,[],[f47])).
% 3.00/1.01  
% 3.00/1.01  fof(f19,conjecture,(
% 3.00/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f20,negated_conjecture,(
% 3.00/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.00/1.01    inference(negated_conjecture,[],[f19])).
% 3.00/1.01  
% 3.00/1.01  fof(f21,plain,(
% 3.00/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.00/1.01    inference(pure_predicate_removal,[],[f20])).
% 3.00/1.01  
% 3.00/1.01  fof(f34,plain,(
% 3.00/1.01    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 3.00/1.01    inference(ennf_transformation,[],[f21])).
% 3.00/1.01  
% 3.00/1.01  fof(f35,plain,(
% 3.00/1.01    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 3.00/1.01    inference(flattening,[],[f34])).
% 3.00/1.01  
% 3.00/1.01  fof(f45,plain,(
% 3.00/1.01    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 3.00/1.01    introduced(choice_axiom,[])).
% 3.00/1.01  
% 3.00/1.01  fof(f46,plain,(
% 3.00/1.01    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 3.00/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f45])).
% 3.00/1.01  
% 3.00/1.01  fof(f76,plain,(
% 3.00/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.00/1.01    inference(cnf_transformation,[],[f46])).
% 3.00/1.01  
% 3.00/1.01  fof(f2,axiom,(
% 3.00/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f50,plain,(
% 3.00/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f2])).
% 3.00/1.01  
% 3.00/1.01  fof(f3,axiom,(
% 3.00/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f51,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f3])).
% 3.00/1.01  
% 3.00/1.01  fof(f4,axiom,(
% 3.00/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f52,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f4])).
% 3.00/1.01  
% 3.00/1.01  fof(f79,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.00/1.01    inference(definition_unfolding,[],[f51,f52])).
% 3.00/1.01  
% 3.00/1.01  fof(f80,plain,(
% 3.00/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.00/1.01    inference(definition_unfolding,[],[f50,f79])).
% 3.00/1.01  
% 3.00/1.01  fof(f86,plain,(
% 3.00/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 3.00/1.01    inference(definition_unfolding,[],[f76,f80])).
% 3.00/1.01  
% 3.00/1.01  fof(f70,plain,(
% 3.00/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f30])).
% 3.00/1.01  
% 3.00/1.01  fof(f11,axiom,(
% 3.00/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f25,plain,(
% 3.00/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.00/1.01    inference(ennf_transformation,[],[f11])).
% 3.00/1.01  
% 3.00/1.01  fof(f43,plain,(
% 3.00/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.00/1.01    inference(nnf_transformation,[],[f25])).
% 3.00/1.01  
% 3.00/1.01  fof(f63,plain,(
% 3.00/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f43])).
% 3.00/1.01  
% 3.00/1.01  fof(f10,axiom,(
% 3.00/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f24,plain,(
% 3.00/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.00/1.01    inference(ennf_transformation,[],[f10])).
% 3.00/1.01  
% 3.00/1.01  fof(f62,plain,(
% 3.00/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f24])).
% 3.00/1.01  
% 3.00/1.01  fof(f61,plain,(
% 3.00/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f42])).
% 3.00/1.01  
% 3.00/1.01  fof(f5,axiom,(
% 3.00/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f38,plain,(
% 3.00/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.00/1.01    inference(nnf_transformation,[],[f5])).
% 3.00/1.01  
% 3.00/1.01  fof(f39,plain,(
% 3.00/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.00/1.01    inference(flattening,[],[f38])).
% 3.00/1.01  
% 3.00/1.01  fof(f53,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f39])).
% 3.00/1.01  
% 3.00/1.01  fof(f83,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.00/1.01    inference(definition_unfolding,[],[f53,f80,f80])).
% 3.00/1.01  
% 3.00/1.01  fof(f15,axiom,(
% 3.00/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f28,plain,(
% 3.00/1.01    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.00/1.01    inference(ennf_transformation,[],[f15])).
% 3.00/1.01  
% 3.00/1.01  fof(f29,plain,(
% 3.00/1.01    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.00/1.01    inference(flattening,[],[f28])).
% 3.00/1.01  
% 3.00/1.01  fof(f69,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.00/1.01    inference(cnf_transformation,[],[f29])).
% 3.00/1.01  
% 3.00/1.01  fof(f84,plain,(
% 3.00/1.01    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.00/1.01    inference(definition_unfolding,[],[f69,f80,f80])).
% 3.00/1.01  
% 3.00/1.01  fof(f75,plain,(
% 3.00/1.01    v1_funct_1(sK3)),
% 3.00/1.01    inference(cnf_transformation,[],[f46])).
% 3.00/1.01  
% 3.00/1.01  fof(f17,axiom,(
% 3.00/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f31,plain,(
% 3.00/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.00/1.01    inference(ennf_transformation,[],[f17])).
% 3.00/1.01  
% 3.00/1.01  fof(f72,plain,(
% 3.00/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.00/1.01    inference(cnf_transformation,[],[f31])).
% 3.00/1.01  
% 3.00/1.01  fof(f78,plain,(
% 3.00/1.01    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 3.00/1.01    inference(cnf_transformation,[],[f46])).
% 3.00/1.01  
% 3.00/1.01  fof(f85,plain,(
% 3.00/1.01    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 3.00/1.01    inference(definition_unfolding,[],[f78,f80,f80])).
% 3.00/1.01  
% 3.00/1.01  fof(f18,axiom,(
% 3.00/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.00/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.00/1.01  
% 3.00/1.01  fof(f22,plain,(
% 3.00/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1))))),
% 3.00/1.01    inference(pure_predicate_removal,[],[f18])).
% 3.00/1.01  
% 3.00/1.01  fof(f32,plain,(
% 3.00/1.01    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.00/1.01    inference(ennf_transformation,[],[f22])).
% 3.00/1.01  
% 3.00/1.01  fof(f33,plain,(
% 3.00/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.00/1.01    inference(flattening,[],[f32])).
% 3.00/1.02  
% 3.00/1.02  fof(f74,plain,(
% 3.00/1.02    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.00/1.02    inference(cnf_transformation,[],[f33])).
% 3.00/1.02  
% 3.00/1.02  fof(f57,plain,(
% 3.00/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.00/1.02    inference(cnf_transformation,[],[f41])).
% 3.00/1.02  
% 3.00/1.02  fof(f92,plain,(
% 3.00/1.02    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.00/1.02    inference(equality_resolution,[],[f57])).
% 3.00/1.02  
% 3.00/1.02  cnf(c_9,plain,
% 3.00/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.00/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1543,plain,
% 3.00/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_20,plain,
% 3.00/1.02      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.00/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_16,plain,
% 3.00/1.02      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_384,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | r1_tarski(k2_relat_1(X0),X2)
% 3.00/1.02      | ~ v1_relat_1(X0) ),
% 3.00/1.02      inference(resolution,[status(thm)],[c_20,c_16]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1531,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.00/1.02      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.00/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_384]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2174,plain,
% 3.00/1.02      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top
% 3.00/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1543,c_1531]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6,plain,
% 3.00/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f91]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_17,plain,
% 3.00/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.00/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1540,plain,
% 3.00/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2047,plain,
% 3.00/1.02      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_6,c_1540]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2223,plain,
% 3.00/1.02      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_2174,c_2047]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_11,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.00/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1541,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.00/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2233,plain,
% 3.00/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1543,c_1541]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_0,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.00/1.02      inference(cnf_transformation,[],[f49]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1548,plain,
% 3.00/1.02      ( X0 = X1
% 3.00/1.02      | r1_tarski(X0,X1) != iProver_top
% 3.00/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3309,plain,
% 3.00/1.02      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2233,c_1548]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3442,plain,
% 3.00/1.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2223,c_3309]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_18,plain,
% 3.00/1.02      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1539,plain,
% 3.00/1.02      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 3.00/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5940,plain,
% 3.00/1.02      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 3.00/1.02      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_3442,c_1539]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6692,plain,
% 3.00/1.02      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 3.00/1.02      inference(global_propositional_subsumption,[status(thm)],[c_5940,c_2047]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_6704,plain,
% 3.00/1.02      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_6692,c_3309]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f88]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1547,plain,
% 3.00/1.02      ( r1_tarski(X0,X0) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_27,negated_conjecture,
% 3.00/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 3.00/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1536,plain,
% 3.00/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_21,plain,
% 3.00/1.02      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.00/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_14,plain,
% 3.00/1.02      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_365,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 3.00/1.02      | ~ v1_relat_1(X0) ),
% 3.00/1.02      inference(resolution,[status(thm)],[c_21,c_14]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1532,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.00/1.02      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.00/1.02      | v1_relat_1(X0) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_365]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2463,plain,
% 3.00/1.02      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top
% 3.00/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1536,c_1532]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_30,plain,
% 3.00/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1837,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2077,plain,
% 3.00/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.00/1.02      | r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1837]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2078,plain,
% 3.00/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 3.00/1.02      | r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_2077]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_12,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_10,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.00/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_200,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.00/1.02      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_201,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_200]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_245,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.00/1.02      inference(bin_hyper_res,[status(thm)],[c_12,c_201]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1684,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.00/1.02      | v1_relat_1(X0)
% 3.00/1.02      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_245]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2156,plain,
% 3.00/1.02      ( ~ r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 3.00/1.02      | ~ v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 3.00/1.02      | v1_relat_1(sK3) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_1684]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2157,plain,
% 3.00/1.02      ( r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 3.00/1.02      | v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 3.00/1.02      | v1_relat_1(sK3) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_2156]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2262,plain,
% 3.00/1.02      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 3.00/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2263,plain,
% 3.00/1.02      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_2262]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2705,plain,
% 3.00/1.02      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_2463,c_30,c_2078,c_2157,c_2263]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5,plain,
% 3.00/1.02      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 3.00/1.02      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.00/1.02      | k1_xboole_0 = X0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1544,plain,
% 3.00/1.02      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.00/1.02      | k1_xboole_0 = X1
% 3.00/1.02      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4207,plain,
% 3.00/1.02      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.00/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2705,c_1544]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_19,plain,
% 3.00/1.02      ( ~ v1_funct_1(X0)
% 3.00/1.02      | ~ v1_relat_1(X0)
% 3.00/1.02      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.00/1.02      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_28,negated_conjecture,
% 3.00/1.02      ( v1_funct_1(sK3) ),
% 3.00/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_342,plain,
% 3.00/1.02      ( ~ v1_relat_1(X0)
% 3.00/1.02      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.00/1.02      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.00/1.02      | sK3 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_343,plain,
% 3.00/1.02      ( ~ v1_relat_1(sK3)
% 3.00/1.02      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.00/1.02      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_342]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1533,plain,
% 3.00/1.02      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.00/1.02      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.00/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4555,plain,
% 3.00/1.02      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.00/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 3.00/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_4207,c_1533]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4598,plain,
% 3.00/1.02      ( ~ v1_relat_1(sK3)
% 3.00/1.02      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.00/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.00/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_4555]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4689,plain,
% 3.00/1.02      ( k1_relat_1(sK3) = k1_xboole_0
% 3.00/1.02      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_4555,c_27,c_2077,c_2156,c_2262,c_4598]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4690,plain,
% 3.00/1.02      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.00/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_4689]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4695,plain,
% 3.00/1.02      ( k2_enumset1(k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0)),k1_funct_1(sK3,k1_funct_1(sK3,sK0))) = k2_relat_1(sK3)
% 3.00/1.02      | k2_relat_1(sK3) != k1_relat_1(sK3)
% 3.00/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 3.00/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_4690,c_1533]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_22,plain,
% 3.00/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.00/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.00/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1538,plain,
% 3.00/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.00/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3567,plain,
% 3.00/1.02      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1536,c_1538]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_25,negated_conjecture,
% 3.00/1.02      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.00/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1537,plain,
% 3.00/1.02      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_3793,plain,
% 3.00/1.02      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_3567,c_1537]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4696,plain,
% 3.00/1.02      ( k1_relat_1(sK3) = k1_xboole_0
% 3.00/1.02      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_4690,c_3793]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4858,plain,
% 3.00/1.02      ( k1_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1539,c_4696]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4861,plain,
% 3.00/1.02      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_4695,c_30,c_2078,c_2157,c_2263,c_4858]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_23,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.00/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.00/1.02      | ~ v1_funct_1(X0)
% 3.00/1.02      | ~ v1_relat_1(X0) ),
% 3.00/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_327,plain,
% 3.00/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.00/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.00/1.02      | ~ v1_relat_1(X0)
% 3.00/1.02      | sK3 != X0 ),
% 3.00/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_328,plain,
% 3.00/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
% 3.00/1.02      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 3.00/1.02      | ~ v1_relat_1(sK3) ),
% 3.00/1.02      inference(unflattening,[status(thm)],[c_327]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_1534,plain,
% 3.00/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 3.00/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.00/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.00/1.02      inference(predicate_to_equality,[status(thm)],[c_328]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2235,plain,
% 3.00/1.02      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.00/1.02      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top
% 3.00/1.02      | v1_relat_1(sK3) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1534,c_1541]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2365,plain,
% 3.00/1.02      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top
% 3.00/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.00/1.02      inference(global_propositional_subsumption,
% 3.00/1.02                [status(thm)],
% 3.00/1.02                [c_2235,c_30,c_2078,c_2157,c_2263]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2366,plain,
% 3.00/1.02      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.00/1.02      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top ),
% 3.00/1.02      inference(renaming,[status(thm)],[c_2365]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_2658,plain,
% 3.00/1.02      ( k2_zfmisc_1(k1_relat_1(sK3),X0) = sK3
% 3.00/1.02      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),X0),sK3) != iProver_top
% 3.00/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_2366,c_1548]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4869,plain,
% 3.00/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = sK3
% 3.00/1.02      | r1_tarski(k2_zfmisc_1(k1_xboole_0,X0),sK3) != iProver_top
% 3.00/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_4861,c_2658]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_7,plain,
% 3.00/1.02      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.00/1.02      inference(cnf_transformation,[],[f92]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_4901,plain,
% 3.00/1.02      ( sK3 = k1_xboole_0
% 3.00/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.00/1.02      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.00/1.02      inference(light_normalisation,[status(thm)],[c_4869,c_7]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5172,plain,
% 3.00/1.02      ( sK3 = k1_xboole_0 | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.00/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4901,c_2233]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5176,plain,
% 3.00/1.02      ( sK3 = k1_xboole_0 ),
% 3.00/1.02      inference(superposition,[status(thm)],[c_1547,c_5172]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_5332,plain,
% 3.00/1.02      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_5176,c_3793]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_7124,plain,
% 3.00/1.02      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.00/1.02      inference(demodulation,[status(thm)],[c_6704,c_5332]) ).
% 3.00/1.02  
% 3.00/1.02  cnf(c_7135,plain,
% 3.00/1.02      ( $false ),
% 3.00/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_7124,c_2233]) ).
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.00/1.02  
% 3.00/1.02  ------                               Statistics
% 3.00/1.02  
% 3.00/1.02  ------ General
% 3.00/1.02  
% 3.00/1.02  abstr_ref_over_cycles:                  0
% 3.00/1.02  abstr_ref_under_cycles:                 0
% 3.00/1.02  gc_basic_clause_elim:                   0
% 3.00/1.02  forced_gc_time:                         0
% 3.00/1.02  parsing_time:                           0.014
% 3.00/1.02  unif_index_cands_time:                  0.
% 3.00/1.02  unif_index_add_time:                    0.
% 3.00/1.02  orderings_time:                         0.
% 3.00/1.02  out_proof_time:                         0.011
% 3.00/1.02  total_time:                             0.234
% 3.00/1.02  num_of_symbols:                         50
% 3.00/1.02  num_of_terms:                           6645
% 3.00/1.02  
% 3.00/1.02  ------ Preprocessing
% 3.00/1.02  
% 3.00/1.02  num_of_splits:                          0
% 3.00/1.02  num_of_split_atoms:                     0
% 3.00/1.02  num_of_reused_defs:                     0
% 3.00/1.02  num_eq_ax_congr_red:                    12
% 3.00/1.02  num_of_sem_filtered_clauses:            1
% 3.00/1.02  num_of_subtypes:                        0
% 3.00/1.02  monotx_restored_types:                  0
% 3.00/1.02  sat_num_of_epr_types:                   0
% 3.00/1.02  sat_num_of_non_cyclic_types:            0
% 3.00/1.02  sat_guarded_non_collapsed_types:        0
% 3.00/1.02  num_pure_diseq_elim:                    0
% 3.00/1.02  simp_replaced_by:                       0
% 3.00/1.02  res_preprocessed:                       118
% 3.00/1.02  prep_upred:                             0
% 3.00/1.02  prep_unflattend:                        32
% 3.00/1.02  smt_new_axioms:                         0
% 3.00/1.02  pred_elim_cands:                        3
% 3.00/1.02  pred_elim:                              3
% 3.00/1.02  pred_elim_cl:                           5
% 3.00/1.02  pred_elim_cycles:                       5
% 3.00/1.02  merged_defs:                            8
% 3.00/1.02  merged_defs_ncl:                        0
% 3.00/1.02  bin_hyper_res:                          9
% 3.00/1.02  prep_cycles:                            4
% 3.00/1.02  pred_elim_time:                         0.015
% 3.00/1.02  splitting_time:                         0.
% 3.00/1.02  sem_filter_time:                        0.
% 3.00/1.02  monotx_time:                            0.
% 3.00/1.02  subtype_inf_time:                       0.
% 3.00/1.02  
% 3.00/1.02  ------ Problem properties
% 3.00/1.02  
% 3.00/1.02  clauses:                                22
% 3.00/1.02  conjectures:                            3
% 3.00/1.02  epr:                                    4
% 3.00/1.02  horn:                                   20
% 3.00/1.02  ground:                                 3
% 3.00/1.02  unary:                                  10
% 3.00/1.02  binary:                                 4
% 3.00/1.02  lits:                                   42
% 3.00/1.02  lits_eq:                                12
% 3.00/1.02  fd_pure:                                0
% 3.00/1.02  fd_pseudo:                              0
% 3.00/1.02  fd_cond:                                1
% 3.00/1.02  fd_pseudo_cond:                         2
% 3.00/1.02  ac_symbols:                             0
% 3.00/1.02  
% 3.00/1.02  ------ Propositional Solver
% 3.00/1.02  
% 3.00/1.02  prop_solver_calls:                      29
% 3.00/1.02  prop_fast_solver_calls:                 866
% 3.00/1.02  smt_solver_calls:                       0
% 3.00/1.02  smt_fast_solver_calls:                  0
% 3.00/1.02  prop_num_of_clauses:                    2629
% 3.00/1.02  prop_preprocess_simplified:             6154
% 3.00/1.02  prop_fo_subsumed:                       33
% 3.00/1.02  prop_solver_time:                       0.
% 3.00/1.02  smt_solver_time:                        0.
% 3.00/1.02  smt_fast_solver_time:                   0.
% 3.00/1.02  prop_fast_solver_time:                  0.
% 3.00/1.02  prop_unsat_core_time:                   0.
% 3.00/1.02  
% 3.00/1.02  ------ QBF
% 3.00/1.02  
% 3.00/1.02  qbf_q_res:                              0
% 3.00/1.02  qbf_num_tautologies:                    0
% 3.00/1.02  qbf_prep_cycles:                        0
% 3.00/1.02  
% 3.00/1.02  ------ BMC1
% 3.00/1.02  
% 3.00/1.02  bmc1_current_bound:                     -1
% 3.00/1.02  bmc1_last_solved_bound:                 -1
% 3.00/1.02  bmc1_unsat_core_size:                   -1
% 3.00/1.02  bmc1_unsat_core_parents_size:           -1
% 3.00/1.02  bmc1_merge_next_fun:                    0
% 3.00/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.00/1.02  
% 3.00/1.02  ------ Instantiation
% 3.00/1.02  
% 3.00/1.02  inst_num_of_clauses:                    719
% 3.00/1.02  inst_num_in_passive:                    163
% 3.00/1.02  inst_num_in_active:                     421
% 3.00/1.02  inst_num_in_unprocessed:                136
% 3.00/1.02  inst_num_of_loops:                      440
% 3.00/1.02  inst_num_of_learning_restarts:          0
% 3.00/1.02  inst_num_moves_active_passive:          15
% 3.00/1.02  inst_lit_activity:                      0
% 3.00/1.02  inst_lit_activity_moves:                0
% 3.00/1.02  inst_num_tautologies:                   0
% 3.00/1.02  inst_num_prop_implied:                  0
% 3.00/1.02  inst_num_existing_simplified:           0
% 3.00/1.02  inst_num_eq_res_simplified:             0
% 3.00/1.02  inst_num_child_elim:                    0
% 3.00/1.02  inst_num_of_dismatching_blockings:      415
% 3.00/1.02  inst_num_of_non_proper_insts:           1115
% 3.00/1.02  inst_num_of_duplicates:                 0
% 3.00/1.02  inst_inst_num_from_inst_to_res:         0
% 3.00/1.02  inst_dismatching_checking_time:         0.
% 3.00/1.02  
% 3.00/1.02  ------ Resolution
% 3.00/1.02  
% 3.00/1.02  res_num_of_clauses:                     0
% 3.00/1.02  res_num_in_passive:                     0
% 3.00/1.02  res_num_in_active:                      0
% 3.00/1.02  res_num_of_loops:                       122
% 3.00/1.02  res_forward_subset_subsumed:            138
% 3.00/1.02  res_backward_subset_subsumed:           6
% 3.00/1.02  res_forward_subsumed:                   0
% 3.00/1.02  res_backward_subsumed:                  0
% 3.00/1.02  res_forward_subsumption_resolution:     0
% 3.00/1.02  res_backward_subsumption_resolution:    0
% 3.00/1.02  res_clause_to_clause_subsumption:       547
% 3.00/1.02  res_orphan_elimination:                 0
% 3.00/1.02  res_tautology_del:                      90
% 3.00/1.02  res_num_eq_res_simplified:              0
% 3.00/1.02  res_num_sel_changes:                    0
% 3.00/1.02  res_moves_from_active_to_pass:          0
% 3.00/1.02  
% 3.00/1.02  ------ Superposition
% 3.00/1.02  
% 3.00/1.02  sup_time_total:                         0.
% 3.00/1.02  sup_time_generating:                    0.
% 3.00/1.02  sup_time_sim_full:                      0.
% 3.00/1.02  sup_time_sim_immed:                     0.
% 3.00/1.02  
% 3.00/1.02  sup_num_of_clauses:                     87
% 3.00/1.02  sup_num_in_active:                      44
% 3.00/1.02  sup_num_in_passive:                     43
% 3.00/1.02  sup_num_of_loops:                       87
% 3.00/1.02  sup_fw_superposition:                   105
% 3.00/1.02  sup_bw_superposition:                   65
% 3.00/1.02  sup_immediate_simplified:               52
% 3.00/1.02  sup_given_eliminated:                   3
% 3.00/1.02  comparisons_done:                       0
% 3.00/1.02  comparisons_avoided:                    3
% 3.00/1.02  
% 3.00/1.02  ------ Simplifications
% 3.00/1.02  
% 3.00/1.02  
% 3.00/1.02  sim_fw_subset_subsumed:                 18
% 3.00/1.02  sim_bw_subset_subsumed:                 14
% 3.00/1.02  sim_fw_subsumed:                        22
% 3.00/1.02  sim_bw_subsumed:                        2
% 3.00/1.02  sim_fw_subsumption_res:                 2
% 3.00/1.02  sim_bw_subsumption_res:                 0
% 3.00/1.02  sim_tautology_del:                      6
% 3.00/1.02  sim_eq_tautology_del:                   15
% 3.00/1.02  sim_eq_res_simp:                        0
% 3.00/1.02  sim_fw_demodulated:                     5
% 3.00/1.02  sim_bw_demodulated:                     35
% 3.00/1.02  sim_light_normalised:                   19
% 3.00/1.02  sim_joinable_taut:                      0
% 3.00/1.02  sim_joinable_simp:                      0
% 3.00/1.02  sim_ac_normalised:                      0
% 3.00/1.02  sim_smt_subsumption:                    0
% 3.00/1.02  
%------------------------------------------------------------------------------
