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
% DateTime   : Thu Dec  3 12:05:29 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 323 expanded)
%              Number of clauses        :   61 (  77 expanded)
%              Number of leaves         :   20 (  79 expanded)
%              Depth                    :   20
%              Number of atoms          :  316 ( 720 expanded)
%              Number of equality atoms :  140 ( 312 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f45])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f52,f77])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f74,f78])).

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

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f63,plain,(
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

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f55,f77,f78,f78,f77])).

fof(f76,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f76,f78,f78])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f67,f78,f78])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f13])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1150,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1132,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_14])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_345,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_18])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_345])).

cnf(c_1130,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_1495,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1130])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1142,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | k2_enumset1(X1,X1,X1,X1) = X2
    | k2_enumset1(X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3216,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1495,c_1142])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_322,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_323,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_322])).

cnf(c_324,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_323])).

cnf(c_326,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_324])).

cnf(c_1302,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1303,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1302])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1376,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1467,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1376])).

cnf(c_614,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1354,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_1466,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1354])).

cnf(c_1557,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1466])).

cnf(c_15,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1411,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1558,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1411])).

cnf(c_3549,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3216,c_25,c_28,c_23,c_326,c_1302,c_1303,c_1467,c_1557,c_1558])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1134,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1980,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1132,c_1134])).

cnf(c_3557,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3549,c_1980])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1141,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1139,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1607,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1141,c_1139])).

cnf(c_3603,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3557,c_1607])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1136,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3612,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3603,c_1136])).

cnf(c_4053,plain,
    ( v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1150,c_3612])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1149,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4058,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4053,c_1149])).

cnf(c_1135,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2193,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1132,c_1135])).

cnf(c_1133,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2390,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2193,c_1133])).

cnf(c_4155,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4058,c_2390])).

cnf(c_16,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_4165,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4155,c_16])).

cnf(c_4252,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4165,c_1607])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:21:15 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.59/0.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.59/0.93  
% 2.59/0.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.59/0.93  
% 2.59/0.93  ------  iProver source info
% 2.59/0.93  
% 2.59/0.93  git: date: 2020-06-30 10:37:57 +0100
% 2.59/0.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.59/0.93  git: non_committed_changes: false
% 2.59/0.93  git: last_make_outside_of_git: false
% 2.59/0.93  
% 2.59/0.93  ------ 
% 2.59/0.93  
% 2.59/0.93  ------ Input Options
% 2.59/0.93  
% 2.59/0.93  --out_options                           all
% 2.59/0.93  --tptp_safe_out                         true
% 2.59/0.93  --problem_path                          ""
% 2.59/0.93  --include_path                          ""
% 2.59/0.93  --clausifier                            res/vclausify_rel
% 2.59/0.93  --clausifier_options                    --mode clausify
% 2.59/0.93  --stdin                                 false
% 2.59/0.93  --stats_out                             all
% 2.59/0.93  
% 2.59/0.93  ------ General Options
% 2.59/0.93  
% 2.59/0.93  --fof                                   false
% 2.59/0.93  --time_out_real                         305.
% 2.59/0.93  --time_out_virtual                      -1.
% 2.59/0.93  --symbol_type_check                     false
% 2.59/0.93  --clausify_out                          false
% 2.59/0.93  --sig_cnt_out                           false
% 2.59/0.93  --trig_cnt_out                          false
% 2.59/0.93  --trig_cnt_out_tolerance                1.
% 2.59/0.93  --trig_cnt_out_sk_spl                   false
% 2.59/0.93  --abstr_cl_out                          false
% 2.59/0.93  
% 2.59/0.93  ------ Global Options
% 2.59/0.93  
% 2.59/0.93  --schedule                              default
% 2.59/0.93  --add_important_lit                     false
% 2.59/0.93  --prop_solver_per_cl                    1000
% 2.59/0.93  --min_unsat_core                        false
% 2.59/0.93  --soft_assumptions                      false
% 2.59/0.93  --soft_lemma_size                       3
% 2.59/0.93  --prop_impl_unit_size                   0
% 2.59/0.93  --prop_impl_unit                        []
% 2.59/0.93  --share_sel_clauses                     true
% 2.59/0.93  --reset_solvers                         false
% 2.59/0.93  --bc_imp_inh                            [conj_cone]
% 2.59/0.93  --conj_cone_tolerance                   3.
% 2.59/0.93  --extra_neg_conj                        none
% 2.59/0.93  --large_theory_mode                     true
% 2.59/0.93  --prolific_symb_bound                   200
% 2.59/0.93  --lt_threshold                          2000
% 2.59/0.93  --clause_weak_htbl                      true
% 2.59/0.93  --gc_record_bc_elim                     false
% 2.59/0.93  
% 2.59/0.93  ------ Preprocessing Options
% 2.59/0.93  
% 2.59/0.93  --preprocessing_flag                    true
% 2.59/0.93  --time_out_prep_mult                    0.1
% 2.59/0.93  --splitting_mode                        input
% 2.59/0.93  --splitting_grd                         true
% 2.59/0.93  --splitting_cvd                         false
% 2.59/0.93  --splitting_cvd_svl                     false
% 2.59/0.93  --splitting_nvd                         32
% 2.59/0.93  --sub_typing                            true
% 2.59/0.93  --prep_gs_sim                           true
% 2.59/0.93  --prep_unflatten                        true
% 2.59/0.93  --prep_res_sim                          true
% 2.59/0.93  --prep_upred                            true
% 2.59/0.93  --prep_sem_filter                       exhaustive
% 2.59/0.93  --prep_sem_filter_out                   false
% 2.59/0.93  --pred_elim                             true
% 2.59/0.93  --res_sim_input                         true
% 2.59/0.93  --eq_ax_congr_red                       true
% 2.59/0.93  --pure_diseq_elim                       true
% 2.59/0.93  --brand_transform                       false
% 2.59/0.93  --non_eq_to_eq                          false
% 2.59/0.93  --prep_def_merge                        true
% 2.59/0.93  --prep_def_merge_prop_impl              false
% 2.59/0.93  --prep_def_merge_mbd                    true
% 2.59/0.93  --prep_def_merge_tr_red                 false
% 2.59/0.93  --prep_def_merge_tr_cl                  false
% 2.59/0.93  --smt_preprocessing                     true
% 2.59/0.93  --smt_ac_axioms                         fast
% 2.59/0.93  --preprocessed_out                      false
% 2.59/0.93  --preprocessed_stats                    false
% 2.59/0.93  
% 2.59/0.93  ------ Abstraction refinement Options
% 2.59/0.93  
% 2.59/0.93  --abstr_ref                             []
% 2.59/0.93  --abstr_ref_prep                        false
% 2.59/0.93  --abstr_ref_until_sat                   false
% 2.59/0.93  --abstr_ref_sig_restrict                funpre
% 2.59/0.93  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.93  --abstr_ref_under                       []
% 2.59/0.93  
% 2.59/0.93  ------ SAT Options
% 2.59/0.93  
% 2.59/0.93  --sat_mode                              false
% 2.59/0.93  --sat_fm_restart_options                ""
% 2.59/0.93  --sat_gr_def                            false
% 2.59/0.93  --sat_epr_types                         true
% 2.59/0.93  --sat_non_cyclic_types                  false
% 2.59/0.93  --sat_finite_models                     false
% 2.59/0.93  --sat_fm_lemmas                         false
% 2.59/0.93  --sat_fm_prep                           false
% 2.59/0.93  --sat_fm_uc_incr                        true
% 2.59/0.93  --sat_out_model                         small
% 2.59/0.93  --sat_out_clauses                       false
% 2.59/0.93  
% 2.59/0.93  ------ QBF Options
% 2.59/0.93  
% 2.59/0.93  --qbf_mode                              false
% 2.59/0.93  --qbf_elim_univ                         false
% 2.59/0.93  --qbf_dom_inst                          none
% 2.59/0.93  --qbf_dom_pre_inst                      false
% 2.59/0.93  --qbf_sk_in                             false
% 2.59/0.93  --qbf_pred_elim                         true
% 2.59/0.93  --qbf_split                             512
% 2.59/0.93  
% 2.59/0.93  ------ BMC1 Options
% 2.59/0.93  
% 2.59/0.93  --bmc1_incremental                      false
% 2.59/0.93  --bmc1_axioms                           reachable_all
% 2.59/0.93  --bmc1_min_bound                        0
% 2.59/0.93  --bmc1_max_bound                        -1
% 2.59/0.93  --bmc1_max_bound_default                -1
% 2.59/0.93  --bmc1_symbol_reachability              true
% 2.59/0.93  --bmc1_property_lemmas                  false
% 2.59/0.93  --bmc1_k_induction                      false
% 2.59/0.93  --bmc1_non_equiv_states                 false
% 2.59/0.93  --bmc1_deadlock                         false
% 2.59/0.93  --bmc1_ucm                              false
% 2.59/0.93  --bmc1_add_unsat_core                   none
% 2.59/0.93  --bmc1_unsat_core_children              false
% 2.59/0.93  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.93  --bmc1_out_stat                         full
% 2.59/0.93  --bmc1_ground_init                      false
% 2.59/0.93  --bmc1_pre_inst_next_state              false
% 2.59/0.93  --bmc1_pre_inst_state                   false
% 2.59/0.93  --bmc1_pre_inst_reach_state             false
% 2.59/0.93  --bmc1_out_unsat_core                   false
% 2.59/0.93  --bmc1_aig_witness_out                  false
% 2.59/0.93  --bmc1_verbose                          false
% 2.59/0.93  --bmc1_dump_clauses_tptp                false
% 2.59/0.93  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.93  --bmc1_dump_file                        -
% 2.59/0.93  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.93  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.93  --bmc1_ucm_extend_mode                  1
% 2.59/0.93  --bmc1_ucm_init_mode                    2
% 2.59/0.93  --bmc1_ucm_cone_mode                    none
% 2.59/0.93  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.93  --bmc1_ucm_relax_model                  4
% 2.59/0.93  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.93  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.93  --bmc1_ucm_layered_model                none
% 2.59/0.93  --bmc1_ucm_max_lemma_size               10
% 2.59/0.93  
% 2.59/0.93  ------ AIG Options
% 2.59/0.93  
% 2.59/0.93  --aig_mode                              false
% 2.59/0.93  
% 2.59/0.93  ------ Instantiation Options
% 2.59/0.93  
% 2.59/0.93  --instantiation_flag                    true
% 2.59/0.93  --inst_sos_flag                         false
% 2.59/0.93  --inst_sos_phase                        true
% 2.59/0.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.93  --inst_lit_sel_side                     num_symb
% 2.59/0.93  --inst_solver_per_active                1400
% 2.59/0.93  --inst_solver_calls_frac                1.
% 2.59/0.93  --inst_passive_queue_type               priority_queues
% 2.59/0.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.93  --inst_passive_queues_freq              [25;2]
% 2.59/0.93  --inst_dismatching                      true
% 2.59/0.93  --inst_eager_unprocessed_to_passive     true
% 2.59/0.93  --inst_prop_sim_given                   true
% 2.59/0.93  --inst_prop_sim_new                     false
% 2.59/0.93  --inst_subs_new                         false
% 2.59/0.93  --inst_eq_res_simp                      false
% 2.59/0.93  --inst_subs_given                       false
% 2.59/0.93  --inst_orphan_elimination               true
% 2.59/0.93  --inst_learning_loop_flag               true
% 2.59/0.93  --inst_learning_start                   3000
% 2.59/0.93  --inst_learning_factor                  2
% 2.59/0.93  --inst_start_prop_sim_after_learn       3
% 2.59/0.93  --inst_sel_renew                        solver
% 2.59/0.93  --inst_lit_activity_flag                true
% 2.59/0.93  --inst_restr_to_given                   false
% 2.59/0.93  --inst_activity_threshold               500
% 2.59/0.93  --inst_out_proof                        true
% 2.59/0.93  
% 2.59/0.93  ------ Resolution Options
% 2.59/0.93  
% 2.59/0.93  --resolution_flag                       true
% 2.59/0.93  --res_lit_sel                           adaptive
% 2.59/0.93  --res_lit_sel_side                      none
% 2.59/0.93  --res_ordering                          kbo
% 2.59/0.93  --res_to_prop_solver                    active
% 2.59/0.93  --res_prop_simpl_new                    false
% 2.59/0.93  --res_prop_simpl_given                  true
% 2.59/0.93  --res_passive_queue_type                priority_queues
% 2.59/0.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.93  --res_passive_queues_freq               [15;5]
% 2.59/0.93  --res_forward_subs                      full
% 2.59/0.93  --res_backward_subs                     full
% 2.59/0.93  --res_forward_subs_resolution           true
% 2.59/0.93  --res_backward_subs_resolution          true
% 2.59/0.93  --res_orphan_elimination                true
% 2.59/0.93  --res_time_limit                        2.
% 2.59/0.93  --res_out_proof                         true
% 2.59/0.93  
% 2.59/0.93  ------ Superposition Options
% 2.59/0.93  
% 2.59/0.93  --superposition_flag                    true
% 2.59/0.93  --sup_passive_queue_type                priority_queues
% 2.59/0.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.93  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.93  --demod_completeness_check              fast
% 2.59/0.93  --demod_use_ground                      true
% 2.59/0.93  --sup_to_prop_solver                    passive
% 2.59/0.93  --sup_prop_simpl_new                    true
% 2.59/0.93  --sup_prop_simpl_given                  true
% 2.59/0.93  --sup_fun_splitting                     false
% 2.59/0.93  --sup_smt_interval                      50000
% 2.59/0.93  
% 2.59/0.93  ------ Superposition Simplification Setup
% 2.59/0.93  
% 2.59/0.93  --sup_indices_passive                   []
% 2.59/0.93  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.93  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.93  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.93  --sup_full_bw                           [BwDemod]
% 2.59/0.93  --sup_immed_triv                        [TrivRules]
% 2.59/0.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.93  --sup_immed_bw_main                     []
% 2.59/0.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.93  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.93  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.93  
% 2.59/0.93  ------ Combination Options
% 2.59/0.93  
% 2.59/0.93  --comb_res_mult                         3
% 2.59/0.93  --comb_sup_mult                         2
% 2.59/0.93  --comb_inst_mult                        10
% 2.59/0.93  
% 2.59/0.93  ------ Debug Options
% 2.59/0.93  
% 2.59/0.93  --dbg_backtrace                         false
% 2.59/0.93  --dbg_dump_prop_clauses                 false
% 2.59/0.93  --dbg_dump_prop_clauses_file            -
% 2.59/0.93  --dbg_out_stat                          false
% 2.59/0.93  ------ Parsing...
% 2.59/0.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.59/0.93  
% 2.59/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.59/0.93  
% 2.59/0.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.59/0.93  
% 2.59/0.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.59/0.93  ------ Proving...
% 2.59/0.93  ------ Problem Properties 
% 2.59/0.93  
% 2.59/0.93  
% 2.59/0.93  clauses                                 23
% 2.59/0.93  conjectures                             3
% 2.59/0.93  EPR                                     5
% 2.59/0.93  Horn                                    22
% 2.59/0.93  unary                                   11
% 2.59/0.93  binary                                  7
% 2.59/0.93  lits                                    42
% 2.59/0.93  lits eq                                 11
% 2.59/0.93  fd_pure                                 0
% 2.59/0.93  fd_pseudo                               0
% 2.59/0.93  fd_cond                                 1
% 2.59/0.93  fd_pseudo_cond                          2
% 2.59/0.93  AC symbols                              0
% 2.59/0.93  
% 2.59/0.93  ------ Schedule dynamic 5 is on 
% 2.59/0.93  
% 2.59/0.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.59/0.93  
% 2.59/0.93  
% 2.59/0.93  ------ 
% 2.59/0.93  Current options:
% 2.59/0.93  ------ 
% 2.59/0.93  
% 2.59/0.93  ------ Input Options
% 2.59/0.93  
% 2.59/0.93  --out_options                           all
% 2.59/0.93  --tptp_safe_out                         true
% 2.59/0.93  --problem_path                          ""
% 2.59/0.93  --include_path                          ""
% 2.59/0.93  --clausifier                            res/vclausify_rel
% 2.59/0.93  --clausifier_options                    --mode clausify
% 2.59/0.93  --stdin                                 false
% 2.59/0.93  --stats_out                             all
% 2.59/0.93  
% 2.59/0.93  ------ General Options
% 2.59/0.93  
% 2.59/0.93  --fof                                   false
% 2.59/0.93  --time_out_real                         305.
% 2.59/0.93  --time_out_virtual                      -1.
% 2.59/0.93  --symbol_type_check                     false
% 2.59/0.93  --clausify_out                          false
% 2.59/0.93  --sig_cnt_out                           false
% 2.59/0.93  --trig_cnt_out                          false
% 2.59/0.93  --trig_cnt_out_tolerance                1.
% 2.59/0.93  --trig_cnt_out_sk_spl                   false
% 2.59/0.93  --abstr_cl_out                          false
% 2.59/0.93  
% 2.59/0.93  ------ Global Options
% 2.59/0.93  
% 2.59/0.93  --schedule                              default
% 2.59/0.93  --add_important_lit                     false
% 2.59/0.93  --prop_solver_per_cl                    1000
% 2.59/0.93  --min_unsat_core                        false
% 2.59/0.93  --soft_assumptions                      false
% 2.59/0.93  --soft_lemma_size                       3
% 2.59/0.93  --prop_impl_unit_size                   0
% 2.59/0.93  --prop_impl_unit                        []
% 2.59/0.93  --share_sel_clauses                     true
% 2.59/0.93  --reset_solvers                         false
% 2.59/0.93  --bc_imp_inh                            [conj_cone]
% 2.59/0.93  --conj_cone_tolerance                   3.
% 2.59/0.94  --extra_neg_conj                        none
% 2.59/0.94  --large_theory_mode                     true
% 2.59/0.94  --prolific_symb_bound                   200
% 2.59/0.94  --lt_threshold                          2000
% 2.59/0.94  --clause_weak_htbl                      true
% 2.59/0.94  --gc_record_bc_elim                     false
% 2.59/0.94  
% 2.59/0.94  ------ Preprocessing Options
% 2.59/0.94  
% 2.59/0.94  --preprocessing_flag                    true
% 2.59/0.94  --time_out_prep_mult                    0.1
% 2.59/0.94  --splitting_mode                        input
% 2.59/0.94  --splitting_grd                         true
% 2.59/0.94  --splitting_cvd                         false
% 2.59/0.94  --splitting_cvd_svl                     false
% 2.59/0.94  --splitting_nvd                         32
% 2.59/0.94  --sub_typing                            true
% 2.59/0.94  --prep_gs_sim                           true
% 2.59/0.94  --prep_unflatten                        true
% 2.59/0.94  --prep_res_sim                          true
% 2.59/0.94  --prep_upred                            true
% 2.59/0.94  --prep_sem_filter                       exhaustive
% 2.59/0.94  --prep_sem_filter_out                   false
% 2.59/0.94  --pred_elim                             true
% 2.59/0.94  --res_sim_input                         true
% 2.59/0.94  --eq_ax_congr_red                       true
% 2.59/0.94  --pure_diseq_elim                       true
% 2.59/0.94  --brand_transform                       false
% 2.59/0.94  --non_eq_to_eq                          false
% 2.59/0.94  --prep_def_merge                        true
% 2.59/0.94  --prep_def_merge_prop_impl              false
% 2.59/0.94  --prep_def_merge_mbd                    true
% 2.59/0.94  --prep_def_merge_tr_red                 false
% 2.59/0.94  --prep_def_merge_tr_cl                  false
% 2.59/0.94  --smt_preprocessing                     true
% 2.59/0.94  --smt_ac_axioms                         fast
% 2.59/0.94  --preprocessed_out                      false
% 2.59/0.94  --preprocessed_stats                    false
% 2.59/0.94  
% 2.59/0.94  ------ Abstraction refinement Options
% 2.59/0.94  
% 2.59/0.94  --abstr_ref                             []
% 2.59/0.94  --abstr_ref_prep                        false
% 2.59/0.94  --abstr_ref_until_sat                   false
% 2.59/0.94  --abstr_ref_sig_restrict                funpre
% 2.59/0.94  --abstr_ref_af_restrict_to_split_sk     false
% 2.59/0.94  --abstr_ref_under                       []
% 2.59/0.94  
% 2.59/0.94  ------ SAT Options
% 2.59/0.94  
% 2.59/0.94  --sat_mode                              false
% 2.59/0.94  --sat_fm_restart_options                ""
% 2.59/0.94  --sat_gr_def                            false
% 2.59/0.94  --sat_epr_types                         true
% 2.59/0.94  --sat_non_cyclic_types                  false
% 2.59/0.94  --sat_finite_models                     false
% 2.59/0.94  --sat_fm_lemmas                         false
% 2.59/0.94  --sat_fm_prep                           false
% 2.59/0.94  --sat_fm_uc_incr                        true
% 2.59/0.94  --sat_out_model                         small
% 2.59/0.94  --sat_out_clauses                       false
% 2.59/0.94  
% 2.59/0.94  ------ QBF Options
% 2.59/0.94  
% 2.59/0.94  --qbf_mode                              false
% 2.59/0.94  --qbf_elim_univ                         false
% 2.59/0.94  --qbf_dom_inst                          none
% 2.59/0.94  --qbf_dom_pre_inst                      false
% 2.59/0.94  --qbf_sk_in                             false
% 2.59/0.94  --qbf_pred_elim                         true
% 2.59/0.94  --qbf_split                             512
% 2.59/0.94  
% 2.59/0.94  ------ BMC1 Options
% 2.59/0.94  
% 2.59/0.94  --bmc1_incremental                      false
% 2.59/0.94  --bmc1_axioms                           reachable_all
% 2.59/0.94  --bmc1_min_bound                        0
% 2.59/0.94  --bmc1_max_bound                        -1
% 2.59/0.94  --bmc1_max_bound_default                -1
% 2.59/0.94  --bmc1_symbol_reachability              true
% 2.59/0.94  --bmc1_property_lemmas                  false
% 2.59/0.94  --bmc1_k_induction                      false
% 2.59/0.94  --bmc1_non_equiv_states                 false
% 2.59/0.94  --bmc1_deadlock                         false
% 2.59/0.94  --bmc1_ucm                              false
% 2.59/0.94  --bmc1_add_unsat_core                   none
% 2.59/0.94  --bmc1_unsat_core_children              false
% 2.59/0.94  --bmc1_unsat_core_extrapolate_axioms    false
% 2.59/0.94  --bmc1_out_stat                         full
% 2.59/0.94  --bmc1_ground_init                      false
% 2.59/0.94  --bmc1_pre_inst_next_state              false
% 2.59/0.94  --bmc1_pre_inst_state                   false
% 2.59/0.94  --bmc1_pre_inst_reach_state             false
% 2.59/0.94  --bmc1_out_unsat_core                   false
% 2.59/0.94  --bmc1_aig_witness_out                  false
% 2.59/0.94  --bmc1_verbose                          false
% 2.59/0.94  --bmc1_dump_clauses_tptp                false
% 2.59/0.94  --bmc1_dump_unsat_core_tptp             false
% 2.59/0.94  --bmc1_dump_file                        -
% 2.59/0.94  --bmc1_ucm_expand_uc_limit              128
% 2.59/0.94  --bmc1_ucm_n_expand_iterations          6
% 2.59/0.94  --bmc1_ucm_extend_mode                  1
% 2.59/0.94  --bmc1_ucm_init_mode                    2
% 2.59/0.94  --bmc1_ucm_cone_mode                    none
% 2.59/0.94  --bmc1_ucm_reduced_relation_type        0
% 2.59/0.94  --bmc1_ucm_relax_model                  4
% 2.59/0.94  --bmc1_ucm_full_tr_after_sat            true
% 2.59/0.94  --bmc1_ucm_expand_neg_assumptions       false
% 2.59/0.94  --bmc1_ucm_layered_model                none
% 2.59/0.94  --bmc1_ucm_max_lemma_size               10
% 2.59/0.94  
% 2.59/0.94  ------ AIG Options
% 2.59/0.94  
% 2.59/0.94  --aig_mode                              false
% 2.59/0.94  
% 2.59/0.94  ------ Instantiation Options
% 2.59/0.94  
% 2.59/0.94  --instantiation_flag                    true
% 2.59/0.94  --inst_sos_flag                         false
% 2.59/0.94  --inst_sos_phase                        true
% 2.59/0.94  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.59/0.94  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.59/0.94  --inst_lit_sel_side                     none
% 2.59/0.94  --inst_solver_per_active                1400
% 2.59/0.94  --inst_solver_calls_frac                1.
% 2.59/0.94  --inst_passive_queue_type               priority_queues
% 2.59/0.94  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.59/0.94  --inst_passive_queues_freq              [25;2]
% 2.59/0.94  --inst_dismatching                      true
% 2.59/0.94  --inst_eager_unprocessed_to_passive     true
% 2.59/0.94  --inst_prop_sim_given                   true
% 2.59/0.94  --inst_prop_sim_new                     false
% 2.59/0.94  --inst_subs_new                         false
% 2.59/0.94  --inst_eq_res_simp                      false
% 2.59/0.94  --inst_subs_given                       false
% 2.59/0.94  --inst_orphan_elimination               true
% 2.59/0.94  --inst_learning_loop_flag               true
% 2.59/0.94  --inst_learning_start                   3000
% 2.59/0.94  --inst_learning_factor                  2
% 2.59/0.94  --inst_start_prop_sim_after_learn       3
% 2.59/0.94  --inst_sel_renew                        solver
% 2.59/0.94  --inst_lit_activity_flag                true
% 2.59/0.94  --inst_restr_to_given                   false
% 2.59/0.94  --inst_activity_threshold               500
% 2.59/0.94  --inst_out_proof                        true
% 2.59/0.94  
% 2.59/0.94  ------ Resolution Options
% 2.59/0.94  
% 2.59/0.94  --resolution_flag                       false
% 2.59/0.94  --res_lit_sel                           adaptive
% 2.59/0.94  --res_lit_sel_side                      none
% 2.59/0.94  --res_ordering                          kbo
% 2.59/0.94  --res_to_prop_solver                    active
% 2.59/0.94  --res_prop_simpl_new                    false
% 2.59/0.94  --res_prop_simpl_given                  true
% 2.59/0.94  --res_passive_queue_type                priority_queues
% 2.59/0.94  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.59/0.94  --res_passive_queues_freq               [15;5]
% 2.59/0.94  --res_forward_subs                      full
% 2.59/0.94  --res_backward_subs                     full
% 2.59/0.94  --res_forward_subs_resolution           true
% 2.59/0.94  --res_backward_subs_resolution          true
% 2.59/0.94  --res_orphan_elimination                true
% 2.59/0.94  --res_time_limit                        2.
% 2.59/0.94  --res_out_proof                         true
% 2.59/0.94  
% 2.59/0.94  ------ Superposition Options
% 2.59/0.94  
% 2.59/0.94  --superposition_flag                    true
% 2.59/0.94  --sup_passive_queue_type                priority_queues
% 2.59/0.94  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.59/0.94  --sup_passive_queues_freq               [8;1;4]
% 2.59/0.94  --demod_completeness_check              fast
% 2.59/0.94  --demod_use_ground                      true
% 2.59/0.94  --sup_to_prop_solver                    passive
% 2.59/0.94  --sup_prop_simpl_new                    true
% 2.59/0.94  --sup_prop_simpl_given                  true
% 2.59/0.94  --sup_fun_splitting                     false
% 2.59/0.94  --sup_smt_interval                      50000
% 2.59/0.94  
% 2.59/0.94  ------ Superposition Simplification Setup
% 2.59/0.94  
% 2.59/0.94  --sup_indices_passive                   []
% 2.59/0.94  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.94  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.94  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.59/0.94  --sup_full_triv                         [TrivRules;PropSubs]
% 2.59/0.94  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.94  --sup_full_bw                           [BwDemod]
% 2.59/0.94  --sup_immed_triv                        [TrivRules]
% 2.59/0.94  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.59/0.94  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.94  --sup_immed_bw_main                     []
% 2.59/0.94  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.94  --sup_input_triv                        [Unflattening;TrivRules]
% 2.59/0.94  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.59/0.94  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.59/0.94  
% 2.59/0.94  ------ Combination Options
% 2.59/0.94  
% 2.59/0.94  --comb_res_mult                         3
% 2.59/0.94  --comb_sup_mult                         2
% 2.59/0.94  --comb_inst_mult                        10
% 2.59/0.94  
% 2.59/0.94  ------ Debug Options
% 2.59/0.94  
% 2.59/0.94  --dbg_backtrace                         false
% 2.59/0.94  --dbg_dump_prop_clauses                 false
% 2.59/0.94  --dbg_dump_prop_clauses_file            -
% 2.59/0.94  --dbg_out_stat                          false
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  ------ Proving...
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  % SZS status Theorem for theBenchmark.p
% 2.59/0.94  
% 2.59/0.94   Resolution empty clause
% 2.59/0.94  
% 2.59/0.94  % SZS output start CNFRefutation for theBenchmark.p
% 2.59/0.94  
% 2.59/0.94  fof(f1,axiom,(
% 2.59/0.94    v1_xboole_0(k1_xboole_0)),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f47,plain,(
% 2.59/0.94    v1_xboole_0(k1_xboole_0)),
% 2.59/0.94    inference(cnf_transformation,[],[f1])).
% 2.59/0.94  
% 2.59/0.94  fof(f20,conjecture,(
% 2.59/0.94    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f21,negated_conjecture,(
% 2.59/0.94    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.59/0.94    inference(negated_conjecture,[],[f20])).
% 2.59/0.94  
% 2.59/0.94  fof(f22,plain,(
% 2.59/0.94    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.59/0.94    inference(pure_predicate_removal,[],[f21])).
% 2.59/0.94  
% 2.59/0.94  fof(f37,plain,(
% 2.59/0.94    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.59/0.94    inference(ennf_transformation,[],[f22])).
% 2.59/0.94  
% 2.59/0.94  fof(f38,plain,(
% 2.59/0.94    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.59/0.94    inference(flattening,[],[f37])).
% 2.59/0.94  
% 2.59/0.94  fof(f45,plain,(
% 2.59/0.94    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.59/0.94    introduced(choice_axiom,[])).
% 2.59/0.94  
% 2.59/0.94  fof(f46,plain,(
% 2.59/0.94    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.59/0.94    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f45])).
% 2.59/0.94  
% 2.59/0.94  fof(f74,plain,(
% 2.59/0.94    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.59/0.94    inference(cnf_transformation,[],[f46])).
% 2.59/0.94  
% 2.59/0.94  fof(f4,axiom,(
% 2.59/0.94    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f52,plain,(
% 2.59/0.94    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f4])).
% 2.59/0.94  
% 2.59/0.94  fof(f5,axiom,(
% 2.59/0.94    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f53,plain,(
% 2.59/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f5])).
% 2.59/0.94  
% 2.59/0.94  fof(f6,axiom,(
% 2.59/0.94    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f54,plain,(
% 2.59/0.94    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f6])).
% 2.59/0.94  
% 2.59/0.94  fof(f77,plain,(
% 2.59/0.94    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.59/0.94    inference(definition_unfolding,[],[f53,f54])).
% 2.59/0.94  
% 2.59/0.94  fof(f78,plain,(
% 2.59/0.94    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.59/0.94    inference(definition_unfolding,[],[f52,f77])).
% 2.59/0.94  
% 2.59/0.94  fof(f86,plain,(
% 2.59/0.94    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.59/0.94    inference(definition_unfolding,[],[f74,f78])).
% 2.59/0.94  
% 2.59/0.94  fof(f16,axiom,(
% 2.59/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f23,plain,(
% 2.59/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.59/0.94    inference(pure_predicate_removal,[],[f16])).
% 2.59/0.94  
% 2.59/0.94  fof(f32,plain,(
% 2.59/0.94    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.94    inference(ennf_transformation,[],[f23])).
% 2.59/0.94  
% 2.59/0.94  fof(f69,plain,(
% 2.59/0.94    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f32])).
% 2.59/0.94  
% 2.59/0.94  fof(f11,axiom,(
% 2.59/0.94    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f27,plain,(
% 2.59/0.94    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.59/0.94    inference(ennf_transformation,[],[f11])).
% 2.59/0.94  
% 2.59/0.94  fof(f44,plain,(
% 2.59/0.94    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.59/0.94    inference(nnf_transformation,[],[f27])).
% 2.59/0.94  
% 2.59/0.94  fof(f63,plain,(
% 2.59/0.94    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f44])).
% 2.59/0.94  
% 2.59/0.94  fof(f15,axiom,(
% 2.59/0.94    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f31,plain,(
% 2.59/0.94    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.94    inference(ennf_transformation,[],[f15])).
% 2.59/0.94  
% 2.59/0.94  fof(f68,plain,(
% 2.59/0.94    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f31])).
% 2.59/0.94  
% 2.59/0.94  fof(f7,axiom,(
% 2.59/0.94    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f26,plain,(
% 2.59/0.94    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.59/0.94    inference(ennf_transformation,[],[f7])).
% 2.59/0.94  
% 2.59/0.94  fof(f41,plain,(
% 2.59/0.94    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.59/0.94    inference(nnf_transformation,[],[f26])).
% 2.59/0.94  
% 2.59/0.94  fof(f42,plain,(
% 2.59/0.94    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.59/0.94    inference(flattening,[],[f41])).
% 2.59/0.94  
% 2.59/0.94  fof(f55,plain,(
% 2.59/0.94    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f42])).
% 2.59/0.94  
% 2.59/0.94  fof(f83,plain,(
% 2.59/0.94    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 2.59/0.94    inference(definition_unfolding,[],[f55,f77,f78,f78,f77])).
% 2.59/0.94  
% 2.59/0.94  fof(f76,plain,(
% 2.59/0.94    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.59/0.94    inference(cnf_transformation,[],[f46])).
% 2.59/0.94  
% 2.59/0.94  fof(f85,plain,(
% 2.59/0.94    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.59/0.94    inference(definition_unfolding,[],[f76,f78,f78])).
% 2.59/0.94  
% 2.59/0.94  fof(f14,axiom,(
% 2.59/0.94    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f29,plain,(
% 2.59/0.94    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.59/0.94    inference(ennf_transformation,[],[f14])).
% 2.59/0.94  
% 2.59/0.94  fof(f30,plain,(
% 2.59/0.94    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.59/0.94    inference(flattening,[],[f29])).
% 2.59/0.94  
% 2.59/0.94  fof(f67,plain,(
% 2.59/0.94    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f30])).
% 2.59/0.94  
% 2.59/0.94  fof(f84,plain,(
% 2.59/0.94    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.59/0.94    inference(definition_unfolding,[],[f67,f78,f78])).
% 2.59/0.94  
% 2.59/0.94  fof(f73,plain,(
% 2.59/0.94    v1_funct_1(sK3)),
% 2.59/0.94    inference(cnf_transformation,[],[f46])).
% 2.59/0.94  
% 2.59/0.94  fof(f18,axiom,(
% 2.59/0.94    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f34,plain,(
% 2.59/0.94    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.94    inference(ennf_transformation,[],[f18])).
% 2.59/0.94  
% 2.59/0.94  fof(f71,plain,(
% 2.59/0.94    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f34])).
% 2.59/0.94  
% 2.59/0.94  fof(f12,axiom,(
% 2.59/0.94    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f28,plain,(
% 2.59/0.94    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.59/0.94    inference(ennf_transformation,[],[f12])).
% 2.59/0.94  
% 2.59/0.94  fof(f65,plain,(
% 2.59/0.94    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f28])).
% 2.59/0.94  
% 2.59/0.94  fof(f19,axiom,(
% 2.59/0.94    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f35,plain,(
% 2.59/0.94    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.59/0.94    inference(ennf_transformation,[],[f19])).
% 2.59/0.94  
% 2.59/0.94  fof(f36,plain,(
% 2.59/0.94    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 2.59/0.94    inference(flattening,[],[f35])).
% 2.59/0.94  
% 2.59/0.94  fof(f72,plain,(
% 2.59/0.94    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f36])).
% 2.59/0.94  
% 2.59/0.94  fof(f8,axiom,(
% 2.59/0.94    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f60,plain,(
% 2.59/0.94    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f8])).
% 2.59/0.94  
% 2.59/0.94  fof(f9,axiom,(
% 2.59/0.94    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f43,plain,(
% 2.59/0.94    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.59/0.94    inference(nnf_transformation,[],[f9])).
% 2.59/0.94  
% 2.59/0.94  fof(f61,plain,(
% 2.59/0.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.59/0.94    inference(cnf_transformation,[],[f43])).
% 2.59/0.94  
% 2.59/0.94  fof(f17,axiom,(
% 2.59/0.94    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f33,plain,(
% 2.59/0.94    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.59/0.94    inference(ennf_transformation,[],[f17])).
% 2.59/0.94  
% 2.59/0.94  fof(f70,plain,(
% 2.59/0.94    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f33])).
% 2.59/0.94  
% 2.59/0.94  fof(f2,axiom,(
% 2.59/0.94    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f25,plain,(
% 2.59/0.94    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.59/0.94    inference(ennf_transformation,[],[f2])).
% 2.59/0.94  
% 2.59/0.94  fof(f48,plain,(
% 2.59/0.94    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f25])).
% 2.59/0.94  
% 2.59/0.94  fof(f13,axiom,(
% 2.59/0.94    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 2.59/0.94    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.59/0.94  
% 2.59/0.94  fof(f66,plain,(
% 2.59/0.94    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 2.59/0.94    inference(cnf_transformation,[],[f13])).
% 2.59/0.94  
% 2.59/0.94  cnf(c_0,plain,
% 2.59/0.94      ( v1_xboole_0(k1_xboole_0) ),
% 2.59/0.94      inference(cnf_transformation,[],[f47]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1150,plain,
% 2.59/0.94      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_25,negated_conjecture,
% 2.59/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.59/0.94      inference(cnf_transformation,[],[f86]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1132,plain,
% 2.59/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_19,plain,
% 2.59/0.94      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.59/0.94      inference(cnf_transformation,[],[f69]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_14,plain,
% 2.59/0.94      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.59/0.94      inference(cnf_transformation,[],[f63]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_341,plain,
% 2.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.94      | r1_tarski(k1_relat_1(X0),X1)
% 2.59/0.94      | ~ v1_relat_1(X0) ),
% 2.59/0.94      inference(resolution,[status(thm)],[c_19,c_14]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_18,plain,
% 2.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.59/0.94      inference(cnf_transformation,[],[f68]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_345,plain,
% 2.59/0.94      ( r1_tarski(k1_relat_1(X0),X1)
% 2.59/0.94      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.59/0.94      inference(global_propositional_subsumption,[status(thm)],[c_341,c_18]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_346,plain,
% 2.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.94      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.59/0.94      inference(renaming,[status(thm)],[c_345]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1130,plain,
% 2.59/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.59/0.94      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1495,plain,
% 2.59/0.94      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_1132,c_1130]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_9,plain,
% 2.59/0.94      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 2.59/0.94      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.59/0.94      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.59/0.94      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.59/0.94      | k1_xboole_0 = X0 ),
% 2.59/0.94      inference(cnf_transformation,[],[f83]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1142,plain,
% 2.59/0.94      ( k2_enumset1(X0,X0,X0,X1) = X2
% 2.59/0.94      | k2_enumset1(X1,X1,X1,X1) = X2
% 2.59/0.94      | k2_enumset1(X0,X0,X0,X0) = X2
% 2.59/0.94      | k1_xboole_0 = X2
% 2.59/0.94      | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_3216,plain,
% 2.59/0.94      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.59/0.94      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_1495,c_1142]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_28,plain,
% 2.59/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_23,negated_conjecture,
% 2.59/0.94      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.59/0.94      inference(cnf_transformation,[],[f85]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_17,plain,
% 2.59/0.94      ( ~ v1_funct_1(X0)
% 2.59/0.94      | ~ v1_relat_1(X0)
% 2.59/0.94      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.59/0.94      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.59/0.94      inference(cnf_transformation,[],[f84]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_26,negated_conjecture,
% 2.59/0.94      ( v1_funct_1(sK3) ),
% 2.59/0.94      inference(cnf_transformation,[],[f73]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_322,plain,
% 2.59/0.94      ( ~ v1_relat_1(X0)
% 2.59/0.94      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.59/0.94      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.59/0.94      | sK3 != X0 ),
% 2.59/0.94      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_323,plain,
% 2.59/0.94      ( ~ v1_relat_1(sK3)
% 2.59/0.94      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.59/0.94      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.59/0.94      inference(unflattening,[status(thm)],[c_322]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_324,plain,
% 2.59/0.94      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.59/0.94      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.59/0.94      | v1_relat_1(sK3) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_323]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_326,plain,
% 2.59/0.94      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.59/0.94      | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
% 2.59/0.94      | v1_relat_1(sK3) != iProver_top ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_324]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1302,plain,
% 2.59/0.94      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.59/0.94      | v1_relat_1(sK3) ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_18]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1303,plain,
% 2.59/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 2.59/0.94      | v1_relat_1(sK3) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_1302]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_21,plain,
% 2.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.94      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.59/0.94      inference(cnf_transformation,[],[f71]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1376,plain,
% 2.59/0.94      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.59/0.94      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_21]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1467,plain,
% 2.59/0.94      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.59/0.94      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_1376]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_614,plain,
% 2.59/0.94      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.59/0.94      theory(equality) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1354,plain,
% 2.59/0.94      ( ~ r1_tarski(X0,X1)
% 2.59/0.94      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.59/0.94      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 2.59/0.94      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_614]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1466,plain,
% 2.59/0.94      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.59/0.94      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 2.59/0.94      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.59/0.94      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_1354]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1557,plain,
% 2.59/0.94      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.59/0.94      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.59/0.94      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.59/0.94      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_1466]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_15,plain,
% 2.59/0.94      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.59/0.94      inference(cnf_transformation,[],[f65]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1411,plain,
% 2.59/0.94      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_15]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1558,plain,
% 2.59/0.94      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.59/0.94      inference(instantiation,[status(thm)],[c_1411]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_3549,plain,
% 2.59/0.94      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.59/0.94      inference(global_propositional_subsumption,
% 2.59/0.94                [status(thm)],
% 2.59/0.94                [c_3216,c_25,c_28,c_23,c_326,c_1302,c_1303,c_1467,c_1557,
% 2.59/0.94                 c_1558]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_22,plain,
% 2.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.94      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 2.59/0.94      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 2.59/0.94      inference(cnf_transformation,[],[f72]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1134,plain,
% 2.59/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.59/0.94      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 2.59/0.94      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1980,plain,
% 2.59/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 2.59/0.94      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_1132,c_1134]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_3557,plain,
% 2.59/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 2.59/0.94      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 2.59/0.94      inference(demodulation,[status(thm)],[c_3549,c_1980]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_10,plain,
% 2.59/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.59/0.94      inference(cnf_transformation,[],[f60]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1141,plain,
% 2.59/0.94      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_12,plain,
% 2.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.59/0.94      inference(cnf_transformation,[],[f61]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1139,plain,
% 2.59/0.94      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.59/0.94      | r1_tarski(X0,X1) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1607,plain,
% 2.59/0.94      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_1141,c_1139]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_3603,plain,
% 2.59/0.94      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top ),
% 2.59/0.94      inference(global_propositional_subsumption,[status(thm)],[c_3557,c_1607]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_20,plain,
% 2.59/0.94      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.59/0.94      | ~ v1_xboole_0(X1)
% 2.59/0.94      | v1_xboole_0(X0) ),
% 2.59/0.94      inference(cnf_transformation,[],[f70]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1136,plain,
% 2.59/0.94      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.59/0.94      | v1_xboole_0(X1) != iProver_top
% 2.59/0.94      | v1_xboole_0(X0) = iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_3612,plain,
% 2.59/0.94      ( v1_xboole_0(X0) != iProver_top | v1_xboole_0(sK3) = iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_3603,c_1136]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_4053,plain,
% 2.59/0.94      ( v1_xboole_0(sK3) = iProver_top ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_1150,c_3612]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1,plain,
% 2.59/0.94      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.59/0.94      inference(cnf_transformation,[],[f48]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1149,plain,
% 2.59/0.94      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_4058,plain,
% 2.59/0.94      ( sK3 = k1_xboole_0 ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_4053,c_1149]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1135,plain,
% 2.59/0.94      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.59/0.94      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2193,plain,
% 2.59/0.94      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.59/0.94      inference(superposition,[status(thm)],[c_1132,c_1135]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_1133,plain,
% 2.59/0.94      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.59/0.94      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_2390,plain,
% 2.59/0.94      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.59/0.94      inference(demodulation,[status(thm)],[c_2193,c_1133]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_4155,plain,
% 2.59/0.94      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.59/0.94      inference(demodulation,[status(thm)],[c_4058,c_2390]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_16,plain,
% 2.59/0.94      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.59/0.94      inference(cnf_transformation,[],[f66]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_4165,plain,
% 2.59/0.94      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.59/0.94      inference(demodulation,[status(thm)],[c_4155,c_16]) ).
% 2.59/0.94  
% 2.59/0.94  cnf(c_4252,plain,
% 2.59/0.94      ( $false ),
% 2.59/0.94      inference(forward_subsumption_resolution,[status(thm)],[c_4165,c_1607]) ).
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  % SZS output end CNFRefutation for theBenchmark.p
% 2.59/0.94  
% 2.59/0.94  ------                               Statistics
% 2.59/0.94  
% 2.59/0.94  ------ General
% 2.59/0.94  
% 2.59/0.94  abstr_ref_over_cycles:                  0
% 2.59/0.94  abstr_ref_under_cycles:                 0
% 2.59/0.94  gc_basic_clause_elim:                   0
% 2.59/0.94  forced_gc_time:                         0
% 2.59/0.94  parsing_time:                           0.009
% 2.59/0.94  unif_index_cands_time:                  0.
% 2.59/0.94  unif_index_add_time:                    0.
% 2.59/0.94  orderings_time:                         0.
% 2.59/0.94  out_proof_time:                         0.007
% 2.59/0.94  total_time:                             0.146
% 2.59/0.94  num_of_symbols:                         50
% 2.59/0.94  num_of_terms:                           3678
% 2.59/0.94  
% 2.59/0.94  ------ Preprocessing
% 2.59/0.94  
% 2.59/0.94  num_of_splits:                          0
% 2.59/0.94  num_of_split_atoms:                     0
% 2.59/0.94  num_of_reused_defs:                     0
% 2.59/0.94  num_eq_ax_congr_red:                    8
% 2.59/0.94  num_of_sem_filtered_clauses:            1
% 2.59/0.94  num_of_subtypes:                        0
% 2.59/0.94  monotx_restored_types:                  0
% 2.59/0.94  sat_num_of_epr_types:                   0
% 2.59/0.94  sat_num_of_non_cyclic_types:            0
% 2.59/0.94  sat_guarded_non_collapsed_types:        0
% 2.59/0.94  num_pure_diseq_elim:                    0
% 2.59/0.94  simp_replaced_by:                       0
% 2.59/0.94  res_preprocessed:                       124
% 2.59/0.94  prep_upred:                             0
% 2.59/0.94  prep_unflattend:                        3
% 2.59/0.94  smt_new_axioms:                         0
% 2.59/0.94  pred_elim_cands:                        4
% 2.59/0.94  pred_elim:                              2
% 2.59/0.94  pred_elim_cl:                           3
% 2.59/0.94  pred_elim_cycles:                       4
% 2.59/0.94  merged_defs:                            8
% 2.59/0.94  merged_defs_ncl:                        0
% 2.59/0.94  bin_hyper_res:                          8
% 2.59/0.94  prep_cycles:                            4
% 2.59/0.94  pred_elim_time:                         0.002
% 2.59/0.94  splitting_time:                         0.
% 2.59/0.94  sem_filter_time:                        0.
% 2.59/0.94  monotx_time:                            0.001
% 2.59/0.94  subtype_inf_time:                       0.
% 2.59/0.94  
% 2.59/0.94  ------ Problem properties
% 2.59/0.94  
% 2.59/0.94  clauses:                                23
% 2.59/0.94  conjectures:                            3
% 2.59/0.94  epr:                                    5
% 2.59/0.94  horn:                                   22
% 2.59/0.94  ground:                                 4
% 2.59/0.94  unary:                                  11
% 2.59/0.94  binary:                                 7
% 2.59/0.94  lits:                                   42
% 2.59/0.94  lits_eq:                                11
% 2.59/0.94  fd_pure:                                0
% 2.59/0.94  fd_pseudo:                              0
% 2.59/0.94  fd_cond:                                1
% 2.59/0.94  fd_pseudo_cond:                         2
% 2.59/0.94  ac_symbols:                             0
% 2.59/0.94  
% 2.59/0.94  ------ Propositional Solver
% 2.59/0.94  
% 2.59/0.94  prop_solver_calls:                      26
% 2.59/0.94  prop_fast_solver_calls:                 639
% 2.59/0.94  smt_solver_calls:                       0
% 2.59/0.94  smt_fast_solver_calls:                  0
% 2.59/0.94  prop_num_of_clauses:                    1540
% 2.59/0.94  prop_preprocess_simplified:             5507
% 2.59/0.94  prop_fo_subsumed:                       8
% 2.59/0.94  prop_solver_time:                       0.
% 2.59/0.94  smt_solver_time:                        0.
% 2.59/0.94  smt_fast_solver_time:                   0.
% 2.59/0.94  prop_fast_solver_time:                  0.
% 2.59/0.94  prop_unsat_core_time:                   0.
% 2.59/0.94  
% 2.59/0.94  ------ QBF
% 2.59/0.94  
% 2.59/0.94  qbf_q_res:                              0
% 2.59/0.94  qbf_num_tautologies:                    0
% 2.59/0.94  qbf_prep_cycles:                        0
% 2.59/0.94  
% 2.59/0.94  ------ BMC1
% 2.59/0.94  
% 2.59/0.94  bmc1_current_bound:                     -1
% 2.59/0.94  bmc1_last_solved_bound:                 -1
% 2.59/0.94  bmc1_unsat_core_size:                   -1
% 2.59/0.94  bmc1_unsat_core_parents_size:           -1
% 2.59/0.94  bmc1_merge_next_fun:                    0
% 2.59/0.94  bmc1_unsat_core_clauses_time:           0.
% 2.59/0.94  
% 2.59/0.94  ------ Instantiation
% 2.59/0.94  
% 2.59/0.94  inst_num_of_clauses:                    461
% 2.59/0.94  inst_num_in_passive:                    65
% 2.59/0.94  inst_num_in_active:                     258
% 2.59/0.94  inst_num_in_unprocessed:                141
% 2.59/0.94  inst_num_of_loops:                      270
% 2.59/0.94  inst_num_of_learning_restarts:          0
% 2.59/0.94  inst_num_moves_active_passive:          10
% 2.59/0.94  inst_lit_activity:                      0
% 2.59/0.94  inst_lit_activity_moves:                0
% 2.59/0.94  inst_num_tautologies:                   0
% 2.59/0.94  inst_num_prop_implied:                  0
% 2.59/0.94  inst_num_existing_simplified:           0
% 2.59/0.94  inst_num_eq_res_simplified:             0
% 2.59/0.94  inst_num_child_elim:                    0
% 2.59/0.94  inst_num_of_dismatching_blockings:      175
% 2.59/0.94  inst_num_of_non_proper_insts:           611
% 2.59/0.94  inst_num_of_duplicates:                 0
% 2.59/0.94  inst_inst_num_from_inst_to_res:         0
% 2.59/0.94  inst_dismatching_checking_time:         0.
% 2.59/0.94  
% 2.59/0.94  ------ Resolution
% 2.59/0.94  
% 2.59/0.94  res_num_of_clauses:                     0
% 2.59/0.94  res_num_in_passive:                     0
% 2.59/0.94  res_num_in_active:                      0
% 2.59/0.94  res_num_of_loops:                       128
% 2.59/0.94  res_forward_subset_subsumed:            75
% 2.59/0.94  res_backward_subset_subsumed:           6
% 2.59/0.94  res_forward_subsumed:                   0
% 2.59/0.94  res_backward_subsumed:                  0
% 2.59/0.94  res_forward_subsumption_resolution:     0
% 2.59/0.94  res_backward_subsumption_resolution:    0
% 2.59/0.94  res_clause_to_clause_subsumption:       204
% 2.59/0.94  res_orphan_elimination:                 0
% 2.59/0.94  res_tautology_del:                      46
% 2.59/0.94  res_num_eq_res_simplified:              0
% 2.59/0.94  res_num_sel_changes:                    0
% 2.59/0.94  res_moves_from_active_to_pass:          0
% 2.59/0.94  
% 2.59/0.94  ------ Superposition
% 2.59/0.94  
% 2.59/0.94  sup_time_total:                         0.
% 2.59/0.94  sup_time_generating:                    0.
% 2.59/0.94  sup_time_sim_full:                      0.
% 2.59/0.94  sup_time_sim_immed:                     0.
% 2.59/0.94  
% 2.59/0.94  sup_num_of_clauses:                     49
% 2.59/0.94  sup_num_in_active:                      28
% 2.59/0.94  sup_num_in_passive:                     21
% 2.59/0.94  sup_num_of_loops:                       52
% 2.59/0.94  sup_fw_superposition:                   48
% 2.59/0.94  sup_bw_superposition:                   21
% 2.59/0.94  sup_immediate_simplified:               17
% 2.59/0.94  sup_given_eliminated:                   1
% 2.59/0.94  comparisons_done:                       0
% 2.59/0.94  comparisons_avoided:                    0
% 2.59/0.94  
% 2.59/0.94  ------ Simplifications
% 2.59/0.94  
% 2.59/0.94  
% 2.59/0.94  sim_fw_subset_subsumed:                 3
% 2.59/0.94  sim_bw_subset_subsumed:                 3
% 2.59/0.94  sim_fw_subsumed:                        11
% 2.59/0.94  sim_bw_subsumed:                        0
% 2.59/0.94  sim_fw_subsumption_res:                 1
% 2.59/0.94  sim_bw_subsumption_res:                 0
% 2.59/0.94  sim_tautology_del:                      2
% 2.59/0.94  sim_eq_tautology_del:                   6
% 2.59/0.94  sim_eq_res_simp:                        0
% 2.59/0.94  sim_fw_demodulated:                     3
% 2.59/0.94  sim_bw_demodulated:                     24
% 2.59/0.94  sim_light_normalised:                   3
% 2.59/0.94  sim_joinable_taut:                      0
% 2.59/0.94  sim_joinable_simp:                      0
% 2.59/0.94  sim_ac_normalised:                      0
% 2.59/0.94  sim_smt_subsumption:                    0
% 2.59/0.94  
%------------------------------------------------------------------------------
