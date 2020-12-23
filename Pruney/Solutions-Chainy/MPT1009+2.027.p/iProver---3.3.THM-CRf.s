%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:33 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  146 (1042 expanded)
%              Number of clauses        :   77 ( 230 expanded)
%              Number of leaves         :   19 ( 255 expanded)
%              Depth                    :   21
%              Number of atoms          :  381 (2500 expanded)
%              Number of equality atoms :  196 (1209 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
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

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f41,plain,
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

fof(f42,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f41])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f73])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f70,f74])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f6])).

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

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X1,X1,X1,X2) = X0
      | k2_enumset1(X2,X2,X2,X2) = X0
      | k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f50,f73,f74,f74,f73])).

fof(f72,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f72,f74,f74])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f64,f74,f74])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f37])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1023,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_313,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_15])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_317,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_313,c_19])).

cnf(c_318,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_317])).

cnf(c_1021,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_318])).

cnf(c_1344,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1023,c_1021])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1031,plain,
    ( k2_enumset1(X0,X0,X0,X1) = X2
    | k2_enumset1(X1,X1,X1,X1) = X2
    | k2_enumset1(X0,X0,X0,X0) = X2
    | k1_xboole_0 = X2
    | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2941,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1344,c_1031])).

cnf(c_3271,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2941,c_1023])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1166,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1220,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1285,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(c_565,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1206,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_1284,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1206])).

cnf(c_1429,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1284])).

cnf(c_16,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1232,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1430,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_294,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_26])).

cnf(c_295,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_294])).

cnf(c_1022,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_296,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_295])).

cnf(c_1167,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1166])).

cnf(c_1176,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1022,c_28,c_296,c_1167])).

cnf(c_1177,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1176])).

cnf(c_3264,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2941,c_1177])).

cnf(c_3324,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3271,c_25,c_23,c_1166,c_1285,c_1429,c_1430,c_3264])).

cnf(c_10,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1025,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1853,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1023,c_1025])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1029,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2344,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1853,c_1029])).

cnf(c_2489,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10,c_2344])).

cnf(c_3328,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3324,c_2489])).

cnf(c_11,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_59,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_60,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_72,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_74,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_72])).

cnf(c_1201,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X2),X3)
    | X3 != X1
    | k1_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_565])).

cnf(c_2549,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK3),X2)
    | X2 != X1
    | k1_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1201])).

cnf(c_2550,plain,
    ( X0 != X1
    | k1_relat_1(sK3) != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2549])).

cnf(c_2552,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2550])).

cnf(c_3452,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3328,c_25,c_23,c_59,c_60,c_74,c_1166,c_1285,c_1429,c_1430,c_2489,c_2552,c_3264])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1038,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3457,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3452,c_1038])).

cnf(c_73,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2074,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2076,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2074])).

cnf(c_2501,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2489])).

cnf(c_2551,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2549])).

cnf(c_4595,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4807,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3457,c_25,c_23,c_59,c_60,c_73,c_1166,c_1285,c_1429,c_1430,c_2076,c_2501,c_2551,c_3264,c_4595])).

cnf(c_1026,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2150,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1023,c_1026])).

cnf(c_1024,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2176,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2150,c_1024])).

cnf(c_4820,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4807,c_2176])).

cnf(c_17,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_4834,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4820,c_17])).

cnf(c_1036,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_5469,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4834,c_1036])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:24:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.41/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.01  
% 3.41/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.41/1.01  
% 3.41/1.01  ------  iProver source info
% 3.41/1.01  
% 3.41/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.41/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.41/1.01  git: non_committed_changes: false
% 3.41/1.01  git: last_make_outside_of_git: false
% 3.41/1.01  
% 3.41/1.01  ------ 
% 3.41/1.01  
% 3.41/1.01  ------ Input Options
% 3.41/1.01  
% 3.41/1.01  --out_options                           all
% 3.41/1.01  --tptp_safe_out                         true
% 3.41/1.01  --problem_path                          ""
% 3.41/1.01  --include_path                          ""
% 3.41/1.01  --clausifier                            res/vclausify_rel
% 3.41/1.01  --clausifier_options                    --mode clausify
% 3.41/1.01  --stdin                                 false
% 3.41/1.01  --stats_out                             all
% 3.41/1.01  
% 3.41/1.01  ------ General Options
% 3.41/1.01  
% 3.41/1.01  --fof                                   false
% 3.41/1.01  --time_out_real                         305.
% 3.41/1.01  --time_out_virtual                      -1.
% 3.41/1.01  --symbol_type_check                     false
% 3.41/1.01  --clausify_out                          false
% 3.41/1.01  --sig_cnt_out                           false
% 3.41/1.01  --trig_cnt_out                          false
% 3.41/1.01  --trig_cnt_out_tolerance                1.
% 3.41/1.01  --trig_cnt_out_sk_spl                   false
% 3.41/1.01  --abstr_cl_out                          false
% 3.41/1.01  
% 3.41/1.01  ------ Global Options
% 3.41/1.01  
% 3.41/1.01  --schedule                              default
% 3.41/1.01  --add_important_lit                     false
% 3.41/1.01  --prop_solver_per_cl                    1000
% 3.41/1.01  --min_unsat_core                        false
% 3.41/1.01  --soft_assumptions                      false
% 3.41/1.01  --soft_lemma_size                       3
% 3.41/1.01  --prop_impl_unit_size                   0
% 3.41/1.01  --prop_impl_unit                        []
% 3.41/1.01  --share_sel_clauses                     true
% 3.41/1.01  --reset_solvers                         false
% 3.41/1.01  --bc_imp_inh                            [conj_cone]
% 3.41/1.01  --conj_cone_tolerance                   3.
% 3.41/1.01  --extra_neg_conj                        none
% 3.41/1.01  --large_theory_mode                     true
% 3.41/1.01  --prolific_symb_bound                   200
% 3.41/1.01  --lt_threshold                          2000
% 3.41/1.01  --clause_weak_htbl                      true
% 3.41/1.01  --gc_record_bc_elim                     false
% 3.41/1.01  
% 3.41/1.01  ------ Preprocessing Options
% 3.41/1.01  
% 3.41/1.01  --preprocessing_flag                    true
% 3.41/1.01  --time_out_prep_mult                    0.1
% 3.41/1.01  --splitting_mode                        input
% 3.41/1.01  --splitting_grd                         true
% 3.41/1.01  --splitting_cvd                         false
% 3.41/1.01  --splitting_cvd_svl                     false
% 3.41/1.01  --splitting_nvd                         32
% 3.41/1.01  --sub_typing                            true
% 3.41/1.01  --prep_gs_sim                           true
% 3.41/1.01  --prep_unflatten                        true
% 3.41/1.01  --prep_res_sim                          true
% 3.41/1.01  --prep_upred                            true
% 3.41/1.01  --prep_sem_filter                       exhaustive
% 3.41/1.01  --prep_sem_filter_out                   false
% 3.41/1.01  --pred_elim                             true
% 3.41/1.01  --res_sim_input                         true
% 3.41/1.01  --eq_ax_congr_red                       true
% 3.41/1.01  --pure_diseq_elim                       true
% 3.41/1.01  --brand_transform                       false
% 3.41/1.01  --non_eq_to_eq                          false
% 3.41/1.01  --prep_def_merge                        true
% 3.41/1.01  --prep_def_merge_prop_impl              false
% 3.41/1.01  --prep_def_merge_mbd                    true
% 3.41/1.01  --prep_def_merge_tr_red                 false
% 3.41/1.01  --prep_def_merge_tr_cl                  false
% 3.41/1.01  --smt_preprocessing                     true
% 3.41/1.01  --smt_ac_axioms                         fast
% 3.41/1.01  --preprocessed_out                      false
% 3.41/1.01  --preprocessed_stats                    false
% 3.41/1.01  
% 3.41/1.01  ------ Abstraction refinement Options
% 3.41/1.01  
% 3.41/1.01  --abstr_ref                             []
% 3.41/1.01  --abstr_ref_prep                        false
% 3.41/1.01  --abstr_ref_until_sat                   false
% 3.41/1.01  --abstr_ref_sig_restrict                funpre
% 3.41/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/1.01  --abstr_ref_under                       []
% 3.41/1.01  
% 3.41/1.01  ------ SAT Options
% 3.41/1.01  
% 3.41/1.01  --sat_mode                              false
% 3.41/1.01  --sat_fm_restart_options                ""
% 3.41/1.01  --sat_gr_def                            false
% 3.41/1.01  --sat_epr_types                         true
% 3.41/1.01  --sat_non_cyclic_types                  false
% 3.41/1.01  --sat_finite_models                     false
% 3.41/1.01  --sat_fm_lemmas                         false
% 3.41/1.01  --sat_fm_prep                           false
% 3.41/1.01  --sat_fm_uc_incr                        true
% 3.41/1.01  --sat_out_model                         small
% 3.41/1.01  --sat_out_clauses                       false
% 3.41/1.01  
% 3.41/1.01  ------ QBF Options
% 3.41/1.01  
% 3.41/1.01  --qbf_mode                              false
% 3.41/1.01  --qbf_elim_univ                         false
% 3.41/1.01  --qbf_dom_inst                          none
% 3.41/1.01  --qbf_dom_pre_inst                      false
% 3.41/1.01  --qbf_sk_in                             false
% 3.41/1.01  --qbf_pred_elim                         true
% 3.41/1.01  --qbf_split                             512
% 3.41/1.01  
% 3.41/1.01  ------ BMC1 Options
% 3.41/1.01  
% 3.41/1.01  --bmc1_incremental                      false
% 3.41/1.01  --bmc1_axioms                           reachable_all
% 3.41/1.01  --bmc1_min_bound                        0
% 3.41/1.01  --bmc1_max_bound                        -1
% 3.41/1.01  --bmc1_max_bound_default                -1
% 3.41/1.01  --bmc1_symbol_reachability              true
% 3.41/1.01  --bmc1_property_lemmas                  false
% 3.41/1.01  --bmc1_k_induction                      false
% 3.41/1.01  --bmc1_non_equiv_states                 false
% 3.41/1.01  --bmc1_deadlock                         false
% 3.41/1.01  --bmc1_ucm                              false
% 3.41/1.01  --bmc1_add_unsat_core                   none
% 3.41/1.01  --bmc1_unsat_core_children              false
% 3.41/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/1.01  --bmc1_out_stat                         full
% 3.41/1.01  --bmc1_ground_init                      false
% 3.41/1.01  --bmc1_pre_inst_next_state              false
% 3.41/1.01  --bmc1_pre_inst_state                   false
% 3.41/1.01  --bmc1_pre_inst_reach_state             false
% 3.41/1.01  --bmc1_out_unsat_core                   false
% 3.41/1.01  --bmc1_aig_witness_out                  false
% 3.41/1.01  --bmc1_verbose                          false
% 3.41/1.01  --bmc1_dump_clauses_tptp                false
% 3.41/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.41/1.01  --bmc1_dump_file                        -
% 3.41/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.41/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.41/1.01  --bmc1_ucm_extend_mode                  1
% 3.41/1.01  --bmc1_ucm_init_mode                    2
% 3.41/1.01  --bmc1_ucm_cone_mode                    none
% 3.41/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.41/1.01  --bmc1_ucm_relax_model                  4
% 3.41/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.41/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/1.01  --bmc1_ucm_layered_model                none
% 3.41/1.01  --bmc1_ucm_max_lemma_size               10
% 3.41/1.01  
% 3.41/1.01  ------ AIG Options
% 3.41/1.01  
% 3.41/1.01  --aig_mode                              false
% 3.41/1.01  
% 3.41/1.01  ------ Instantiation Options
% 3.41/1.01  
% 3.41/1.01  --instantiation_flag                    true
% 3.41/1.01  --inst_sos_flag                         false
% 3.41/1.01  --inst_sos_phase                        true
% 3.41/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/1.01  --inst_lit_sel_side                     num_symb
% 3.41/1.01  --inst_solver_per_active                1400
% 3.41/1.01  --inst_solver_calls_frac                1.
% 3.41/1.01  --inst_passive_queue_type               priority_queues
% 3.41/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/1.01  --inst_passive_queues_freq              [25;2]
% 3.41/1.01  --inst_dismatching                      true
% 3.41/1.01  --inst_eager_unprocessed_to_passive     true
% 3.41/1.01  --inst_prop_sim_given                   true
% 3.41/1.01  --inst_prop_sim_new                     false
% 3.41/1.01  --inst_subs_new                         false
% 3.41/1.01  --inst_eq_res_simp                      false
% 3.41/1.01  --inst_subs_given                       false
% 3.41/1.01  --inst_orphan_elimination               true
% 3.41/1.01  --inst_learning_loop_flag               true
% 3.41/1.01  --inst_learning_start                   3000
% 3.41/1.01  --inst_learning_factor                  2
% 3.41/1.01  --inst_start_prop_sim_after_learn       3
% 3.41/1.01  --inst_sel_renew                        solver
% 3.41/1.01  --inst_lit_activity_flag                true
% 3.41/1.01  --inst_restr_to_given                   false
% 3.41/1.01  --inst_activity_threshold               500
% 3.41/1.01  --inst_out_proof                        true
% 3.41/1.01  
% 3.41/1.01  ------ Resolution Options
% 3.41/1.01  
% 3.41/1.01  --resolution_flag                       true
% 3.41/1.01  --res_lit_sel                           adaptive
% 3.41/1.01  --res_lit_sel_side                      none
% 3.41/1.01  --res_ordering                          kbo
% 3.41/1.01  --res_to_prop_solver                    active
% 3.41/1.01  --res_prop_simpl_new                    false
% 3.41/1.01  --res_prop_simpl_given                  true
% 3.41/1.01  --res_passive_queue_type                priority_queues
% 3.41/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/1.01  --res_passive_queues_freq               [15;5]
% 3.41/1.01  --res_forward_subs                      full
% 3.41/1.01  --res_backward_subs                     full
% 3.41/1.01  --res_forward_subs_resolution           true
% 3.41/1.01  --res_backward_subs_resolution          true
% 3.41/1.01  --res_orphan_elimination                true
% 3.41/1.01  --res_time_limit                        2.
% 3.41/1.01  --res_out_proof                         true
% 3.41/1.01  
% 3.41/1.01  ------ Superposition Options
% 3.41/1.01  
% 3.41/1.01  --superposition_flag                    true
% 3.41/1.01  --sup_passive_queue_type                priority_queues
% 3.41/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.41/1.01  --demod_completeness_check              fast
% 3.41/1.01  --demod_use_ground                      true
% 3.41/1.01  --sup_to_prop_solver                    passive
% 3.41/1.01  --sup_prop_simpl_new                    true
% 3.41/1.01  --sup_prop_simpl_given                  true
% 3.41/1.01  --sup_fun_splitting                     false
% 3.41/1.01  --sup_smt_interval                      50000
% 3.41/1.01  
% 3.41/1.01  ------ Superposition Simplification Setup
% 3.41/1.01  
% 3.41/1.01  --sup_indices_passive                   []
% 3.41/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/1.01  --sup_full_bw                           [BwDemod]
% 3.41/1.01  --sup_immed_triv                        [TrivRules]
% 3.41/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/1.01  --sup_immed_bw_main                     []
% 3.41/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/1.01  
% 3.41/1.01  ------ Combination Options
% 3.41/1.01  
% 3.41/1.01  --comb_res_mult                         3
% 3.41/1.01  --comb_sup_mult                         2
% 3.41/1.01  --comb_inst_mult                        10
% 3.41/1.01  
% 3.41/1.01  ------ Debug Options
% 3.41/1.01  
% 3.41/1.01  --dbg_backtrace                         false
% 3.41/1.01  --dbg_dump_prop_clauses                 false
% 3.41/1.01  --dbg_dump_prop_clauses_file            -
% 3.41/1.01  --dbg_out_stat                          false
% 3.41/1.01  ------ Parsing...
% 3.41/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.41/1.01  
% 3.41/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.41/1.01  
% 3.41/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.41/1.01  
% 3.41/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/1.01  ------ Proving...
% 3.41/1.01  ------ Problem Properties 
% 3.41/1.01  
% 3.41/1.01  
% 3.41/1.01  clauses                                 23
% 3.41/1.01  conjectures                             3
% 3.41/1.01  EPR                                     4
% 3.41/1.01  Horn                                    21
% 3.41/1.01  unary                                   12
% 3.41/1.01  binary                                  6
% 3.41/1.01  lits                                    41
% 3.41/1.01  lits eq                                 15
% 3.41/1.01  fd_pure                                 0
% 3.41/1.01  fd_pseudo                               0
% 3.41/1.01  fd_cond                                 1
% 3.41/1.01  fd_pseudo_cond                          2
% 3.41/1.01  AC symbols                              0
% 3.41/1.01  
% 3.41/1.01  ------ Schedule dynamic 5 is on 
% 3.41/1.01  
% 3.41/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.41/1.01  
% 3.41/1.01  
% 3.41/1.01  ------ 
% 3.41/1.01  Current options:
% 3.41/1.01  ------ 
% 3.41/1.01  
% 3.41/1.01  ------ Input Options
% 3.41/1.01  
% 3.41/1.01  --out_options                           all
% 3.41/1.01  --tptp_safe_out                         true
% 3.41/1.01  --problem_path                          ""
% 3.41/1.01  --include_path                          ""
% 3.41/1.01  --clausifier                            res/vclausify_rel
% 3.41/1.01  --clausifier_options                    --mode clausify
% 3.41/1.01  --stdin                                 false
% 3.41/1.01  --stats_out                             all
% 3.41/1.01  
% 3.41/1.01  ------ General Options
% 3.41/1.01  
% 3.41/1.01  --fof                                   false
% 3.41/1.01  --time_out_real                         305.
% 3.41/1.01  --time_out_virtual                      -1.
% 3.41/1.01  --symbol_type_check                     false
% 3.41/1.01  --clausify_out                          false
% 3.41/1.01  --sig_cnt_out                           false
% 3.41/1.01  --trig_cnt_out                          false
% 3.41/1.01  --trig_cnt_out_tolerance                1.
% 3.41/1.01  --trig_cnt_out_sk_spl                   false
% 3.41/1.01  --abstr_cl_out                          false
% 3.41/1.01  
% 3.41/1.01  ------ Global Options
% 3.41/1.01  
% 3.41/1.01  --schedule                              default
% 3.41/1.01  --add_important_lit                     false
% 3.41/1.01  --prop_solver_per_cl                    1000
% 3.41/1.01  --min_unsat_core                        false
% 3.41/1.01  --soft_assumptions                      false
% 3.41/1.01  --soft_lemma_size                       3
% 3.41/1.01  --prop_impl_unit_size                   0
% 3.41/1.01  --prop_impl_unit                        []
% 3.41/1.01  --share_sel_clauses                     true
% 3.41/1.01  --reset_solvers                         false
% 3.41/1.01  --bc_imp_inh                            [conj_cone]
% 3.41/1.01  --conj_cone_tolerance                   3.
% 3.41/1.01  --extra_neg_conj                        none
% 3.41/1.01  --large_theory_mode                     true
% 3.41/1.01  --prolific_symb_bound                   200
% 3.41/1.01  --lt_threshold                          2000
% 3.41/1.01  --clause_weak_htbl                      true
% 3.41/1.01  --gc_record_bc_elim                     false
% 3.41/1.01  
% 3.41/1.01  ------ Preprocessing Options
% 3.41/1.01  
% 3.41/1.01  --preprocessing_flag                    true
% 3.41/1.01  --time_out_prep_mult                    0.1
% 3.41/1.01  --splitting_mode                        input
% 3.41/1.01  --splitting_grd                         true
% 3.41/1.01  --splitting_cvd                         false
% 3.41/1.01  --splitting_cvd_svl                     false
% 3.41/1.01  --splitting_nvd                         32
% 3.41/1.01  --sub_typing                            true
% 3.41/1.01  --prep_gs_sim                           true
% 3.41/1.01  --prep_unflatten                        true
% 3.41/1.01  --prep_res_sim                          true
% 3.41/1.01  --prep_upred                            true
% 3.41/1.01  --prep_sem_filter                       exhaustive
% 3.41/1.01  --prep_sem_filter_out                   false
% 3.41/1.01  --pred_elim                             true
% 3.41/1.01  --res_sim_input                         true
% 3.41/1.01  --eq_ax_congr_red                       true
% 3.41/1.01  --pure_diseq_elim                       true
% 3.41/1.01  --brand_transform                       false
% 3.41/1.01  --non_eq_to_eq                          false
% 3.41/1.01  --prep_def_merge                        true
% 3.41/1.01  --prep_def_merge_prop_impl              false
% 3.41/1.01  --prep_def_merge_mbd                    true
% 3.41/1.01  --prep_def_merge_tr_red                 false
% 3.41/1.01  --prep_def_merge_tr_cl                  false
% 3.41/1.01  --smt_preprocessing                     true
% 3.41/1.01  --smt_ac_axioms                         fast
% 3.41/1.01  --preprocessed_out                      false
% 3.41/1.01  --preprocessed_stats                    false
% 3.41/1.01  
% 3.41/1.01  ------ Abstraction refinement Options
% 3.41/1.01  
% 3.41/1.01  --abstr_ref                             []
% 3.41/1.01  --abstr_ref_prep                        false
% 3.41/1.01  --abstr_ref_until_sat                   false
% 3.41/1.01  --abstr_ref_sig_restrict                funpre
% 3.41/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/1.01  --abstr_ref_under                       []
% 3.41/1.01  
% 3.41/1.01  ------ SAT Options
% 3.41/1.01  
% 3.41/1.01  --sat_mode                              false
% 3.41/1.01  --sat_fm_restart_options                ""
% 3.41/1.01  --sat_gr_def                            false
% 3.41/1.01  --sat_epr_types                         true
% 3.41/1.01  --sat_non_cyclic_types                  false
% 3.41/1.01  --sat_finite_models                     false
% 3.41/1.01  --sat_fm_lemmas                         false
% 3.41/1.01  --sat_fm_prep                           false
% 3.41/1.01  --sat_fm_uc_incr                        true
% 3.41/1.01  --sat_out_model                         small
% 3.41/1.01  --sat_out_clauses                       false
% 3.41/1.01  
% 3.41/1.01  ------ QBF Options
% 3.41/1.01  
% 3.41/1.01  --qbf_mode                              false
% 3.41/1.01  --qbf_elim_univ                         false
% 3.41/1.01  --qbf_dom_inst                          none
% 3.41/1.01  --qbf_dom_pre_inst                      false
% 3.41/1.01  --qbf_sk_in                             false
% 3.41/1.01  --qbf_pred_elim                         true
% 3.41/1.01  --qbf_split                             512
% 3.41/1.01  
% 3.41/1.01  ------ BMC1 Options
% 3.41/1.01  
% 3.41/1.01  --bmc1_incremental                      false
% 3.41/1.01  --bmc1_axioms                           reachable_all
% 3.41/1.01  --bmc1_min_bound                        0
% 3.41/1.01  --bmc1_max_bound                        -1
% 3.41/1.01  --bmc1_max_bound_default                -1
% 3.41/1.01  --bmc1_symbol_reachability              true
% 3.41/1.01  --bmc1_property_lemmas                  false
% 3.41/1.01  --bmc1_k_induction                      false
% 3.41/1.01  --bmc1_non_equiv_states                 false
% 3.41/1.01  --bmc1_deadlock                         false
% 3.41/1.01  --bmc1_ucm                              false
% 3.41/1.01  --bmc1_add_unsat_core                   none
% 3.41/1.01  --bmc1_unsat_core_children              false
% 3.41/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/1.01  --bmc1_out_stat                         full
% 3.41/1.01  --bmc1_ground_init                      false
% 3.41/1.01  --bmc1_pre_inst_next_state              false
% 3.41/1.01  --bmc1_pre_inst_state                   false
% 3.41/1.01  --bmc1_pre_inst_reach_state             false
% 3.41/1.01  --bmc1_out_unsat_core                   false
% 3.41/1.01  --bmc1_aig_witness_out                  false
% 3.41/1.01  --bmc1_verbose                          false
% 3.41/1.01  --bmc1_dump_clauses_tptp                false
% 3.41/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.41/1.01  --bmc1_dump_file                        -
% 3.41/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.41/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.41/1.01  --bmc1_ucm_extend_mode                  1
% 3.41/1.01  --bmc1_ucm_init_mode                    2
% 3.41/1.01  --bmc1_ucm_cone_mode                    none
% 3.41/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.41/1.01  --bmc1_ucm_relax_model                  4
% 3.41/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.41/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/1.01  --bmc1_ucm_layered_model                none
% 3.41/1.01  --bmc1_ucm_max_lemma_size               10
% 3.41/1.01  
% 3.41/1.01  ------ AIG Options
% 3.41/1.01  
% 3.41/1.01  --aig_mode                              false
% 3.41/1.01  
% 3.41/1.01  ------ Instantiation Options
% 3.41/1.01  
% 3.41/1.01  --instantiation_flag                    true
% 3.41/1.01  --inst_sos_flag                         false
% 3.41/1.01  --inst_sos_phase                        true
% 3.41/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/1.01  --inst_lit_sel_side                     none
% 3.41/1.01  --inst_solver_per_active                1400
% 3.41/1.01  --inst_solver_calls_frac                1.
% 3.41/1.01  --inst_passive_queue_type               priority_queues
% 3.41/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/1.01  --inst_passive_queues_freq              [25;2]
% 3.41/1.01  --inst_dismatching                      true
% 3.41/1.01  --inst_eager_unprocessed_to_passive     true
% 3.41/1.01  --inst_prop_sim_given                   true
% 3.41/1.01  --inst_prop_sim_new                     false
% 3.41/1.01  --inst_subs_new                         false
% 3.41/1.01  --inst_eq_res_simp                      false
% 3.41/1.01  --inst_subs_given                       false
% 3.41/1.01  --inst_orphan_elimination               true
% 3.41/1.01  --inst_learning_loop_flag               true
% 3.41/1.01  --inst_learning_start                   3000
% 3.41/1.01  --inst_learning_factor                  2
% 3.41/1.01  --inst_start_prop_sim_after_learn       3
% 3.41/1.01  --inst_sel_renew                        solver
% 3.41/1.01  --inst_lit_activity_flag                true
% 3.41/1.01  --inst_restr_to_given                   false
% 3.41/1.01  --inst_activity_threshold               500
% 3.41/1.01  --inst_out_proof                        true
% 3.41/1.01  
% 3.41/1.01  ------ Resolution Options
% 3.41/1.01  
% 3.41/1.01  --resolution_flag                       false
% 3.41/1.01  --res_lit_sel                           adaptive
% 3.41/1.01  --res_lit_sel_side                      none
% 3.41/1.01  --res_ordering                          kbo
% 3.41/1.01  --res_to_prop_solver                    active
% 3.41/1.01  --res_prop_simpl_new                    false
% 3.41/1.01  --res_prop_simpl_given                  true
% 3.41/1.01  --res_passive_queue_type                priority_queues
% 3.41/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/1.01  --res_passive_queues_freq               [15;5]
% 3.41/1.01  --res_forward_subs                      full
% 3.41/1.01  --res_backward_subs                     full
% 3.41/1.01  --res_forward_subs_resolution           true
% 3.41/1.01  --res_backward_subs_resolution          true
% 3.41/1.01  --res_orphan_elimination                true
% 3.41/1.01  --res_time_limit                        2.
% 3.41/1.01  --res_out_proof                         true
% 3.41/1.01  
% 3.41/1.01  ------ Superposition Options
% 3.41/1.01  
% 3.41/1.01  --superposition_flag                    true
% 3.41/1.01  --sup_passive_queue_type                priority_queues
% 3.41/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.41/1.01  --demod_completeness_check              fast
% 3.41/1.01  --demod_use_ground                      true
% 3.41/1.01  --sup_to_prop_solver                    passive
% 3.41/1.01  --sup_prop_simpl_new                    true
% 3.41/1.01  --sup_prop_simpl_given                  true
% 3.41/1.01  --sup_fun_splitting                     false
% 3.41/1.01  --sup_smt_interval                      50000
% 3.41/1.01  
% 3.41/1.01  ------ Superposition Simplification Setup
% 3.41/1.01  
% 3.41/1.01  --sup_indices_passive                   []
% 3.41/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.41/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/1.01  --sup_full_bw                           [BwDemod]
% 3.41/1.01  --sup_immed_triv                        [TrivRules]
% 3.41/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/1.01  --sup_immed_bw_main                     []
% 3.41/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.41/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.41/1.01  
% 3.41/1.01  ------ Combination Options
% 3.41/1.01  
% 3.41/1.01  --comb_res_mult                         3
% 3.41/1.01  --comb_sup_mult                         2
% 3.41/1.01  --comb_inst_mult                        10
% 3.41/1.01  
% 3.41/1.01  ------ Debug Options
% 3.41/1.01  
% 3.41/1.01  --dbg_backtrace                         false
% 3.41/1.01  --dbg_dump_prop_clauses                 false
% 3.41/1.01  --dbg_dump_prop_clauses_file            -
% 3.41/1.01  --dbg_out_stat                          false
% 3.41/1.01  
% 3.41/1.01  
% 3.41/1.01  
% 3.41/1.01  
% 3.41/1.01  ------ Proving...
% 3.41/1.01  
% 3.41/1.01  
% 3.41/1.01  % SZS status Theorem for theBenchmark.p
% 3.41/1.01  
% 3.41/1.01   Resolution empty clause
% 3.41/1.01  
% 3.41/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.41/1.01  
% 3.41/1.01  fof(f17,conjecture,(
% 3.41/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f18,negated_conjecture,(
% 3.41/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.41/1.01    inference(negated_conjecture,[],[f17])).
% 3.41/1.01  
% 3.41/1.01  fof(f19,plain,(
% 3.41/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.41/1.01    inference(pure_predicate_removal,[],[f18])).
% 3.41/1.01  
% 3.41/1.01  fof(f31,plain,(
% 3.41/1.01    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 3.41/1.01    inference(ennf_transformation,[],[f19])).
% 3.41/1.01  
% 3.41/1.01  fof(f32,plain,(
% 3.41/1.01    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 3.41/1.01    inference(flattening,[],[f31])).
% 3.41/1.01  
% 3.41/1.01  fof(f41,plain,(
% 3.41/1.01    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 3.41/1.01    introduced(choice_axiom,[])).
% 3.41/1.01  
% 3.41/1.01  fof(f42,plain,(
% 3.41/1.01    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 3.41/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f41])).
% 3.41/1.01  
% 3.41/1.01  fof(f70,plain,(
% 3.41/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.41/1.01    inference(cnf_transformation,[],[f42])).
% 3.41/1.01  
% 3.41/1.01  fof(f3,axiom,(
% 3.41/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f47,plain,(
% 3.41/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.41/1.01    inference(cnf_transformation,[],[f3])).
% 3.41/1.01  
% 3.41/1.01  fof(f4,axiom,(
% 3.41/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f48,plain,(
% 3.41/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.41/1.01    inference(cnf_transformation,[],[f4])).
% 3.41/1.01  
% 3.41/1.01  fof(f5,axiom,(
% 3.41/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f49,plain,(
% 3.41/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.41/1.01    inference(cnf_transformation,[],[f5])).
% 3.41/1.01  
% 3.41/1.01  fof(f73,plain,(
% 3.41/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.41/1.01    inference(definition_unfolding,[],[f48,f49])).
% 3.41/1.01  
% 3.41/1.01  fof(f74,plain,(
% 3.41/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.41/1.01    inference(definition_unfolding,[],[f47,f73])).
% 3.41/1.01  
% 3.41/1.01  fof(f82,plain,(
% 3.41/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 3.41/1.01    inference(definition_unfolding,[],[f70,f74])).
% 3.41/1.01  
% 3.41/1.01  fof(f14,axiom,(
% 3.41/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f20,plain,(
% 3.41/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.41/1.01    inference(pure_predicate_removal,[],[f14])).
% 3.41/1.01  
% 3.41/1.01  fof(f27,plain,(
% 3.41/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/1.01    inference(ennf_transformation,[],[f20])).
% 3.41/1.01  
% 3.41/1.01  fof(f66,plain,(
% 3.41/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.41/1.01    inference(cnf_transformation,[],[f27])).
% 3.41/1.01  
% 3.41/1.01  fof(f9,axiom,(
% 3.41/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f22,plain,(
% 3.41/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.41/1.01    inference(ennf_transformation,[],[f9])).
% 3.41/1.01  
% 3.41/1.01  fof(f40,plain,(
% 3.41/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.41/1.01    inference(nnf_transformation,[],[f22])).
% 3.41/1.01  
% 3.41/1.01  fof(f60,plain,(
% 3.41/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.41/1.01    inference(cnf_transformation,[],[f40])).
% 3.41/1.01  
% 3.41/1.01  fof(f13,axiom,(
% 3.41/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f26,plain,(
% 3.41/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/1.01    inference(ennf_transformation,[],[f13])).
% 3.41/1.01  
% 3.41/1.01  fof(f65,plain,(
% 3.41/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.41/1.01    inference(cnf_transformation,[],[f26])).
% 3.41/1.01  
% 3.41/1.01  fof(f6,axiom,(
% 3.41/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f21,plain,(
% 3.41/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.41/1.01    inference(ennf_transformation,[],[f6])).
% 3.41/1.01  
% 3.41/1.01  fof(f35,plain,(
% 3.41/1.01    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.41/1.01    inference(nnf_transformation,[],[f21])).
% 3.41/1.01  
% 3.41/1.01  fof(f36,plain,(
% 3.41/1.01    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 3.41/1.01    inference(flattening,[],[f35])).
% 3.41/1.01  
% 3.41/1.01  fof(f50,plain,(
% 3.41/1.01    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 3.41/1.01    inference(cnf_transformation,[],[f36])).
% 3.41/1.01  
% 3.41/1.01  fof(f79,plain,(
% 3.41/1.01    ( ! [X2,X0,X1] : (k2_enumset1(X1,X1,X1,X2) = X0 | k2_enumset1(X2,X2,X2,X2) = X0 | k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 3.41/1.01    inference(definition_unfolding,[],[f50,f73,f74,f74,f73])).
% 3.41/1.01  
% 3.41/1.01  fof(f72,plain,(
% 3.41/1.01    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 3.41/1.01    inference(cnf_transformation,[],[f42])).
% 3.41/1.01  
% 3.41/1.01  fof(f81,plain,(
% 3.41/1.01    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 3.41/1.01    inference(definition_unfolding,[],[f72,f74,f74])).
% 3.41/1.01  
% 3.41/1.01  fof(f15,axiom,(
% 3.41/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f28,plain,(
% 3.41/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/1.01    inference(ennf_transformation,[],[f15])).
% 3.41/1.01  
% 3.41/1.01  fof(f67,plain,(
% 3.41/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.41/1.01    inference(cnf_transformation,[],[f28])).
% 3.41/1.01  
% 3.41/1.01  fof(f10,axiom,(
% 3.41/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f23,plain,(
% 3.41/1.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.41/1.01    inference(ennf_transformation,[],[f10])).
% 3.41/1.01  
% 3.41/1.01  fof(f62,plain,(
% 3.41/1.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.41/1.01    inference(cnf_transformation,[],[f23])).
% 3.41/1.01  
% 3.41/1.01  fof(f12,axiom,(
% 3.41/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f24,plain,(
% 3.41/1.01    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.41/1.01    inference(ennf_transformation,[],[f12])).
% 3.41/1.01  
% 3.41/1.01  fof(f25,plain,(
% 3.41/1.01    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.41/1.01    inference(flattening,[],[f24])).
% 3.41/1.01  
% 3.41/1.01  fof(f64,plain,(
% 3.41/1.01    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.41/1.01    inference(cnf_transformation,[],[f25])).
% 3.41/1.01  
% 3.41/1.01  fof(f80,plain,(
% 3.41/1.01    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.41/1.01    inference(definition_unfolding,[],[f64,f74,f74])).
% 3.41/1.01  
% 3.41/1.01  fof(f69,plain,(
% 3.41/1.01    v1_funct_1(sK3)),
% 3.41/1.01    inference(cnf_transformation,[],[f42])).
% 3.41/1.01  
% 3.41/1.01  fof(f7,axiom,(
% 3.41/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f37,plain,(
% 3.41/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.41/1.01    inference(nnf_transformation,[],[f7])).
% 3.41/1.01  
% 3.41/1.01  fof(f38,plain,(
% 3.41/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.41/1.01    inference(flattening,[],[f37])).
% 3.41/1.01  
% 3.41/1.01  fof(f56,plain,(
% 3.41/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.41/1.01    inference(cnf_transformation,[],[f38])).
% 3.41/1.01  
% 3.41/1.01  fof(f90,plain,(
% 3.41/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.41/1.01    inference(equality_resolution,[],[f56])).
% 3.41/1.01  
% 3.41/1.01  fof(f16,axiom,(
% 3.41/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f29,plain,(
% 3.41/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.41/1.01    inference(ennf_transformation,[],[f16])).
% 3.41/1.01  
% 3.41/1.01  fof(f30,plain,(
% 3.41/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 3.41/1.01    inference(flattening,[],[f29])).
% 3.41/1.01  
% 3.41/1.01  fof(f68,plain,(
% 3.41/1.01    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 3.41/1.01    inference(cnf_transformation,[],[f30])).
% 3.41/1.01  
% 3.41/1.01  fof(f8,axiom,(
% 3.41/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f39,plain,(
% 3.41/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.41/1.01    inference(nnf_transformation,[],[f8])).
% 3.41/1.01  
% 3.41/1.01  fof(f58,plain,(
% 3.41/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.41/1.01    inference(cnf_transformation,[],[f39])).
% 3.41/1.01  
% 3.41/1.01  fof(f55,plain,(
% 3.41/1.01    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.41/1.01    inference(cnf_transformation,[],[f38])).
% 3.41/1.01  
% 3.41/1.01  fof(f2,axiom,(
% 3.41/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f46,plain,(
% 3.41/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.41/1.01    inference(cnf_transformation,[],[f2])).
% 3.41/1.01  
% 3.41/1.01  fof(f1,axiom,(
% 3.41/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f33,plain,(
% 3.41/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.41/1.01    inference(nnf_transformation,[],[f1])).
% 3.41/1.01  
% 3.41/1.01  fof(f34,plain,(
% 3.41/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.41/1.01    inference(flattening,[],[f33])).
% 3.41/1.01  
% 3.41/1.01  fof(f45,plain,(
% 3.41/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.41/1.01    inference(cnf_transformation,[],[f34])).
% 3.41/1.01  
% 3.41/1.01  fof(f11,axiom,(
% 3.41/1.01    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 3.41/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.41/1.01  
% 3.41/1.01  fof(f63,plain,(
% 3.41/1.01    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 3.41/1.01    inference(cnf_transformation,[],[f11])).
% 3.41/1.01  
% 3.41/1.01  cnf(c_25,negated_conjecture,
% 3.41/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 3.41/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1023,plain,
% 3.41/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_20,plain,
% 3.41/1.01      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.41/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_15,plain,
% 3.41/1.01      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.41/1.01      inference(cnf_transformation,[],[f60]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_313,plain,
% 3.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.41/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 3.41/1.01      | ~ v1_relat_1(X0) ),
% 3.41/1.01      inference(resolution,[status(thm)],[c_20,c_15]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_19,plain,
% 3.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.41/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_317,plain,
% 3.41/1.01      ( r1_tarski(k1_relat_1(X0),X1)
% 3.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.41/1.01      inference(global_propositional_subsumption,[status(thm)],[c_313,c_19]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_318,plain,
% 3.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.41/1.01      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.41/1.01      inference(renaming,[status(thm)],[c_317]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1021,plain,
% 3.41/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.41/1.01      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_318]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1344,plain,
% 3.41/1.01      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.41/1.01      inference(superposition,[status(thm)],[c_1023,c_1021]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_8,plain,
% 3.41/1.01      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))
% 3.41/1.01      | k2_enumset1(X1,X1,X1,X2) = X0
% 3.41/1.01      | k2_enumset1(X2,X2,X2,X2) = X0
% 3.41/1.01      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.41/1.01      | k1_xboole_0 = X0 ),
% 3.41/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1031,plain,
% 3.41/1.01      ( k2_enumset1(X0,X0,X0,X1) = X2
% 3.41/1.01      | k2_enumset1(X1,X1,X1,X1) = X2
% 3.41/1.01      | k2_enumset1(X0,X0,X0,X0) = X2
% 3.41/1.01      | k1_xboole_0 = X2
% 3.41/1.01      | r1_tarski(X2,k2_enumset1(X0,X0,X0,X1)) != iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2941,plain,
% 3.41/1.01      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.41/1.01      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.41/1.01      inference(superposition,[status(thm)],[c_1344,c_1031]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_3271,plain,
% 3.41/1.01      ( k1_relat_1(sK3) = k1_xboole_0
% 3.41/1.01      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 3.41/1.01      inference(superposition,[status(thm)],[c_2941,c_1023]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_23,negated_conjecture,
% 3.41/1.01      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.41/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1166,plain,
% 3.41/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.41/1.01      | v1_relat_1(sK3) ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_21,plain,
% 3.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.41/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.41/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1220,plain,
% 3.41/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.41/1.01      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1285,plain,
% 3.41/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.41/1.01      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_1220]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_565,plain,
% 3.41/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.41/1.01      theory(equality) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1206,plain,
% 3.41/1.01      ( ~ r1_tarski(X0,X1)
% 3.41/1.01      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.41/1.01      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 3.41/1.01      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_565]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1284,plain,
% 3.41/1.01      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.41/1.01      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 3.41/1.01      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.41/1.01      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_1206]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1429,plain,
% 3.41/1.01      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.41/1.01      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 3.41/1.01      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.41/1.01      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_1284]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_16,plain,
% 3.41/1.01      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.41/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1232,plain,
% 3.41/1.01      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1430,plain,
% 3.41/1.01      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_1232]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_18,plain,
% 3.41/1.01      ( ~ v1_funct_1(X0)
% 3.41/1.01      | ~ v1_relat_1(X0)
% 3.41/1.01      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.41/1.01      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.41/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_26,negated_conjecture,
% 3.41/1.01      ( v1_funct_1(sK3) ),
% 3.41/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_294,plain,
% 3.41/1.01      ( ~ v1_relat_1(X0)
% 3.41/1.01      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.41/1.01      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.41/1.01      | sK3 != X0 ),
% 3.41/1.01      inference(resolution_lifted,[status(thm)],[c_18,c_26]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_295,plain,
% 3.41/1.01      ( ~ v1_relat_1(sK3)
% 3.41/1.01      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.41/1.01      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.41/1.01      inference(unflattening,[status(thm)],[c_294]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1022,plain,
% 3.41/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.41/1.01      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.41/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_28,plain,
% 3.41/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_296,plain,
% 3.41/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.41/1.01      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.41/1.01      | v1_relat_1(sK3) != iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_295]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1167,plain,
% 3.41/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 3.41/1.01      | v1_relat_1(sK3) = iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_1166]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1176,plain,
% 3.41/1.01      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.41/1.01      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 3.41/1.01      inference(global_propositional_subsumption,
% 3.41/1.01                [status(thm)],
% 3.41/1.01                [c_1022,c_28,c_296,c_1167]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1177,plain,
% 3.41/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.41/1.01      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.41/1.01      inference(renaming,[status(thm)],[c_1176]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_3264,plain,
% 3.41/1.01      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.41/1.01      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.41/1.01      inference(superposition,[status(thm)],[c_2941,c_1177]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_3324,plain,
% 3.41/1.01      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.41/1.01      inference(global_propositional_subsumption,
% 3.41/1.01                [status(thm)],
% 3.41/1.01                [c_3271,c_25,c_23,c_1166,c_1285,c_1429,c_1430,c_3264]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_10,plain,
% 3.41/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.41/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_22,plain,
% 3.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.41/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 3.41/1.01      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 3.41/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1025,plain,
% 3.41/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.41/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2))) = iProver_top
% 3.41/1.01      | r1_tarski(k1_relat_1(X0),X3) != iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1853,plain,
% 3.41/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) = iProver_top
% 3.41/1.01      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.41/1.01      inference(superposition,[status(thm)],[c_1023,c_1025]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_13,plain,
% 3.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.41/1.01      inference(cnf_transformation,[],[f58]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1029,plain,
% 3.41/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.41/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2344,plain,
% 3.41/1.01      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.41/1.01      | r1_tarski(sK3,k2_zfmisc_1(X0,sK1)) = iProver_top ),
% 3.41/1.01      inference(superposition,[status(thm)],[c_1853,c_1029]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2489,plain,
% 3.41/1.01      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.41/1.01      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.41/1.01      inference(superposition,[status(thm)],[c_10,c_2344]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_3328,plain,
% 3.41/1.01      ( r1_tarski(sK3,k1_xboole_0) = iProver_top
% 3.41/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.41/1.01      inference(demodulation,[status(thm)],[c_3324,c_2489]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_11,plain,
% 3.41/1.01      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.41/1.01      | k1_xboole_0 = X0
% 3.41/1.01      | k1_xboole_0 = X1 ),
% 3.41/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_59,plain,
% 3.41/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.41/1.01      | k1_xboole_0 = k1_xboole_0 ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_60,plain,
% 3.41/1.01      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_3,plain,
% 3.41/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 3.41/1.01      inference(cnf_transformation,[],[f46]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_72,plain,
% 3.41/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_74,plain,
% 3.41/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_72]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1201,plain,
% 3.41/1.01      ( ~ r1_tarski(X0,X1)
% 3.41/1.01      | r1_tarski(k1_relat_1(X2),X3)
% 3.41/1.01      | X3 != X1
% 3.41/1.01      | k1_relat_1(X2) != X0 ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_565]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2549,plain,
% 3.41/1.01      ( ~ r1_tarski(X0,X1)
% 3.41/1.01      | r1_tarski(k1_relat_1(sK3),X2)
% 3.41/1.01      | X2 != X1
% 3.41/1.01      | k1_relat_1(sK3) != X0 ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_1201]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2550,plain,
% 3.41/1.01      ( X0 != X1
% 3.41/1.01      | k1_relat_1(sK3) != X2
% 3.41/1.01      | r1_tarski(X2,X1) != iProver_top
% 3.41/1.01      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_2549]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2552,plain,
% 3.41/1.01      ( k1_relat_1(sK3) != k1_xboole_0
% 3.41/1.01      | k1_xboole_0 != k1_xboole_0
% 3.41/1.01      | r1_tarski(k1_relat_1(sK3),k1_xboole_0) = iProver_top
% 3.41/1.01      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_2550]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_3452,plain,
% 3.41/1.01      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.41/1.01      inference(global_propositional_subsumption,
% 3.41/1.01                [status(thm)],
% 3.41/1.01                [c_3328,c_25,c_23,c_59,c_60,c_74,c_1166,c_1285,c_1429,c_1430,
% 3.41/1.01                 c_2489,c_2552,c_3264]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_0,plain,
% 3.41/1.01      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.41/1.01      inference(cnf_transformation,[],[f45]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1038,plain,
% 3.41/1.01      ( X0 = X1
% 3.41/1.01      | r1_tarski(X0,X1) != iProver_top
% 3.41/1.01      | r1_tarski(X1,X0) != iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_3457,plain,
% 3.41/1.01      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.41/1.01      inference(superposition,[status(thm)],[c_3452,c_1038]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_73,plain,
% 3.41/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2074,plain,
% 3.41/1.01      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2076,plain,
% 3.41/1.01      ( ~ r1_tarski(sK3,k1_xboole_0)
% 3.41/1.01      | ~ r1_tarski(k1_xboole_0,sK3)
% 3.41/1.01      | sK3 = k1_xboole_0 ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_2074]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2501,plain,
% 3.41/1.01      ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0) | r1_tarski(sK3,k1_xboole_0) ),
% 3.41/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_2489]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2551,plain,
% 3.41/1.01      ( r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 3.41/1.01      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.41/1.01      | k1_relat_1(sK3) != k1_xboole_0
% 3.41/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_2549]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_4595,plain,
% 3.41/1.01      ( r1_tarski(k1_xboole_0,sK3) ),
% 3.41/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_4807,plain,
% 3.41/1.01      ( sK3 = k1_xboole_0 ),
% 3.41/1.01      inference(global_propositional_subsumption,
% 3.41/1.01                [status(thm)],
% 3.41/1.01                [c_3457,c_25,c_23,c_59,c_60,c_73,c_1166,c_1285,c_1429,c_1430,
% 3.41/1.01                 c_2076,c_2501,c_2551,c_3264,c_4595]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1026,plain,
% 3.41/1.01      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.41/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2150,plain,
% 3.41/1.01      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.41/1.01      inference(superposition,[status(thm)],[c_1023,c_1026]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1024,plain,
% 3.41/1.01      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_2176,plain,
% 3.41/1.01      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.41/1.01      inference(demodulation,[status(thm)],[c_2150,c_1024]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_4820,plain,
% 3.41/1.01      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.41/1.01      inference(demodulation,[status(thm)],[c_4807,c_2176]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_17,plain,
% 3.41/1.01      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.41/1.01      inference(cnf_transformation,[],[f63]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_4834,plain,
% 3.41/1.01      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.41/1.01      inference(demodulation,[status(thm)],[c_4820,c_17]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_1036,plain,
% 3.41/1.01      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.41/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.41/1.01  
% 3.41/1.01  cnf(c_5469,plain,
% 3.41/1.01      ( $false ),
% 3.41/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4834,c_1036]) ).
% 3.41/1.01  
% 3.41/1.01  
% 3.41/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.41/1.01  
% 3.41/1.01  ------                               Statistics
% 3.41/1.01  
% 3.41/1.01  ------ General
% 3.41/1.01  
% 3.41/1.01  abstr_ref_over_cycles:                  0
% 3.41/1.01  abstr_ref_under_cycles:                 0
% 3.41/1.01  gc_basic_clause_elim:                   0
% 3.41/1.01  forced_gc_time:                         0
% 3.41/1.01  parsing_time:                           0.009
% 3.41/1.01  unif_index_cands_time:                  0.
% 3.41/1.01  unif_index_add_time:                    0.
% 3.41/1.01  orderings_time:                         0.
% 3.41/1.01  out_proof_time:                         0.015
% 3.41/1.01  total_time:                             0.215
% 3.41/1.01  num_of_symbols:                         49
% 3.41/1.01  num_of_terms:                           5054
% 3.41/1.01  
% 3.41/1.01  ------ Preprocessing
% 3.41/1.01  
% 3.41/1.01  num_of_splits:                          0
% 3.41/1.01  num_of_split_atoms:                     0
% 3.41/1.01  num_of_reused_defs:                     0
% 3.41/1.01  num_eq_ax_congr_red:                    8
% 3.41/1.01  num_of_sem_filtered_clauses:            1
% 3.41/1.01  num_of_subtypes:                        0
% 3.41/1.01  monotx_restored_types:                  0
% 3.41/1.01  sat_num_of_epr_types:                   0
% 3.41/1.01  sat_num_of_non_cyclic_types:            0
% 3.41/1.01  sat_guarded_non_collapsed_types:        0
% 3.41/1.01  num_pure_diseq_elim:                    0
% 3.41/1.01  simp_replaced_by:                       0
% 3.41/1.01  res_preprocessed:                       122
% 3.41/1.01  prep_upred:                             0
% 3.41/1.01  prep_unflattend:                        3
% 3.41/1.01  smt_new_axioms:                         0
% 3.41/1.01  pred_elim_cands:                        3
% 3.41/1.01  pred_elim:                              2
% 3.41/1.01  pred_elim_cl:                           3
% 3.41/1.01  pred_elim_cycles:                       4
% 3.41/1.01  merged_defs:                            8
% 3.41/1.01  merged_defs_ncl:                        0
% 3.41/1.01  bin_hyper_res:                          8
% 3.41/1.01  prep_cycles:                            4
% 3.41/1.01  pred_elim_time:                         0.003
% 3.41/1.01  splitting_time:                         0.
% 3.41/1.01  sem_filter_time:                        0.
% 3.41/1.01  monotx_time:                            0.
% 3.41/1.01  subtype_inf_time:                       0.
% 3.41/1.01  
% 3.41/1.01  ------ Problem properties
% 3.41/1.01  
% 3.41/1.01  clauses:                                23
% 3.41/1.01  conjectures:                            3
% 3.41/1.01  epr:                                    4
% 3.41/1.01  horn:                                   21
% 3.41/1.01  ground:                                 3
% 3.41/1.01  unary:                                  12
% 3.41/1.01  binary:                                 6
% 3.41/1.01  lits:                                   41
% 3.41/1.01  lits_eq:                                15
% 3.41/1.01  fd_pure:                                0
% 3.41/1.01  fd_pseudo:                              0
% 3.41/1.01  fd_cond:                                1
% 3.41/1.01  fd_pseudo_cond:                         2
% 3.41/1.01  ac_symbols:                             0
% 3.41/1.01  
% 3.41/1.01  ------ Propositional Solver
% 3.41/1.01  
% 3.41/1.01  prop_solver_calls:                      28
% 3.41/1.01  prop_fast_solver_calls:                 638
% 3.41/1.01  smt_solver_calls:                       0
% 3.41/1.01  smt_fast_solver_calls:                  0
% 3.41/1.01  prop_num_of_clauses:                    2191
% 3.41/1.01  prop_preprocess_simplified:             7092
% 3.41/1.01  prop_fo_subsumed:                       10
% 3.41/1.01  prop_solver_time:                       0.
% 3.41/1.01  smt_solver_time:                        0.
% 3.41/1.01  smt_fast_solver_time:                   0.
% 3.41/1.01  prop_fast_solver_time:                  0.
% 3.41/1.01  prop_unsat_core_time:                   0.
% 3.41/1.01  
% 3.41/1.01  ------ QBF
% 3.41/1.01  
% 3.41/1.01  qbf_q_res:                              0
% 3.41/1.01  qbf_num_tautologies:                    0
% 3.41/1.01  qbf_prep_cycles:                        0
% 3.41/1.01  
% 3.41/1.01  ------ BMC1
% 3.41/1.01  
% 3.41/1.01  bmc1_current_bound:                     -1
% 3.41/1.01  bmc1_last_solved_bound:                 -1
% 3.41/1.01  bmc1_unsat_core_size:                   -1
% 3.41/1.01  bmc1_unsat_core_parents_size:           -1
% 3.41/1.01  bmc1_merge_next_fun:                    0
% 3.41/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.41/1.01  
% 3.41/1.01  ------ Instantiation
% 3.41/1.01  
% 3.41/1.01  inst_num_of_clauses:                    694
% 3.41/1.01  inst_num_in_passive:                    386
% 3.41/1.01  inst_num_in_active:                     270
% 3.41/1.01  inst_num_in_unprocessed:                38
% 3.41/1.01  inst_num_of_loops:                      300
% 3.41/1.01  inst_num_of_learning_restarts:          0
% 3.41/1.01  inst_num_moves_active_passive:          28
% 3.41/1.01  inst_lit_activity:                      0
% 3.41/1.01  inst_lit_activity_moves:                0
% 3.41/1.01  inst_num_tautologies:                   0
% 3.41/1.01  inst_num_prop_implied:                  0
% 3.41/1.01  inst_num_existing_simplified:           0
% 3.41/1.01  inst_num_eq_res_simplified:             0
% 3.41/1.01  inst_num_child_elim:                    0
% 3.41/1.01  inst_num_of_dismatching_blockings:      152
% 3.41/1.01  inst_num_of_non_proper_insts:           637
% 3.41/1.01  inst_num_of_duplicates:                 0
% 3.41/1.01  inst_inst_num_from_inst_to_res:         0
% 3.41/1.01  inst_dismatching_checking_time:         0.
% 3.41/1.01  
% 3.41/1.01  ------ Resolution
% 3.41/1.01  
% 3.41/1.01  res_num_of_clauses:                     0
% 3.41/1.01  res_num_in_passive:                     0
% 3.41/1.01  res_num_in_active:                      0
% 3.41/1.01  res_num_of_loops:                       126
% 3.41/1.01  res_forward_subset_subsumed:            80
% 3.41/1.01  res_backward_subset_subsumed:           2
% 3.41/1.01  res_forward_subsumed:                   0
% 3.41/1.01  res_backward_subsumed:                  0
% 3.41/1.01  res_forward_subsumption_resolution:     0
% 3.41/1.01  res_backward_subsumption_resolution:    0
% 3.41/1.01  res_clause_to_clause_subsumption:       268
% 3.41/1.01  res_orphan_elimination:                 0
% 3.41/1.01  res_tautology_del:                      40
% 3.41/1.01  res_num_eq_res_simplified:              0
% 3.41/1.01  res_num_sel_changes:                    0
% 3.41/1.01  res_moves_from_active_to_pass:          0
% 3.41/1.01  
% 3.41/1.01  ------ Superposition
% 3.41/1.01  
% 3.41/1.01  sup_time_total:                         0.
% 3.41/1.01  sup_time_generating:                    0.
% 3.41/1.01  sup_time_sim_full:                      0.
% 3.41/1.01  sup_time_sim_immed:                     0.
% 3.41/1.01  
% 3.41/1.01  sup_num_of_clauses:                     65
% 3.41/1.01  sup_num_in_active:                      33
% 3.41/1.01  sup_num_in_passive:                     32
% 3.41/1.01  sup_num_of_loops:                       59
% 3.41/1.01  sup_fw_superposition:                   57
% 3.41/1.01  sup_bw_superposition:                   45
% 3.41/1.01  sup_immediate_simplified:               23
% 3.41/1.01  sup_given_eliminated:                   0
% 3.41/1.01  comparisons_done:                       0
% 3.41/1.01  comparisons_avoided:                    0
% 3.41/1.01  
% 3.41/1.01  ------ Simplifications
% 3.41/1.01  
% 3.41/1.01  
% 3.41/1.01  sim_fw_subset_subsumed:                 3
% 3.41/1.01  sim_bw_subset_subsumed:                 6
% 3.41/1.01  sim_fw_subsumed:                        14
% 3.41/1.01  sim_bw_subsumed:                        3
% 3.41/1.01  sim_fw_subsumption_res:                 1
% 3.41/1.01  sim_bw_subsumption_res:                 0
% 3.41/1.01  sim_tautology_del:                      3
% 3.41/1.01  sim_eq_tautology_del:                   7
% 3.41/1.01  sim_eq_res_simp:                        0
% 3.41/1.01  sim_fw_demodulated:                     4
% 3.41/1.01  sim_bw_demodulated:                     26
% 3.41/1.01  sim_light_normalised:                   3
% 3.41/1.01  sim_joinable_taut:                      0
% 3.41/1.01  sim_joinable_simp:                      0
% 3.41/1.01  sim_ac_normalised:                      0
% 3.41/1.01  sim_smt_subsumption:                    0
% 3.41/1.01  
%------------------------------------------------------------------------------
