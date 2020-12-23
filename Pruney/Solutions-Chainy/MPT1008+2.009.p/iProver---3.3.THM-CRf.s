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
% DateTime   : Thu Dec  3 12:05:06 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  195 (1518 expanded)
%              Number of clauses        :  111 ( 389 expanded)
%              Number of leaves         :   22 ( 358 expanded)
%              Depth                    :   25
%              Number of atoms          :  519 (3927 expanded)
%              Number of equality atoms :  256 (1826 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f53])).

fof(f84,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f88,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f62,f63])).

fof(f89,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f61,f88])).

fof(f95,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f84,f89])).

fof(f83,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f85,f89])).

fof(f86,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f77,f89])).

fof(f87,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(definition_unfolding,[],[f87,f89,f89])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f68,f89])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f48])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f66])).

fof(f7,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f78,f89,f89])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1194,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_287,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_28])).

cnf(c_288,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_287])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_26,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_288,c_29,c_27,c_26])).

cnf(c_1189,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_308,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_309,plain,
    ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_1388,plain,
    ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_309])).

cnf(c_1435,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1189,c_1388])).

cnf(c_2019,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1),X0)),k2_relat_1(sK3)) = iProver_top
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1435])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1193,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2984,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1),X0)),X1) = iProver_top
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2019,c_1193])).

cnf(c_14,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_329,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_330,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_538,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | k11_relat_1(X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_330])).

cnf(c_539,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | k11_relat_1(sK3,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_674,plain,
    ( r2_hidden(X0,k1_relat_1(sK3))
    | k11_relat_1(sK3,X0) = k1_xboole_0
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_539])).

cnf(c_1164,plain,
    ( k11_relat_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_675,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_539])).

cnf(c_719,plain,
    ( sP1_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_675])).

cnf(c_720,plain,
    ( k11_relat_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_691,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1391,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_673,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_539])).

cnf(c_1394,plain,
    ( ~ sP0_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_1396,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1394])).

cnf(c_1476,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
    | k11_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1164,c_719,c_720,c_1391,c_1396])).

cnf(c_1477,plain,
    ( k11_relat_1(sK3,X0) = k1_xboole_0
    | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1476])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_349,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_350,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_349])).

cnf(c_454,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_330,c_350])).

cnf(c_686,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | ~ sP6_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP6_iProver_split])],[c_454])).

cnf(c_1183,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP6_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_687,plain,
    ( sP6_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_454])).

cnf(c_750,plain,
    ( sP6_iProver_split = iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_751,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP6_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_2080,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1183,c_750,c_751,c_1391,c_1396])).

cnf(c_2081,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2080])).

cnf(c_2089,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
    | k11_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1477,c_2081])).

cnf(c_25,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1390,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1388,c_25])).

cnf(c_3153,plain,
    ( k11_relat_1(sK3,sK1) != k2_relat_1(sK3)
    | k11_relat_1(sK3,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2089,c_1390])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_514,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_330])).

cnf(c_515,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_678,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_515])).

cnf(c_1170,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_679,plain,
    ( sP3_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_515])).

cnf(c_1750,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1170,c_679,c_678,c_1391,c_1394])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_317,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_318,plain,
    ( v4_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_317])).

cnf(c_402,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_318])).

cnf(c_403,plain,
    ( ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_407,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_330])).

cnf(c_1407,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_407])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_505,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_330])).

cnf(c_506,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(k7_relat_1(sK3,X2)) = k9_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_680,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0)
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_506])).

cnf(c_1174,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0)
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_681,plain,
    ( sP4_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_506])).

cnf(c_1694,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1174,c_681,c_680,c_1391,c_1394])).

cnf(c_1698,plain,
    ( k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1407,c_1694])).

cnf(c_2918,plain,
    ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1750,c_1698])).

cnf(c_3156,plain,
    ( k11_relat_1(sK3,sK1) = k1_xboole_0
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_3153,c_2918])).

cnf(c_3157,plain,
    ( k11_relat_1(sK3,sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3156])).

cnf(c_3200,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3157,c_2918])).

cnf(c_4068,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1),X0)),X1) = iProver_top
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top
    | r1_tarski(k1_xboole_0,X1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2984,c_3200])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1190,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1959,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1190])).

cnf(c_2020,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1194,c_1959])).

cnf(c_4072,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1),X0)),X1) = iProver_top
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4068,c_2020])).

cnf(c_4079,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4072,c_1959])).

cnf(c_12,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_416,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_318])).

cnf(c_417,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_421,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_417,c_330])).

cnf(c_1188,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_2064,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1188])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1192,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2974,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2064,c_1192])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_364,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_365,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_443,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_330,c_365])).

cnf(c_689,plain,
    ( sP7_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_443])).

cnf(c_688,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | ~ sP7_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP7_iProver_split])],[c_443])).

cnf(c_757,plain,
    ( ~ sP7_iProver_split
    | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_1392,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_421])).

cnf(c_1398,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
    | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1392])).

cnf(c_1788,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0))
    | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1789,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_1791,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top
    | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1789])).

cnf(c_3528,plain,
    ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2974,c_689,c_757,c_1390,c_1391,c_1394,c_1398,c_1791])).

cnf(c_4207,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_4079,c_3528])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.01/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/0.99  
% 3.01/0.99  ------  iProver source info
% 3.01/0.99  
% 3.01/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.01/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/0.99  git: non_committed_changes: false
% 3.01/0.99  git: last_make_outside_of_git: false
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options
% 3.01/0.99  
% 3.01/0.99  --out_options                           all
% 3.01/0.99  --tptp_safe_out                         true
% 3.01/0.99  --problem_path                          ""
% 3.01/0.99  --include_path                          ""
% 3.01/0.99  --clausifier                            res/vclausify_rel
% 3.01/0.99  --clausifier_options                    --mode clausify
% 3.01/0.99  --stdin                                 false
% 3.01/0.99  --stats_out                             all
% 3.01/0.99  
% 3.01/0.99  ------ General Options
% 3.01/0.99  
% 3.01/0.99  --fof                                   false
% 3.01/0.99  --time_out_real                         305.
% 3.01/0.99  --time_out_virtual                      -1.
% 3.01/0.99  --symbol_type_check                     false
% 3.01/0.99  --clausify_out                          false
% 3.01/0.99  --sig_cnt_out                           false
% 3.01/0.99  --trig_cnt_out                          false
% 3.01/0.99  --trig_cnt_out_tolerance                1.
% 3.01/0.99  --trig_cnt_out_sk_spl                   false
% 3.01/0.99  --abstr_cl_out                          false
% 3.01/0.99  
% 3.01/0.99  ------ Global Options
% 3.01/0.99  
% 3.01/0.99  --schedule                              default
% 3.01/0.99  --add_important_lit                     false
% 3.01/0.99  --prop_solver_per_cl                    1000
% 3.01/0.99  --min_unsat_core                        false
% 3.01/0.99  --soft_assumptions                      false
% 3.01/0.99  --soft_lemma_size                       3
% 3.01/0.99  --prop_impl_unit_size                   0
% 3.01/0.99  --prop_impl_unit                        []
% 3.01/0.99  --share_sel_clauses                     true
% 3.01/0.99  --reset_solvers                         false
% 3.01/0.99  --bc_imp_inh                            [conj_cone]
% 3.01/0.99  --conj_cone_tolerance                   3.
% 3.01/0.99  --extra_neg_conj                        none
% 3.01/0.99  --large_theory_mode                     true
% 3.01/0.99  --prolific_symb_bound                   200
% 3.01/0.99  --lt_threshold                          2000
% 3.01/0.99  --clause_weak_htbl                      true
% 3.01/0.99  --gc_record_bc_elim                     false
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing Options
% 3.01/0.99  
% 3.01/0.99  --preprocessing_flag                    true
% 3.01/0.99  --time_out_prep_mult                    0.1
% 3.01/0.99  --splitting_mode                        input
% 3.01/0.99  --splitting_grd                         true
% 3.01/0.99  --splitting_cvd                         false
% 3.01/0.99  --splitting_cvd_svl                     false
% 3.01/0.99  --splitting_nvd                         32
% 3.01/0.99  --sub_typing                            true
% 3.01/0.99  --prep_gs_sim                           true
% 3.01/0.99  --prep_unflatten                        true
% 3.01/0.99  --prep_res_sim                          true
% 3.01/0.99  --prep_upred                            true
% 3.01/0.99  --prep_sem_filter                       exhaustive
% 3.01/0.99  --prep_sem_filter_out                   false
% 3.01/0.99  --pred_elim                             true
% 3.01/0.99  --res_sim_input                         true
% 3.01/0.99  --eq_ax_congr_red                       true
% 3.01/0.99  --pure_diseq_elim                       true
% 3.01/0.99  --brand_transform                       false
% 3.01/0.99  --non_eq_to_eq                          false
% 3.01/0.99  --prep_def_merge                        true
% 3.01/0.99  --prep_def_merge_prop_impl              false
% 3.01/0.99  --prep_def_merge_mbd                    true
% 3.01/0.99  --prep_def_merge_tr_red                 false
% 3.01/0.99  --prep_def_merge_tr_cl                  false
% 3.01/0.99  --smt_preprocessing                     true
% 3.01/0.99  --smt_ac_axioms                         fast
% 3.01/0.99  --preprocessed_out                      false
% 3.01/0.99  --preprocessed_stats                    false
% 3.01/0.99  
% 3.01/0.99  ------ Abstraction refinement Options
% 3.01/0.99  
% 3.01/0.99  --abstr_ref                             []
% 3.01/0.99  --abstr_ref_prep                        false
% 3.01/0.99  --abstr_ref_until_sat                   false
% 3.01/0.99  --abstr_ref_sig_restrict                funpre
% 3.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.99  --abstr_ref_under                       []
% 3.01/0.99  
% 3.01/0.99  ------ SAT Options
% 3.01/0.99  
% 3.01/0.99  --sat_mode                              false
% 3.01/0.99  --sat_fm_restart_options                ""
% 3.01/0.99  --sat_gr_def                            false
% 3.01/0.99  --sat_epr_types                         true
% 3.01/0.99  --sat_non_cyclic_types                  false
% 3.01/0.99  --sat_finite_models                     false
% 3.01/0.99  --sat_fm_lemmas                         false
% 3.01/0.99  --sat_fm_prep                           false
% 3.01/0.99  --sat_fm_uc_incr                        true
% 3.01/0.99  --sat_out_model                         small
% 3.01/0.99  --sat_out_clauses                       false
% 3.01/0.99  
% 3.01/0.99  ------ QBF Options
% 3.01/0.99  
% 3.01/0.99  --qbf_mode                              false
% 3.01/0.99  --qbf_elim_univ                         false
% 3.01/0.99  --qbf_dom_inst                          none
% 3.01/0.99  --qbf_dom_pre_inst                      false
% 3.01/0.99  --qbf_sk_in                             false
% 3.01/0.99  --qbf_pred_elim                         true
% 3.01/0.99  --qbf_split                             512
% 3.01/0.99  
% 3.01/0.99  ------ BMC1 Options
% 3.01/0.99  
% 3.01/0.99  --bmc1_incremental                      false
% 3.01/0.99  --bmc1_axioms                           reachable_all
% 3.01/0.99  --bmc1_min_bound                        0
% 3.01/0.99  --bmc1_max_bound                        -1
% 3.01/0.99  --bmc1_max_bound_default                -1
% 3.01/0.99  --bmc1_symbol_reachability              true
% 3.01/0.99  --bmc1_property_lemmas                  false
% 3.01/0.99  --bmc1_k_induction                      false
% 3.01/0.99  --bmc1_non_equiv_states                 false
% 3.01/0.99  --bmc1_deadlock                         false
% 3.01/0.99  --bmc1_ucm                              false
% 3.01/0.99  --bmc1_add_unsat_core                   none
% 3.01/0.99  --bmc1_unsat_core_children              false
% 3.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.99  --bmc1_out_stat                         full
% 3.01/0.99  --bmc1_ground_init                      false
% 3.01/0.99  --bmc1_pre_inst_next_state              false
% 3.01/0.99  --bmc1_pre_inst_state                   false
% 3.01/0.99  --bmc1_pre_inst_reach_state             false
% 3.01/0.99  --bmc1_out_unsat_core                   false
% 3.01/0.99  --bmc1_aig_witness_out                  false
% 3.01/0.99  --bmc1_verbose                          false
% 3.01/0.99  --bmc1_dump_clauses_tptp                false
% 3.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.99  --bmc1_dump_file                        -
% 3.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.99  --bmc1_ucm_extend_mode                  1
% 3.01/0.99  --bmc1_ucm_init_mode                    2
% 3.01/0.99  --bmc1_ucm_cone_mode                    none
% 3.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.99  --bmc1_ucm_relax_model                  4
% 3.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.99  --bmc1_ucm_layered_model                none
% 3.01/0.99  --bmc1_ucm_max_lemma_size               10
% 3.01/0.99  
% 3.01/0.99  ------ AIG Options
% 3.01/0.99  
% 3.01/0.99  --aig_mode                              false
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation Options
% 3.01/0.99  
% 3.01/0.99  --instantiation_flag                    true
% 3.01/0.99  --inst_sos_flag                         false
% 3.01/0.99  --inst_sos_phase                        true
% 3.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel_side                     num_symb
% 3.01/0.99  --inst_solver_per_active                1400
% 3.01/0.99  --inst_solver_calls_frac                1.
% 3.01/0.99  --inst_passive_queue_type               priority_queues
% 3.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.99  --inst_passive_queues_freq              [25;2]
% 3.01/0.99  --inst_dismatching                      true
% 3.01/0.99  --inst_eager_unprocessed_to_passive     true
% 3.01/0.99  --inst_prop_sim_given                   true
% 3.01/0.99  --inst_prop_sim_new                     false
% 3.01/0.99  --inst_subs_new                         false
% 3.01/0.99  --inst_eq_res_simp                      false
% 3.01/0.99  --inst_subs_given                       false
% 3.01/0.99  --inst_orphan_elimination               true
% 3.01/0.99  --inst_learning_loop_flag               true
% 3.01/0.99  --inst_learning_start                   3000
% 3.01/0.99  --inst_learning_factor                  2
% 3.01/0.99  --inst_start_prop_sim_after_learn       3
% 3.01/0.99  --inst_sel_renew                        solver
% 3.01/0.99  --inst_lit_activity_flag                true
% 3.01/0.99  --inst_restr_to_given                   false
% 3.01/0.99  --inst_activity_threshold               500
% 3.01/0.99  --inst_out_proof                        true
% 3.01/0.99  
% 3.01/0.99  ------ Resolution Options
% 3.01/0.99  
% 3.01/0.99  --resolution_flag                       true
% 3.01/0.99  --res_lit_sel                           adaptive
% 3.01/0.99  --res_lit_sel_side                      none
% 3.01/0.99  --res_ordering                          kbo
% 3.01/0.99  --res_to_prop_solver                    active
% 3.01/0.99  --res_prop_simpl_new                    false
% 3.01/0.99  --res_prop_simpl_given                  true
% 3.01/0.99  --res_passive_queue_type                priority_queues
% 3.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.99  --res_passive_queues_freq               [15;5]
% 3.01/0.99  --res_forward_subs                      full
% 3.01/0.99  --res_backward_subs                     full
% 3.01/0.99  --res_forward_subs_resolution           true
% 3.01/0.99  --res_backward_subs_resolution          true
% 3.01/0.99  --res_orphan_elimination                true
% 3.01/0.99  --res_time_limit                        2.
% 3.01/0.99  --res_out_proof                         true
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Options
% 3.01/0.99  
% 3.01/0.99  --superposition_flag                    true
% 3.01/0.99  --sup_passive_queue_type                priority_queues
% 3.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.99  --demod_completeness_check              fast
% 3.01/0.99  --demod_use_ground                      true
% 3.01/0.99  --sup_to_prop_solver                    passive
% 3.01/0.99  --sup_prop_simpl_new                    true
% 3.01/0.99  --sup_prop_simpl_given                  true
% 3.01/0.99  --sup_fun_splitting                     false
% 3.01/0.99  --sup_smt_interval                      50000
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Simplification Setup
% 3.01/0.99  
% 3.01/0.99  --sup_indices_passive                   []
% 3.01/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_full_bw                           [BwDemod]
% 3.01/0.99  --sup_immed_triv                        [TrivRules]
% 3.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_immed_bw_main                     []
% 3.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  
% 3.01/0.99  ------ Combination Options
% 3.01/0.99  
% 3.01/0.99  --comb_res_mult                         3
% 3.01/0.99  --comb_sup_mult                         2
% 3.01/0.99  --comb_inst_mult                        10
% 3.01/0.99  
% 3.01/0.99  ------ Debug Options
% 3.01/0.99  
% 3.01/0.99  --dbg_backtrace                         false
% 3.01/0.99  --dbg_dump_prop_clauses                 false
% 3.01/0.99  --dbg_dump_prop_clauses_file            -
% 3.01/0.99  --dbg_out_stat                          false
% 3.01/0.99  ------ Parsing...
% 3.01/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... gs_s  sp: 16 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/0.99  ------ Proving...
% 3.01/0.99  ------ Problem Properties 
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  clauses                                 40
% 3.01/0.99  conjectures                             2
% 3.01/0.99  EPR                                     11
% 3.01/0.99  Horn                                    28
% 3.01/0.99  unary                                   6
% 3.01/0.99  binary                                  24
% 3.01/0.99  lits                                    84
% 3.01/0.99  lits eq                                 34
% 3.01/0.99  fd_pure                                 0
% 3.01/0.99  fd_pseudo                               0
% 3.01/0.99  fd_cond                                 1
% 3.01/0.99  fd_pseudo_cond                          1
% 3.01/0.99  AC symbols                              0
% 3.01/0.99  
% 3.01/0.99  ------ Schedule dynamic 5 is on 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  ------ 
% 3.01/0.99  Current options:
% 3.01/0.99  ------ 
% 3.01/0.99  
% 3.01/0.99  ------ Input Options
% 3.01/0.99  
% 3.01/0.99  --out_options                           all
% 3.01/0.99  --tptp_safe_out                         true
% 3.01/0.99  --problem_path                          ""
% 3.01/0.99  --include_path                          ""
% 3.01/0.99  --clausifier                            res/vclausify_rel
% 3.01/0.99  --clausifier_options                    --mode clausify
% 3.01/0.99  --stdin                                 false
% 3.01/0.99  --stats_out                             all
% 3.01/0.99  
% 3.01/0.99  ------ General Options
% 3.01/0.99  
% 3.01/0.99  --fof                                   false
% 3.01/0.99  --time_out_real                         305.
% 3.01/0.99  --time_out_virtual                      -1.
% 3.01/0.99  --symbol_type_check                     false
% 3.01/0.99  --clausify_out                          false
% 3.01/0.99  --sig_cnt_out                           false
% 3.01/0.99  --trig_cnt_out                          false
% 3.01/0.99  --trig_cnt_out_tolerance                1.
% 3.01/0.99  --trig_cnt_out_sk_spl                   false
% 3.01/0.99  --abstr_cl_out                          false
% 3.01/0.99  
% 3.01/0.99  ------ Global Options
% 3.01/0.99  
% 3.01/0.99  --schedule                              default
% 3.01/0.99  --add_important_lit                     false
% 3.01/0.99  --prop_solver_per_cl                    1000
% 3.01/0.99  --min_unsat_core                        false
% 3.01/0.99  --soft_assumptions                      false
% 3.01/0.99  --soft_lemma_size                       3
% 3.01/0.99  --prop_impl_unit_size                   0
% 3.01/0.99  --prop_impl_unit                        []
% 3.01/0.99  --share_sel_clauses                     true
% 3.01/0.99  --reset_solvers                         false
% 3.01/0.99  --bc_imp_inh                            [conj_cone]
% 3.01/0.99  --conj_cone_tolerance                   3.
% 3.01/0.99  --extra_neg_conj                        none
% 3.01/0.99  --large_theory_mode                     true
% 3.01/0.99  --prolific_symb_bound                   200
% 3.01/0.99  --lt_threshold                          2000
% 3.01/0.99  --clause_weak_htbl                      true
% 3.01/0.99  --gc_record_bc_elim                     false
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing Options
% 3.01/0.99  
% 3.01/0.99  --preprocessing_flag                    true
% 3.01/0.99  --time_out_prep_mult                    0.1
% 3.01/0.99  --splitting_mode                        input
% 3.01/0.99  --splitting_grd                         true
% 3.01/0.99  --splitting_cvd                         false
% 3.01/0.99  --splitting_cvd_svl                     false
% 3.01/0.99  --splitting_nvd                         32
% 3.01/0.99  --sub_typing                            true
% 3.01/0.99  --prep_gs_sim                           true
% 3.01/0.99  --prep_unflatten                        true
% 3.01/0.99  --prep_res_sim                          true
% 3.01/0.99  --prep_upred                            true
% 3.01/0.99  --prep_sem_filter                       exhaustive
% 3.01/0.99  --prep_sem_filter_out                   false
% 3.01/0.99  --pred_elim                             true
% 3.01/0.99  --res_sim_input                         true
% 3.01/0.99  --eq_ax_congr_red                       true
% 3.01/0.99  --pure_diseq_elim                       true
% 3.01/0.99  --brand_transform                       false
% 3.01/0.99  --non_eq_to_eq                          false
% 3.01/0.99  --prep_def_merge                        true
% 3.01/0.99  --prep_def_merge_prop_impl              false
% 3.01/0.99  --prep_def_merge_mbd                    true
% 3.01/0.99  --prep_def_merge_tr_red                 false
% 3.01/0.99  --prep_def_merge_tr_cl                  false
% 3.01/0.99  --smt_preprocessing                     true
% 3.01/0.99  --smt_ac_axioms                         fast
% 3.01/0.99  --preprocessed_out                      false
% 3.01/0.99  --preprocessed_stats                    false
% 3.01/0.99  
% 3.01/0.99  ------ Abstraction refinement Options
% 3.01/0.99  
% 3.01/0.99  --abstr_ref                             []
% 3.01/0.99  --abstr_ref_prep                        false
% 3.01/0.99  --abstr_ref_until_sat                   false
% 3.01/0.99  --abstr_ref_sig_restrict                funpre
% 3.01/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/0.99  --abstr_ref_under                       []
% 3.01/0.99  
% 3.01/0.99  ------ SAT Options
% 3.01/0.99  
% 3.01/0.99  --sat_mode                              false
% 3.01/0.99  --sat_fm_restart_options                ""
% 3.01/0.99  --sat_gr_def                            false
% 3.01/0.99  --sat_epr_types                         true
% 3.01/0.99  --sat_non_cyclic_types                  false
% 3.01/0.99  --sat_finite_models                     false
% 3.01/0.99  --sat_fm_lemmas                         false
% 3.01/0.99  --sat_fm_prep                           false
% 3.01/0.99  --sat_fm_uc_incr                        true
% 3.01/0.99  --sat_out_model                         small
% 3.01/0.99  --sat_out_clauses                       false
% 3.01/0.99  
% 3.01/0.99  ------ QBF Options
% 3.01/0.99  
% 3.01/0.99  --qbf_mode                              false
% 3.01/0.99  --qbf_elim_univ                         false
% 3.01/0.99  --qbf_dom_inst                          none
% 3.01/0.99  --qbf_dom_pre_inst                      false
% 3.01/0.99  --qbf_sk_in                             false
% 3.01/0.99  --qbf_pred_elim                         true
% 3.01/0.99  --qbf_split                             512
% 3.01/0.99  
% 3.01/0.99  ------ BMC1 Options
% 3.01/0.99  
% 3.01/0.99  --bmc1_incremental                      false
% 3.01/0.99  --bmc1_axioms                           reachable_all
% 3.01/0.99  --bmc1_min_bound                        0
% 3.01/0.99  --bmc1_max_bound                        -1
% 3.01/0.99  --bmc1_max_bound_default                -1
% 3.01/0.99  --bmc1_symbol_reachability              true
% 3.01/0.99  --bmc1_property_lemmas                  false
% 3.01/0.99  --bmc1_k_induction                      false
% 3.01/0.99  --bmc1_non_equiv_states                 false
% 3.01/0.99  --bmc1_deadlock                         false
% 3.01/0.99  --bmc1_ucm                              false
% 3.01/0.99  --bmc1_add_unsat_core                   none
% 3.01/0.99  --bmc1_unsat_core_children              false
% 3.01/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/0.99  --bmc1_out_stat                         full
% 3.01/0.99  --bmc1_ground_init                      false
% 3.01/0.99  --bmc1_pre_inst_next_state              false
% 3.01/0.99  --bmc1_pre_inst_state                   false
% 3.01/0.99  --bmc1_pre_inst_reach_state             false
% 3.01/0.99  --bmc1_out_unsat_core                   false
% 3.01/0.99  --bmc1_aig_witness_out                  false
% 3.01/0.99  --bmc1_verbose                          false
% 3.01/0.99  --bmc1_dump_clauses_tptp                false
% 3.01/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.01/0.99  --bmc1_dump_file                        -
% 3.01/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.01/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.01/0.99  --bmc1_ucm_extend_mode                  1
% 3.01/0.99  --bmc1_ucm_init_mode                    2
% 3.01/0.99  --bmc1_ucm_cone_mode                    none
% 3.01/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.01/0.99  --bmc1_ucm_relax_model                  4
% 3.01/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.01/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/0.99  --bmc1_ucm_layered_model                none
% 3.01/0.99  --bmc1_ucm_max_lemma_size               10
% 3.01/0.99  
% 3.01/0.99  ------ AIG Options
% 3.01/0.99  
% 3.01/0.99  --aig_mode                              false
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation Options
% 3.01/0.99  
% 3.01/0.99  --instantiation_flag                    true
% 3.01/0.99  --inst_sos_flag                         false
% 3.01/0.99  --inst_sos_phase                        true
% 3.01/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/0.99  --inst_lit_sel_side                     none
% 3.01/0.99  --inst_solver_per_active                1400
% 3.01/0.99  --inst_solver_calls_frac                1.
% 3.01/0.99  --inst_passive_queue_type               priority_queues
% 3.01/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/0.99  --inst_passive_queues_freq              [25;2]
% 3.01/0.99  --inst_dismatching                      true
% 3.01/0.99  --inst_eager_unprocessed_to_passive     true
% 3.01/0.99  --inst_prop_sim_given                   true
% 3.01/0.99  --inst_prop_sim_new                     false
% 3.01/0.99  --inst_subs_new                         false
% 3.01/0.99  --inst_eq_res_simp                      false
% 3.01/0.99  --inst_subs_given                       false
% 3.01/0.99  --inst_orphan_elimination               true
% 3.01/0.99  --inst_learning_loop_flag               true
% 3.01/0.99  --inst_learning_start                   3000
% 3.01/0.99  --inst_learning_factor                  2
% 3.01/0.99  --inst_start_prop_sim_after_learn       3
% 3.01/0.99  --inst_sel_renew                        solver
% 3.01/0.99  --inst_lit_activity_flag                true
% 3.01/0.99  --inst_restr_to_given                   false
% 3.01/0.99  --inst_activity_threshold               500
% 3.01/0.99  --inst_out_proof                        true
% 3.01/0.99  
% 3.01/0.99  ------ Resolution Options
% 3.01/0.99  
% 3.01/0.99  --resolution_flag                       false
% 3.01/0.99  --res_lit_sel                           adaptive
% 3.01/0.99  --res_lit_sel_side                      none
% 3.01/0.99  --res_ordering                          kbo
% 3.01/0.99  --res_to_prop_solver                    active
% 3.01/0.99  --res_prop_simpl_new                    false
% 3.01/0.99  --res_prop_simpl_given                  true
% 3.01/0.99  --res_passive_queue_type                priority_queues
% 3.01/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/0.99  --res_passive_queues_freq               [15;5]
% 3.01/0.99  --res_forward_subs                      full
% 3.01/0.99  --res_backward_subs                     full
% 3.01/0.99  --res_forward_subs_resolution           true
% 3.01/0.99  --res_backward_subs_resolution          true
% 3.01/0.99  --res_orphan_elimination                true
% 3.01/0.99  --res_time_limit                        2.
% 3.01/0.99  --res_out_proof                         true
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Options
% 3.01/0.99  
% 3.01/0.99  --superposition_flag                    true
% 3.01/0.99  --sup_passive_queue_type                priority_queues
% 3.01/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.01/0.99  --demod_completeness_check              fast
% 3.01/0.99  --demod_use_ground                      true
% 3.01/0.99  --sup_to_prop_solver                    passive
% 3.01/0.99  --sup_prop_simpl_new                    true
% 3.01/0.99  --sup_prop_simpl_given                  true
% 3.01/0.99  --sup_fun_splitting                     false
% 3.01/0.99  --sup_smt_interval                      50000
% 3.01/0.99  
% 3.01/0.99  ------ Superposition Simplification Setup
% 3.01/0.99  
% 3.01/0.99  --sup_indices_passive                   []
% 3.01/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_full_bw                           [BwDemod]
% 3.01/0.99  --sup_immed_triv                        [TrivRules]
% 3.01/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_immed_bw_main                     []
% 3.01/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/0.99  
% 3.01/0.99  ------ Combination Options
% 3.01/0.99  
% 3.01/0.99  --comb_res_mult                         3
% 3.01/0.99  --comb_sup_mult                         2
% 3.01/0.99  --comb_inst_mult                        10
% 3.01/0.99  
% 3.01/0.99  ------ Debug Options
% 3.01/0.99  
% 3.01/0.99  --dbg_backtrace                         false
% 3.01/0.99  --dbg_dump_prop_clauses                 false
% 3.01/0.99  --dbg_dump_prop_clauses_file            -
% 3.01/0.99  --dbg_out_stat                          false
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  ------ Proving...
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  % SZS status Theorem for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99   Resolution empty clause
% 3.01/0.99  
% 3.01/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  fof(f1,axiom,(
% 3.01/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f23,plain,(
% 3.01/0.99    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.01/0.99    inference(ennf_transformation,[],[f1])).
% 3.01/0.99  
% 3.01/0.99  fof(f42,plain,(
% 3.01/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.01/0.99    inference(nnf_transformation,[],[f23])).
% 3.01/0.99  
% 3.01/0.99  fof(f43,plain,(
% 3.01/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.01/0.99    inference(rectify,[],[f42])).
% 3.01/0.99  
% 3.01/0.99  fof(f44,plain,(
% 3.01/0.99    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f45,plain,(
% 3.01/0.99    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 3.01/0.99  
% 3.01/0.99  fof(f56,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f45])).
% 3.01/0.99  
% 3.01/0.99  fof(f19,axiom,(
% 3.01/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f38,plain,(
% 3.01/0.99    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.01/0.99    inference(ennf_transformation,[],[f19])).
% 3.01/0.99  
% 3.01/0.99  fof(f39,plain,(
% 3.01/0.99    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.01/0.99    inference(flattening,[],[f38])).
% 3.01/0.99  
% 3.01/0.99  fof(f82,plain,(
% 3.01/0.99    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f39])).
% 3.01/0.99  
% 3.01/0.99  fof(f20,conjecture,(
% 3.01/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f21,negated_conjecture,(
% 3.01/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 3.01/0.99    inference(negated_conjecture,[],[f20])).
% 3.01/0.99  
% 3.01/0.99  fof(f40,plain,(
% 3.01/0.99    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 3.01/0.99    inference(ennf_transformation,[],[f21])).
% 3.01/0.99  
% 3.01/0.99  fof(f41,plain,(
% 3.01/0.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 3.01/0.99    inference(flattening,[],[f40])).
% 3.01/0.99  
% 3.01/0.99  fof(f53,plain,(
% 3.01/0.99    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 3.01/0.99    introduced(choice_axiom,[])).
% 3.01/0.99  
% 3.01/0.99  fof(f54,plain,(
% 3.01/0.99    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 3.01/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f41,f53])).
% 3.01/0.99  
% 3.01/0.99  fof(f84,plain,(
% 3.01/0.99    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 3.01/0.99    inference(cnf_transformation,[],[f54])).
% 3.01/0.99  
% 3.01/0.99  fof(f3,axiom,(
% 3.01/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f61,plain,(
% 3.01/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f3])).
% 3.01/0.99  
% 3.01/0.99  fof(f4,axiom,(
% 3.01/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f62,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f4])).
% 3.01/0.99  
% 3.01/0.99  fof(f5,axiom,(
% 3.01/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f63,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f5])).
% 3.01/0.99  
% 3.01/0.99  fof(f88,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.01/0.99    inference(definition_unfolding,[],[f62,f63])).
% 3.01/0.99  
% 3.01/0.99  fof(f89,plain,(
% 3.01/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.01/0.99    inference(definition_unfolding,[],[f61,f88])).
% 3.01/0.99  
% 3.01/0.99  fof(f95,plain,(
% 3.01/0.99    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 3.01/0.99    inference(definition_unfolding,[],[f84,f89])).
% 3.01/0.99  
% 3.01/0.99  fof(f83,plain,(
% 3.01/0.99    v1_funct_1(sK3)),
% 3.01/0.99    inference(cnf_transformation,[],[f54])).
% 3.01/0.99  
% 3.01/0.99  fof(f85,plain,(
% 3.01/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 3.01/0.99    inference(cnf_transformation,[],[f54])).
% 3.01/0.99  
% 3.01/0.99  fof(f94,plain,(
% 3.01/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 3.01/0.99    inference(definition_unfolding,[],[f85,f89])).
% 3.01/0.99  
% 3.01/0.99  fof(f86,plain,(
% 3.01/0.99    k1_xboole_0 != sK2),
% 3.01/0.99    inference(cnf_transformation,[],[f54])).
% 3.01/0.99  
% 3.01/0.99  fof(f18,axiom,(
% 3.01/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f37,plain,(
% 3.01/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.99    inference(ennf_transformation,[],[f18])).
% 3.01/0.99  
% 3.01/0.99  fof(f81,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f37])).
% 3.01/0.99  
% 3.01/0.99  fof(f55,plain,(
% 3.01/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f45])).
% 3.01/0.99  
% 3.01/0.99  fof(f11,axiom,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f27,plain,(
% 3.01/0.99    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(ennf_transformation,[],[f11])).
% 3.01/0.99  
% 3.01/0.99  fof(f51,plain,(
% 3.01/0.99    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(nnf_transformation,[],[f27])).
% 3.01/0.99  
% 3.01/0.99  fof(f73,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f51])).
% 3.01/0.99  
% 3.01/0.99  fof(f16,axiom,(
% 3.01/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f35,plain,(
% 3.01/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.99    inference(ennf_transformation,[],[f16])).
% 3.01/0.99  
% 3.01/0.99  fof(f79,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f35])).
% 3.01/0.99  
% 3.01/0.99  fof(f14,axiom,(
% 3.01/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f31,plain,(
% 3.01/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.01/0.99    inference(ennf_transformation,[],[f14])).
% 3.01/0.99  
% 3.01/0.99  fof(f32,plain,(
% 3.01/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(flattening,[],[f31])).
% 3.01/0.99  
% 3.01/0.99  fof(f77,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f32])).
% 3.01/0.99  
% 3.01/0.99  fof(f91,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(definition_unfolding,[],[f77,f89])).
% 3.01/0.99  
% 3.01/0.99  fof(f87,plain,(
% 3.01/0.99    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)),
% 3.01/0.99    inference(cnf_transformation,[],[f54])).
% 3.01/0.99  
% 3.01/0.99  fof(f93,plain,(
% 3.01/0.99    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)),
% 3.01/0.99    inference(definition_unfolding,[],[f87,f89,f89])).
% 3.01/0.99  
% 3.01/0.99  fof(f8,axiom,(
% 3.01/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f24,plain,(
% 3.01/0.99    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 3.01/0.99    inference(ennf_transformation,[],[f8])).
% 3.01/0.99  
% 3.01/0.99  fof(f68,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f24])).
% 3.01/0.99  
% 3.01/0.99  fof(f90,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 3.01/0.99    inference(definition_unfolding,[],[f68,f89])).
% 3.01/0.99  
% 3.01/0.99  fof(f12,axiom,(
% 3.01/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f28,plain,(
% 3.01/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.01/0.99    inference(ennf_transformation,[],[f12])).
% 3.01/0.99  
% 3.01/0.99  fof(f29,plain,(
% 3.01/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(flattening,[],[f28])).
% 3.01/0.99  
% 3.01/0.99  fof(f74,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f29])).
% 3.01/0.99  
% 3.01/0.99  fof(f17,axiom,(
% 3.01/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f22,plain,(
% 3.01/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.01/0.99    inference(pure_predicate_removal,[],[f17])).
% 3.01/0.99  
% 3.01/0.99  fof(f36,plain,(
% 3.01/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/0.99    inference(ennf_transformation,[],[f22])).
% 3.01/0.99  
% 3.01/0.99  fof(f80,plain,(
% 3.01/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f36])).
% 3.01/0.99  
% 3.01/0.99  fof(f10,axiom,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f26,plain,(
% 3.01/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(ennf_transformation,[],[f10])).
% 3.01/0.99  
% 3.01/0.99  fof(f71,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f26])).
% 3.01/0.99  
% 3.01/0.99  fof(f6,axiom,(
% 3.01/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f48,plain,(
% 3.01/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.01/0.99    inference(nnf_transformation,[],[f6])).
% 3.01/0.99  
% 3.01/0.99  fof(f49,plain,(
% 3.01/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.01/0.99    inference(flattening,[],[f48])).
% 3.01/0.99  
% 3.01/0.99  fof(f66,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.01/0.99    inference(cnf_transformation,[],[f49])).
% 3.01/0.99  
% 3.01/0.99  fof(f98,plain,(
% 3.01/0.99    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.01/0.99    inference(equality_resolution,[],[f66])).
% 3.01/0.99  
% 3.01/0.99  fof(f7,axiom,(
% 3.01/0.99    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f67,plain,(
% 3.01/0.99    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 3.01/0.99    inference(cnf_transformation,[],[f7])).
% 3.01/0.99  
% 3.01/0.99  fof(f9,axiom,(
% 3.01/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f25,plain,(
% 3.01/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(ennf_transformation,[],[f9])).
% 3.01/0.99  
% 3.01/0.99  fof(f50,plain,(
% 3.01/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(nnf_transformation,[],[f25])).
% 3.01/0.99  
% 3.01/0.99  fof(f69,plain,(
% 3.01/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f50])).
% 3.01/0.99  
% 3.01/0.99  fof(f2,axiom,(
% 3.01/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f46,plain,(
% 3.01/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.01/0.99    inference(nnf_transformation,[],[f2])).
% 3.01/0.99  
% 3.01/0.99  fof(f47,plain,(
% 3.01/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.01/0.99    inference(flattening,[],[f46])).
% 3.01/0.99  
% 3.01/0.99  fof(f60,plain,(
% 3.01/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f47])).
% 3.01/0.99  
% 3.01/0.99  fof(f15,axiom,(
% 3.01/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.01/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.01/0.99  
% 3.01/0.99  fof(f33,plain,(
% 3.01/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.01/0.99    inference(ennf_transformation,[],[f15])).
% 3.01/0.99  
% 3.01/0.99  fof(f34,plain,(
% 3.01/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.01/0.99    inference(flattening,[],[f33])).
% 3.01/0.99  
% 3.01/0.99  fof(f78,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(cnf_transformation,[],[f34])).
% 3.01/0.99  
% 3.01/0.99  fof(f92,plain,(
% 3.01/0.99    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.01/0.99    inference(definition_unfolding,[],[f78,f89,f89])).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1,plain,
% 3.01/0.99      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1194,plain,
% 3.01/0.99      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.01/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_24,plain,
% 3.01/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.99      | ~ r2_hidden(X3,X1)
% 3.01/0.99      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.01/0.99      | ~ v1_funct_1(X0)
% 3.01/0.99      | k1_xboole_0 = X2 ),
% 3.01/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_28,negated_conjecture,
% 3.01/0.99      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 3.01/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_287,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.99      | ~ r2_hidden(X3,X1)
% 3.01/0.99      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 3.01/0.99      | ~ v1_funct_1(X0)
% 3.01/0.99      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 3.01/0.99      | sK2 != X2
% 3.01/0.99      | sK3 != X0
% 3.01/0.99      | k1_xboole_0 = X2 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_28]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_288,plain,
% 3.01/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 3.01/0.99      | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 3.01/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
% 3.01/0.99      | ~ v1_funct_1(sK3)
% 3.01/0.99      | k1_xboole_0 = sK2 ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_287]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_29,negated_conjecture,
% 3.01/0.99      ( v1_funct_1(sK3) ),
% 3.01/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_27,negated_conjecture,
% 3.01/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 3.01/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_26,negated_conjecture,
% 3.01/0.99      ( k1_xboole_0 != sK2 ),
% 3.01/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_292,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 3.01/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_288,c_29,c_27,c_26]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1189,plain,
% 3.01/0.99      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 3.01/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_23,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_308,plain,
% 3.01/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.01/0.99      | sK3 != X2 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_309,plain,
% 3.01/0.99      ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_308]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1388,plain,
% 3.01/0.99      ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 3.01/0.99      inference(equality_resolution,[status(thm)],[c_309]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1435,plain,
% 3.01/0.99      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 3.01/0.99      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 3.01/0.99      inference(light_normalisation,[status(thm)],[c_1189,c_1388]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2019,plain,
% 3.01/0.99      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1),X0)),k2_relat_1(sK3)) = iProver_top
% 3.01/0.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1194,c_1435]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.01/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1193,plain,
% 3.01/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.01/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.01/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2984,plain,
% 3.01/0.99      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1),X0)),X1) = iProver_top
% 3.01/0.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top
% 3.01/0.99      | r1_tarski(k2_relat_1(sK3),X1) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_2019,c_1193]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_14,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 3.01/0.99      | ~ v1_relat_1(X1)
% 3.01/0.99      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 3.01/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_21,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_329,plain,
% 3.01/0.99      ( v1_relat_1(X0)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.01/0.99      | sK3 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_330,plain,
% 3.01/0.99      ( v1_relat_1(sK3)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_329]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_538,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_relat_1(X1))
% 3.01/0.99      | k11_relat_1(X1,X0) = k1_xboole_0
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 3.01/0.99      | sK3 != X1 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_330]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_539,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_relat_1(sK3))
% 3.01/0.99      | k11_relat_1(sK3,X0) = k1_xboole_0
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_538]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_674,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_relat_1(sK3))
% 3.01/0.99      | k11_relat_1(sK3,X0) = k1_xboole_0
% 3.01/0.99      | ~ sP1_iProver_split ),
% 3.01/0.99      inference(splitting,
% 3.01/0.99                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 3.01/0.99                [c_539]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1164,plain,
% 3.01/0.99      ( k11_relat_1(sK3,X0) = k1_xboole_0
% 3.01/0.99      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 3.01/0.99      | sP1_iProver_split != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_675,plain,
% 3.01/0.99      ( sP1_iProver_split | sP0_iProver_split ),
% 3.01/0.99      inference(splitting,
% 3.01/0.99                [splitting(split),new_symbols(definition,[])],
% 3.01/0.99                [c_539]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_719,plain,
% 3.01/0.99      ( sP1_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_675]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_720,plain,
% 3.01/0.99      ( k11_relat_1(sK3,X0) = k1_xboole_0
% 3.01/0.99      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 3.01/0.99      | sP1_iProver_split != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_691,plain,( X0 = X0 ),theory(equality) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1391,plain,
% 3.01/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_691]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_673,plain,
% 3.01/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.01/0.99      | ~ sP0_iProver_split ),
% 3.01/0.99      inference(splitting,
% 3.01/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.01/0.99                [c_539]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1394,plain,
% 3.01/0.99      ( ~ sP0_iProver_split
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_673]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1396,plain,
% 3.01/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 3.01/0.99      | sP0_iProver_split != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1394]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1476,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) = iProver_top
% 3.01/0.99      | k11_relat_1(sK3,X0) = k1_xboole_0 ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_1164,c_719,c_720,c_1391,c_1396]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1477,plain,
% 3.01/0.99      ( k11_relat_1(sK3,X0) = k1_xboole_0
% 3.01/0.99      | r2_hidden(X0,k1_relat_1(sK3)) = iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_1476]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_19,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.01/0.99      | ~ v1_funct_1(X1)
% 3.01/0.99      | ~ v1_relat_1(X1)
% 3.01/0.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_349,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.01/0.99      | ~ v1_relat_1(X1)
% 3.01/0.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k11_relat_1(X1,X0)
% 3.01/0.99      | sK3 != X1 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_350,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.01/0.99      | ~ v1_relat_1(sK3)
% 3.01/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_349]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_454,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.01/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 3.01/0.99      inference(resolution,[status(thm)],[c_330,c_350]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_686,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.01/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.01/0.99      | ~ sP6_iProver_split ),
% 3.01/0.99      inference(splitting,
% 3.01/0.99                [splitting(split),new_symbols(definition,[sP6_iProver_split])],
% 3.01/0.99                [c_454]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1183,plain,
% 3.01/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.01/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.01/0.99      | sP6_iProver_split != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_687,plain,
% 3.01/0.99      ( sP6_iProver_split | sP0_iProver_split ),
% 3.01/0.99      inference(splitting,
% 3.01/0.99                [splitting(split),new_symbols(definition,[])],
% 3.01/0.99                [c_454]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_750,plain,
% 3.01/0.99      ( sP6_iProver_split = iProver_top | sP0_iProver_split = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_751,plain,
% 3.01/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.01/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.01/0.99      | sP6_iProver_split != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2080,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.01/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_1183,c_750,c_751,c_1391,c_1396]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2081,plain,
% 3.01/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.01/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 3.01/0.99      inference(renaming,[status(thm)],[c_2080]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2089,plain,
% 3.01/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k11_relat_1(sK3,X0)
% 3.01/0.99      | k11_relat_1(sK3,X0) = k1_xboole_0 ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1477,c_2081]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_25,negated_conjecture,
% 3.01/0.99      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
% 3.01/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1390,plain,
% 3.01/0.99      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
% 3.01/0.99      inference(demodulation,[status(thm)],[c_1388,c_25]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3153,plain,
% 3.01/0.99      ( k11_relat_1(sK3,sK1) != k2_relat_1(sK3)
% 3.01/0.99      | k11_relat_1(sK3,sK1) = k1_xboole_0 ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_2089,c_1390]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_10,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0)
% 3.01/0.99      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_514,plain,
% 3.01/0.99      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 3.01/0.99      | sK3 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_330]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_515,plain,
% 3.01/0.99      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_514]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_678,plain,
% 3.01/0.99      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
% 3.01/0.99      | ~ sP3_iProver_split ),
% 3.01/0.99      inference(splitting,
% 3.01/0.99                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 3.01/0.99                [c_515]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1170,plain,
% 3.01/0.99      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
% 3.01/0.99      | sP3_iProver_split != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_679,plain,
% 3.01/0.99      ( sP3_iProver_split | sP0_iProver_split ),
% 3.01/0.99      inference(splitting,
% 3.01/0.99                [splitting(split),new_symbols(definition,[])],
% 3.01/0.99                [c_515]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1750,plain,
% 3.01/0.99      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_1170,c_679,c_678,c_1391,c_1394]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_16,plain,
% 3.01/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.01/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_22,plain,
% 3.01/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_317,plain,
% 3.01/0.99      ( v4_relat_1(X0,X1)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 3.01/0.99      | sK3 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_318,plain,
% 3.01/0.99      ( v4_relat_1(sK3,X0)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_317]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_402,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0)
% 3.01/0.99      | X1 != X2
% 3.01/0.99      | k7_relat_1(X0,X2) = X0
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X3))
% 3.01/0.99      | sK3 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_318]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_403,plain,
% 3.01/0.99      ( ~ v1_relat_1(sK3)
% 3.01/0.99      | k7_relat_1(sK3,X0) = sK3
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_402]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_407,plain,
% 3.01/0.99      ( k7_relat_1(sK3,X0) = sK3
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.01/0.99      inference(global_propositional_subsumption,[status(thm)],[c_403,c_330]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1407,plain,
% 3.01/0.99      ( k7_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = sK3 ),
% 3.01/0.99      inference(equality_resolution,[status(thm)],[c_407]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_13,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.01/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_505,plain,
% 3.01/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.01/0.99      | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
% 3.01/0.99      | sK3 != X2 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_330]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_506,plain,
% 3.01/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.01/0.99      | k2_relat_1(k7_relat_1(sK3,X2)) = k9_relat_1(sK3,X2) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_505]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_680,plain,
% 3.01/0.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0)
% 3.01/0.99      | ~ sP4_iProver_split ),
% 3.01/0.99      inference(splitting,
% 3.01/0.99                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 3.01/0.99                [c_506]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1174,plain,
% 3.01/0.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0)
% 3.01/0.99      | sP4_iProver_split != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_681,plain,
% 3.01/0.99      ( sP4_iProver_split | sP0_iProver_split ),
% 3.01/0.99      inference(splitting,
% 3.01/0.99                [splitting(split),new_symbols(definition,[])],
% 3.01/0.99                [c_506]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1694,plain,
% 3.01/0.99      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_1174,c_681,c_680,c_1391,c_1394]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1698,plain,
% 3.01/0.99      ( k9_relat_1(sK3,k2_enumset1(sK1,sK1,sK1,sK1)) = k2_relat_1(sK3) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1407,c_1694]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2918,plain,
% 3.01/0.99      ( k11_relat_1(sK3,sK1) = k2_relat_1(sK3) ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1750,c_1698]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3156,plain,
% 3.01/0.99      ( k11_relat_1(sK3,sK1) = k1_xboole_0
% 3.01/0.99      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 3.01/0.99      inference(light_normalisation,[status(thm)],[c_3153,c_2918]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3157,plain,
% 3.01/0.99      ( k11_relat_1(sK3,sK1) = k1_xboole_0 ),
% 3.01/0.99      inference(equality_resolution_simp,[status(thm)],[c_3156]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3200,plain,
% 3.01/0.99      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 3.01/0.99      inference(demodulation,[status(thm)],[c_3157,c_2918]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4068,plain,
% 3.01/0.99      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1),X0)),X1) = iProver_top
% 3.01/0.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top
% 3.01/0.99      | r1_tarski(k1_xboole_0,X1) != iProver_top ),
% 3.01/0.99      inference(light_normalisation,[status(thm)],[c_2984,c_3200]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_6,plain,
% 3.01/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.01/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_9,plain,
% 3.01/0.99      ( ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
% 3.01/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1190,plain,
% 3.01/0.99      ( r2_hidden(X0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1959,plain,
% 3.01/0.99      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_6,c_1190]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2020,plain,
% 3.01/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_1194,c_1959]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4072,plain,
% 3.01/0.99      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1),X0)),X1) = iProver_top
% 3.01/0.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top ),
% 3.01/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4068,c_2020]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4079,plain,
% 3.01/0.99      ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),X0) = iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_4072,c_1959]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_12,plain,
% 3.01/0.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_416,plain,
% 3.01/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.01/0.99      | ~ v1_relat_1(X0)
% 3.01/0.99      | X2 != X1
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 3.01/0.99      | sK3 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_318]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_417,plain,
% 3.01/0.99      ( r1_tarski(k1_relat_1(sK3),X0)
% 3.01/0.99      | ~ v1_relat_1(sK3)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_416]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_421,plain,
% 3.01/0.99      ( r1_tarski(k1_relat_1(sK3),X0)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 3.01/0.99      inference(global_propositional_subsumption,[status(thm)],[c_417,c_330]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1188,plain,
% 3.01/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 3.01/0.99      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2064,plain,
% 3.01/0.99      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 3.01/0.99      inference(equality_resolution,[status(thm)],[c_1188]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3,plain,
% 3.01/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.01/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1192,plain,
% 3.01/0.99      ( X0 = X1
% 3.01/0.99      | r1_tarski(X1,X0) != iProver_top
% 3.01/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_2974,plain,
% 3.01/0.99      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 3.01/0.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_2064,c_1192]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_20,plain,
% 3.01/0.99      ( ~ v1_funct_1(X0)
% 3.01/0.99      | ~ v1_relat_1(X0)
% 3.01/0.99      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.01/0.99      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.01/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_364,plain,
% 3.01/0.99      ( ~ v1_relat_1(X0)
% 3.01/0.99      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.01/0.99      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.01/0.99      | sK3 != X0 ),
% 3.01/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_365,plain,
% 3.01/0.99      ( ~ v1_relat_1(sK3)
% 3.01/0.99      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.01/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.01/0.99      inference(unflattening,[status(thm)],[c_364]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_443,plain,
% 3.01/0.99      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.01/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 3.01/0.99      inference(resolution,[status(thm)],[c_330,c_365]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_689,plain,
% 3.01/0.99      ( sP7_iProver_split | sP0_iProver_split ),
% 3.01/0.99      inference(splitting,
% 3.01/0.99                [splitting(split),new_symbols(definition,[])],
% 3.01/0.99                [c_443]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_688,plain,
% 3.01/0.99      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.01/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.01/0.99      | ~ sP7_iProver_split ),
% 3.01/0.99      inference(splitting,
% 3.01/0.99                [splitting(split),new_symbols(definition,[sP7_iProver_split])],
% 3.01/0.99                [c_443]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_757,plain,
% 3.01/0.99      ( ~ sP7_iProver_split
% 3.01/0.99      | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
% 3.01/0.99      | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_688]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1392,plain,
% 3.01/0.99      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1))
% 3.01/0.99      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_421]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1398,plain,
% 3.01/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))
% 3.01/0.99      | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1392]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1788,plain,
% 3.01/0.99      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3))
% 3.01/0.99      | ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0))
% 3.01/0.99      | k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3) ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1789,plain,
% 3.01/0.99      ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(sK3)
% 3.01/0.99      | r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3)) != iProver_top
% 3.01/0.99      | r1_tarski(k1_relat_1(sK3),k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.01/0.99      inference(predicate_to_equality,[status(thm)],[c_1788]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_1791,plain,
% 3.01/0.99      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 3.01/0.99      | r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top
% 3.01/0.99      | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 3.01/0.99      inference(instantiation,[status(thm)],[c_1789]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_3528,plain,
% 3.01/0.99      ( r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),k1_relat_1(sK3)) != iProver_top ),
% 3.01/0.99      inference(global_propositional_subsumption,
% 3.01/0.99                [status(thm)],
% 3.01/0.99                [c_2974,c_689,c_757,c_1390,c_1391,c_1394,c_1398,c_1791]) ).
% 3.01/0.99  
% 3.01/0.99  cnf(c_4207,plain,
% 3.01/0.99      ( $false ),
% 3.01/0.99      inference(superposition,[status(thm)],[c_4079,c_3528]) ).
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/0.99  
% 3.01/0.99  ------                               Statistics
% 3.01/0.99  
% 3.01/0.99  ------ General
% 3.01/0.99  
% 3.01/0.99  abstr_ref_over_cycles:                  0
% 3.01/0.99  abstr_ref_under_cycles:                 0
% 3.01/0.99  gc_basic_clause_elim:                   0
% 3.01/0.99  forced_gc_time:                         0
% 3.01/0.99  parsing_time:                           0.009
% 3.01/0.99  unif_index_cands_time:                  0.
% 3.01/0.99  unif_index_add_time:                    0.
% 3.01/0.99  orderings_time:                         0.
% 3.01/0.99  out_proof_time:                         0.011
% 3.01/0.99  total_time:                             0.158
% 3.01/0.99  num_of_symbols:                         61
% 3.01/0.99  num_of_terms:                           3500
% 3.01/0.99  
% 3.01/0.99  ------ Preprocessing
% 3.01/0.99  
% 3.01/0.99  num_of_splits:                          16
% 3.01/0.99  num_of_split_atoms:                     8
% 3.01/0.99  num_of_reused_defs:                     8
% 3.01/0.99  num_eq_ax_congr_red:                    22
% 3.01/0.99  num_of_sem_filtered_clauses:            1
% 3.01/0.99  num_of_subtypes:                        0
% 3.01/0.99  monotx_restored_types:                  0
% 3.01/0.99  sat_num_of_epr_types:                   0
% 3.01/0.99  sat_num_of_non_cyclic_types:            0
% 3.01/0.99  sat_guarded_non_collapsed_types:        0
% 3.01/0.99  num_pure_diseq_elim:                    0
% 3.01/0.99  simp_replaced_by:                       0
% 3.01/0.99  res_preprocessed:                       146
% 3.01/0.99  prep_upred:                             0
% 3.01/0.99  prep_unflattend:                        19
% 3.01/0.99  smt_new_axioms:                         0
% 3.01/0.99  pred_elim_cands:                        2
% 3.01/0.99  pred_elim:                              5
% 3.01/0.99  pred_elim_cl:                           5
% 3.01/0.99  pred_elim_cycles:                       7
% 3.01/0.99  merged_defs:                            0
% 3.01/0.99  merged_defs_ncl:                        0
% 3.01/0.99  bin_hyper_res:                          0
% 3.01/0.99  prep_cycles:                            4
% 3.01/0.99  pred_elim_time:                         0.007
% 3.01/0.99  splitting_time:                         0.
% 3.01/0.99  sem_filter_time:                        0.
% 3.01/0.99  monotx_time:                            0.001
% 3.01/0.99  subtype_inf_time:                       0.
% 3.01/0.99  
% 3.01/0.99  ------ Problem properties
% 3.01/0.99  
% 3.01/0.99  clauses:                                40
% 3.01/0.99  conjectures:                            2
% 3.01/0.99  epr:                                    11
% 3.01/0.99  horn:                                   28
% 3.01/0.99  ground:                                 11
% 3.01/0.99  unary:                                  6
% 3.01/0.99  binary:                                 24
% 3.01/0.99  lits:                                   84
% 3.01/0.99  lits_eq:                                34
% 3.01/0.99  fd_pure:                                0
% 3.01/0.99  fd_pseudo:                              0
% 3.01/0.99  fd_cond:                                1
% 3.01/0.99  fd_pseudo_cond:                         1
% 3.01/0.99  ac_symbols:                             0
% 3.01/0.99  
% 3.01/0.99  ------ Propositional Solver
% 3.01/0.99  
% 3.01/0.99  prop_solver_calls:                      28
% 3.01/0.99  prop_fast_solver_calls:                 911
% 3.01/0.99  smt_solver_calls:                       0
% 3.01/0.99  smt_fast_solver_calls:                  0
% 3.01/0.99  prop_num_of_clauses:                    1576
% 3.01/0.99  prop_preprocess_simplified:             5144
% 3.01/0.99  prop_fo_subsumed:                       23
% 3.01/0.99  prop_solver_time:                       0.
% 3.01/0.99  smt_solver_time:                        0.
% 3.01/0.99  smt_fast_solver_time:                   0.
% 3.01/0.99  prop_fast_solver_time:                  0.
% 3.01/0.99  prop_unsat_core_time:                   0.
% 3.01/0.99  
% 3.01/0.99  ------ QBF
% 3.01/0.99  
% 3.01/0.99  qbf_q_res:                              0
% 3.01/0.99  qbf_num_tautologies:                    0
% 3.01/0.99  qbf_prep_cycles:                        0
% 3.01/0.99  
% 3.01/0.99  ------ BMC1
% 3.01/0.99  
% 3.01/0.99  bmc1_current_bound:                     -1
% 3.01/0.99  bmc1_last_solved_bound:                 -1
% 3.01/0.99  bmc1_unsat_core_size:                   -1
% 3.01/0.99  bmc1_unsat_core_parents_size:           -1
% 3.01/0.99  bmc1_merge_next_fun:                    0
% 3.01/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.01/0.99  
% 3.01/0.99  ------ Instantiation
% 3.01/0.99  
% 3.01/0.99  inst_num_of_clauses:                    487
% 3.01/0.99  inst_num_in_passive:                    154
% 3.01/0.99  inst_num_in_active:                     234
% 3.01/0.99  inst_num_in_unprocessed:                99
% 3.01/0.99  inst_num_of_loops:                      360
% 3.01/0.99  inst_num_of_learning_restarts:          0
% 3.01/0.99  inst_num_moves_active_passive:          123
% 3.01/0.99  inst_lit_activity:                      0
% 3.01/0.99  inst_lit_activity_moves:                0
% 3.01/0.99  inst_num_tautologies:                   0
% 3.01/0.99  inst_num_prop_implied:                  0
% 3.01/0.99  inst_num_existing_simplified:           0
% 3.01/0.99  inst_num_eq_res_simplified:             0
% 3.01/0.99  inst_num_child_elim:                    0
% 3.01/0.99  inst_num_of_dismatching_blockings:      97
% 3.01/0.99  inst_num_of_non_proper_insts:           464
% 3.01/0.99  inst_num_of_duplicates:                 0
% 3.01/0.99  inst_inst_num_from_inst_to_res:         0
% 3.01/0.99  inst_dismatching_checking_time:         0.
% 3.01/0.99  
% 3.01/0.99  ------ Resolution
% 3.01/0.99  
% 3.01/0.99  res_num_of_clauses:                     0
% 3.01/0.99  res_num_in_passive:                     0
% 3.01/0.99  res_num_in_active:                      0
% 3.01/0.99  res_num_of_loops:                       150
% 3.01/0.99  res_forward_subset_subsumed:            99
% 3.01/0.99  res_backward_subset_subsumed:           0
% 3.01/0.99  res_forward_subsumed:                   0
% 3.01/0.99  res_backward_subsumed:                  0
% 3.01/0.99  res_forward_subsumption_resolution:     0
% 3.01/0.99  res_backward_subsumption_resolution:    0
% 3.01/0.99  res_clause_to_clause_subsumption:       208
% 3.01/0.99  res_orphan_elimination:                 0
% 3.01/0.99  res_tautology_del:                      38
% 3.01/0.99  res_num_eq_res_simplified:              0
% 3.01/0.99  res_num_sel_changes:                    0
% 3.01/0.99  res_moves_from_active_to_pass:          0
% 3.01/0.99  
% 3.01/0.99  ------ Superposition
% 3.01/0.99  
% 3.01/0.99  sup_time_total:                         0.
% 3.01/0.99  sup_time_generating:                    0.
% 3.01/0.99  sup_time_sim_full:                      0.
% 3.01/0.99  sup_time_sim_immed:                     0.
% 3.01/0.99  
% 3.01/0.99  sup_num_of_clauses:                     78
% 3.01/0.99  sup_num_in_active:                      52
% 3.01/0.99  sup_num_in_passive:                     26
% 3.01/0.99  sup_num_of_loops:                       70
% 3.01/0.99  sup_fw_superposition:                   38
% 3.01/0.99  sup_bw_superposition:                   39
% 3.01/0.99  sup_immediate_simplified:               15
% 3.01/0.99  sup_given_eliminated:                   1
% 3.01/0.99  comparisons_done:                       0
% 3.01/0.99  comparisons_avoided:                    9
% 3.01/0.99  
% 3.01/0.99  ------ Simplifications
% 3.01/0.99  
% 3.01/0.99  
% 3.01/0.99  sim_fw_subset_subsumed:                 6
% 3.01/0.99  sim_bw_subset_subsumed:                 1
% 3.01/0.99  sim_fw_subsumed:                        3
% 3.01/0.99  sim_bw_subsumed:                        3
% 3.01/0.99  sim_fw_subsumption_res:                 1
% 3.01/0.99  sim_bw_subsumption_res:                 0
% 3.01/0.99  sim_tautology_del:                      2
% 3.01/0.99  sim_eq_tautology_del:                   3
% 3.01/0.99  sim_eq_res_simp:                        3
% 3.01/0.99  sim_fw_demodulated:                     0
% 3.01/0.99  sim_bw_demodulated:                     18
% 3.01/0.99  sim_light_normalised:                   6
% 3.01/0.99  sim_joinable_taut:                      0
% 3.01/0.99  sim_joinable_simp:                      0
% 3.01/0.99  sim_ac_normalised:                      0
% 3.01/0.99  sim_smt_subsumption:                    0
% 3.01/0.99  
%------------------------------------------------------------------------------
