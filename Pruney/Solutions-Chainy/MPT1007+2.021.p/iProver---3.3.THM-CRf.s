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
% DateTime   : Thu Dec  3 12:04:46 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 353 expanded)
%              Number of clauses        :   79 (  93 expanded)
%              Number of leaves         :   21 (  82 expanded)
%              Depth                    :   18
%              Number of atoms          :  422 ( 971 expanded)
%              Number of equality atoms :  147 ( 318 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => r2_hidden(k1_funct_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(k1_funct_1(X2,X0),X1)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
      & k1_xboole_0 != sK2
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
      & v1_funct_2(sK3,k1_tarski(sK1),sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f46])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f80])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f77,f81])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f42])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f61,f81,f81])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f35])).

fof(f37,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f76,f81])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f47])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f82,plain,(
    ! [X0] : ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f58,f81])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f84,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f59,f81])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f79,plain,(
    ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_443,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_444,plain,
    ( v4_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_498,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_444])).

cnf(c_499,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_455,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_456,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_455])).

cnf(c_503,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_499,c_456])).

cnf(c_1240,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_503])).

cnf(c_1494,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1240])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1243,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2056,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1494,c_1243])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_94,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_519,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(X2) = k1_xboole_0
    | k1_relat_1(X2) != k1_xboole_0
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_456])).

cnf(c_520,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_519])).

cnf(c_737,plain,
    ( sP0_iProver_split
    | k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_520])).

cnf(c_741,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1405,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(sK3))
    | k2_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_741])).

cnf(c_1406,plain,
    ( k2_relat_1(sK3) != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1405])).

cnf(c_1408,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | v1_xboole_0(k2_relat_1(sK3)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1406])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_543,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_456])).

cnf(c_544,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK3))
    | v1_xboole_0(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_734,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_544])).

cnf(c_1235,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_734])).

cnf(c_1457,plain,
    ( sP0_iProver_split != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1235])).

cnf(c_1458,plain,
    ( ~ sP0_iProver_split ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1457])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1254,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_395,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_399,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_395,c_28,c_26,c_25])).

cnf(c_1241,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_434,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_435,plain,
    ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_1412,plain,
    ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_435])).

cnf(c_1448,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1241,c_1412])).

cnf(c_2064,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),k2_relat_1(sK3)) = iProver_top
    | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_1448])).

cnf(c_7,plain,
    ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1749,plain,
    ( ~ v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1750,plain,
    ( v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1749])).

cnf(c_2260,plain,
    ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),k2_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2064,c_1750])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1253,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2265,plain,
    ( v1_xboole_0(k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2260,c_1253])).

cnf(c_2446,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2056,c_94,c_737,c_1408,c_1458,c_2265])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1249,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_9,plain,
    ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
    | r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1246,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2156,plain,
    ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1249,c_1246])).

cnf(c_2812,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2446,c_2156])).

cnf(c_18,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X4))
    | r2_hidden(k1_funct_1(X4,X3),X5)
    | ~ v1_funct_1(X4)
    | ~ v1_relat_1(X4)
    | X0 != X4
    | X2 != X5 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_20])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_370,plain,
    ( ~ v1_funct_1(X0)
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_19])).

cnf(c_371,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_370])).

cnf(c_415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X3),X2)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_371,c_28])).

cnf(c_416,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r2_hidden(X2,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X2),X1) ),
    inference(unflattening,[status(thm)],[c_415])).

cnf(c_467,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_416])).

cnf(c_587,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | r2_hidden(k1_funct_1(sK3,X0),X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
    inference(equality_resolution_simp,[status(thm)],[c_467])).

cnf(c_1233,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_1500,plain,
    ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1233])).

cnf(c_24,negated_conjecture,
    ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1242,plain,
    ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1885,plain,
    ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1500,c_1242])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2812,c_1885])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:16:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 1.99/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/0.99  
% 1.99/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.99/0.99  
% 1.99/0.99  ------  iProver source info
% 1.99/0.99  
% 1.99/0.99  git: date: 2020-06-30 10:37:57 +0100
% 1.99/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.99/0.99  git: non_committed_changes: false
% 1.99/0.99  git: last_make_outside_of_git: false
% 1.99/0.99  
% 1.99/0.99  ------ 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options
% 1.99/0.99  
% 1.99/0.99  --out_options                           all
% 1.99/0.99  --tptp_safe_out                         true
% 1.99/0.99  --problem_path                          ""
% 1.99/0.99  --include_path                          ""
% 1.99/0.99  --clausifier                            res/vclausify_rel
% 1.99/0.99  --clausifier_options                    --mode clausify
% 1.99/0.99  --stdin                                 false
% 1.99/0.99  --stats_out                             all
% 1.99/0.99  
% 1.99/0.99  ------ General Options
% 1.99/0.99  
% 1.99/0.99  --fof                                   false
% 1.99/0.99  --time_out_real                         305.
% 1.99/0.99  --time_out_virtual                      -1.
% 1.99/0.99  --symbol_type_check                     false
% 1.99/0.99  --clausify_out                          false
% 1.99/0.99  --sig_cnt_out                           false
% 1.99/0.99  --trig_cnt_out                          false
% 1.99/0.99  --trig_cnt_out_tolerance                1.
% 1.99/0.99  --trig_cnt_out_sk_spl                   false
% 1.99/0.99  --abstr_cl_out                          false
% 1.99/0.99  
% 1.99/0.99  ------ Global Options
% 1.99/0.99  
% 1.99/0.99  --schedule                              default
% 1.99/0.99  --add_important_lit                     false
% 1.99/0.99  --prop_solver_per_cl                    1000
% 1.99/0.99  --min_unsat_core                        false
% 1.99/0.99  --soft_assumptions                      false
% 1.99/0.99  --soft_lemma_size                       3
% 1.99/0.99  --prop_impl_unit_size                   0
% 1.99/0.99  --prop_impl_unit                        []
% 1.99/0.99  --share_sel_clauses                     true
% 1.99/0.99  --reset_solvers                         false
% 1.99/0.99  --bc_imp_inh                            [conj_cone]
% 1.99/0.99  --conj_cone_tolerance                   3.
% 1.99/0.99  --extra_neg_conj                        none
% 1.99/0.99  --large_theory_mode                     true
% 1.99/0.99  --prolific_symb_bound                   200
% 1.99/0.99  --lt_threshold                          2000
% 1.99/0.99  --clause_weak_htbl                      true
% 1.99/0.99  --gc_record_bc_elim                     false
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing Options
% 1.99/0.99  
% 1.99/0.99  --preprocessing_flag                    true
% 1.99/0.99  --time_out_prep_mult                    0.1
% 1.99/0.99  --splitting_mode                        input
% 1.99/0.99  --splitting_grd                         true
% 1.99/0.99  --splitting_cvd                         false
% 1.99/0.99  --splitting_cvd_svl                     false
% 1.99/0.99  --splitting_nvd                         32
% 1.99/0.99  --sub_typing                            true
% 1.99/0.99  --prep_gs_sim                           true
% 1.99/0.99  --prep_unflatten                        true
% 1.99/0.99  --prep_res_sim                          true
% 1.99/0.99  --prep_upred                            true
% 1.99/0.99  --prep_sem_filter                       exhaustive
% 1.99/0.99  --prep_sem_filter_out                   false
% 1.99/0.99  --pred_elim                             true
% 1.99/0.99  --res_sim_input                         true
% 1.99/0.99  --eq_ax_congr_red                       true
% 1.99/0.99  --pure_diseq_elim                       true
% 1.99/0.99  --brand_transform                       false
% 1.99/0.99  --non_eq_to_eq                          false
% 1.99/0.99  --prep_def_merge                        true
% 1.99/0.99  --prep_def_merge_prop_impl              false
% 1.99/0.99  --prep_def_merge_mbd                    true
% 1.99/0.99  --prep_def_merge_tr_red                 false
% 1.99/0.99  --prep_def_merge_tr_cl                  false
% 1.99/0.99  --smt_preprocessing                     true
% 1.99/0.99  --smt_ac_axioms                         fast
% 1.99/0.99  --preprocessed_out                      false
% 1.99/0.99  --preprocessed_stats                    false
% 1.99/0.99  
% 1.99/0.99  ------ Abstraction refinement Options
% 1.99/0.99  
% 1.99/0.99  --abstr_ref                             []
% 1.99/0.99  --abstr_ref_prep                        false
% 1.99/0.99  --abstr_ref_until_sat                   false
% 1.99/0.99  --abstr_ref_sig_restrict                funpre
% 1.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.99  --abstr_ref_under                       []
% 1.99/0.99  
% 1.99/0.99  ------ SAT Options
% 1.99/0.99  
% 1.99/0.99  --sat_mode                              false
% 1.99/0.99  --sat_fm_restart_options                ""
% 1.99/0.99  --sat_gr_def                            false
% 1.99/0.99  --sat_epr_types                         true
% 1.99/0.99  --sat_non_cyclic_types                  false
% 1.99/0.99  --sat_finite_models                     false
% 1.99/0.99  --sat_fm_lemmas                         false
% 1.99/0.99  --sat_fm_prep                           false
% 1.99/0.99  --sat_fm_uc_incr                        true
% 1.99/0.99  --sat_out_model                         small
% 1.99/0.99  --sat_out_clauses                       false
% 1.99/0.99  
% 1.99/0.99  ------ QBF Options
% 1.99/0.99  
% 1.99/0.99  --qbf_mode                              false
% 1.99/0.99  --qbf_elim_univ                         false
% 1.99/0.99  --qbf_dom_inst                          none
% 1.99/0.99  --qbf_dom_pre_inst                      false
% 1.99/0.99  --qbf_sk_in                             false
% 1.99/0.99  --qbf_pred_elim                         true
% 1.99/0.99  --qbf_split                             512
% 1.99/0.99  
% 1.99/0.99  ------ BMC1 Options
% 1.99/0.99  
% 1.99/0.99  --bmc1_incremental                      false
% 1.99/0.99  --bmc1_axioms                           reachable_all
% 1.99/0.99  --bmc1_min_bound                        0
% 1.99/0.99  --bmc1_max_bound                        -1
% 1.99/0.99  --bmc1_max_bound_default                -1
% 1.99/0.99  --bmc1_symbol_reachability              true
% 1.99/0.99  --bmc1_property_lemmas                  false
% 1.99/0.99  --bmc1_k_induction                      false
% 1.99/0.99  --bmc1_non_equiv_states                 false
% 1.99/0.99  --bmc1_deadlock                         false
% 1.99/0.99  --bmc1_ucm                              false
% 1.99/0.99  --bmc1_add_unsat_core                   none
% 1.99/0.99  --bmc1_unsat_core_children              false
% 1.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.99  --bmc1_out_stat                         full
% 1.99/0.99  --bmc1_ground_init                      false
% 1.99/0.99  --bmc1_pre_inst_next_state              false
% 1.99/0.99  --bmc1_pre_inst_state                   false
% 1.99/0.99  --bmc1_pre_inst_reach_state             false
% 1.99/0.99  --bmc1_out_unsat_core                   false
% 1.99/0.99  --bmc1_aig_witness_out                  false
% 1.99/0.99  --bmc1_verbose                          false
% 1.99/0.99  --bmc1_dump_clauses_tptp                false
% 1.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.99  --bmc1_dump_file                        -
% 1.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.99  --bmc1_ucm_extend_mode                  1
% 1.99/0.99  --bmc1_ucm_init_mode                    2
% 1.99/0.99  --bmc1_ucm_cone_mode                    none
% 1.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.99  --bmc1_ucm_relax_model                  4
% 1.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.99  --bmc1_ucm_layered_model                none
% 1.99/0.99  --bmc1_ucm_max_lemma_size               10
% 1.99/0.99  
% 1.99/0.99  ------ AIG Options
% 1.99/0.99  
% 1.99/0.99  --aig_mode                              false
% 1.99/0.99  
% 1.99/0.99  ------ Instantiation Options
% 1.99/0.99  
% 1.99/0.99  --instantiation_flag                    true
% 1.99/0.99  --inst_sos_flag                         false
% 1.99/0.99  --inst_sos_phase                        true
% 1.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel_side                     num_symb
% 1.99/0.99  --inst_solver_per_active                1400
% 1.99/0.99  --inst_solver_calls_frac                1.
% 1.99/0.99  --inst_passive_queue_type               priority_queues
% 1.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/0.99  --inst_passive_queues_freq              [25;2]
% 1.99/0.99  --inst_dismatching                      true
% 1.99/0.99  --inst_eager_unprocessed_to_passive     true
% 1.99/0.99  --inst_prop_sim_given                   true
% 1.99/0.99  --inst_prop_sim_new                     false
% 1.99/0.99  --inst_subs_new                         false
% 1.99/0.99  --inst_eq_res_simp                      false
% 1.99/0.99  --inst_subs_given                       false
% 1.99/0.99  --inst_orphan_elimination               true
% 1.99/0.99  --inst_learning_loop_flag               true
% 1.99/0.99  --inst_learning_start                   3000
% 1.99/0.99  --inst_learning_factor                  2
% 1.99/0.99  --inst_start_prop_sim_after_learn       3
% 1.99/0.99  --inst_sel_renew                        solver
% 1.99/0.99  --inst_lit_activity_flag                true
% 1.99/0.99  --inst_restr_to_given                   false
% 1.99/0.99  --inst_activity_threshold               500
% 1.99/0.99  --inst_out_proof                        true
% 1.99/0.99  
% 1.99/0.99  ------ Resolution Options
% 1.99/0.99  
% 1.99/0.99  --resolution_flag                       true
% 1.99/0.99  --res_lit_sel                           adaptive
% 1.99/0.99  --res_lit_sel_side                      none
% 1.99/0.99  --res_ordering                          kbo
% 1.99/0.99  --res_to_prop_solver                    active
% 1.99/0.99  --res_prop_simpl_new                    false
% 1.99/0.99  --res_prop_simpl_given                  true
% 1.99/0.99  --res_passive_queue_type                priority_queues
% 1.99/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/0.99  --res_passive_queues_freq               [15;5]
% 1.99/0.99  --res_forward_subs                      full
% 1.99/0.99  --res_backward_subs                     full
% 1.99/0.99  --res_forward_subs_resolution           true
% 1.99/0.99  --res_backward_subs_resolution          true
% 1.99/0.99  --res_orphan_elimination                true
% 1.99/0.99  --res_time_limit                        2.
% 1.99/0.99  --res_out_proof                         true
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Options
% 1.99/0.99  
% 1.99/0.99  --superposition_flag                    true
% 1.99/0.99  --sup_passive_queue_type                priority_queues
% 1.99/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/0.99  --sup_passive_queues_freq               [8;1;4]
% 1.99/0.99  --demod_completeness_check              fast
% 1.99/0.99  --demod_use_ground                      true
% 1.99/0.99  --sup_to_prop_solver                    passive
% 1.99/0.99  --sup_prop_simpl_new                    true
% 1.99/0.99  --sup_prop_simpl_given                  true
% 1.99/0.99  --sup_fun_splitting                     false
% 1.99/0.99  --sup_smt_interval                      50000
% 1.99/0.99  
% 1.99/0.99  ------ Superposition Simplification Setup
% 1.99/0.99  
% 1.99/0.99  --sup_indices_passive                   []
% 1.99/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_full_bw                           [BwDemod]
% 1.99/0.99  --sup_immed_triv                        [TrivRules]
% 1.99/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_immed_bw_main                     []
% 1.99/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/0.99  
% 1.99/0.99  ------ Combination Options
% 1.99/0.99  
% 1.99/0.99  --comb_res_mult                         3
% 1.99/0.99  --comb_sup_mult                         2
% 1.99/0.99  --comb_inst_mult                        10
% 1.99/0.99  
% 1.99/0.99  ------ Debug Options
% 1.99/0.99  
% 1.99/0.99  --dbg_backtrace                         false
% 1.99/0.99  --dbg_dump_prop_clauses                 false
% 1.99/0.99  --dbg_dump_prop_clauses_file            -
% 1.99/0.99  --dbg_out_stat                          false
% 1.99/0.99  ------ Parsing...
% 1.99/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... gs_s  sp: 3 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.99/0.99  ------ Proving...
% 1.99/0.99  ------ Problem Properties 
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  clauses                                 24
% 1.99/0.99  conjectures                             2
% 1.99/0.99  EPR                                     6
% 1.99/0.99  Horn                                    19
% 1.99/0.99  unary                                   7
% 1.99/0.99  binary                                  11
% 1.99/0.99  lits                                    47
% 1.99/0.99  lits eq                                 16
% 1.99/0.99  fd_pure                                 0
% 1.99/0.99  fd_pseudo                               0
% 1.99/0.99  fd_cond                                 1
% 1.99/0.99  fd_pseudo_cond                          2
% 1.99/0.99  AC symbols                              0
% 1.99/0.99  
% 1.99/0.99  ------ Schedule dynamic 5 is on 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.99/0.99  
% 1.99/0.99  
% 1.99/0.99  ------ 
% 1.99/0.99  Current options:
% 1.99/0.99  ------ 
% 1.99/0.99  
% 1.99/0.99  ------ Input Options
% 1.99/0.99  
% 1.99/0.99  --out_options                           all
% 1.99/0.99  --tptp_safe_out                         true
% 1.99/0.99  --problem_path                          ""
% 1.99/0.99  --include_path                          ""
% 1.99/0.99  --clausifier                            res/vclausify_rel
% 1.99/0.99  --clausifier_options                    --mode clausify
% 1.99/0.99  --stdin                                 false
% 1.99/0.99  --stats_out                             all
% 1.99/0.99  
% 1.99/0.99  ------ General Options
% 1.99/0.99  
% 1.99/0.99  --fof                                   false
% 1.99/0.99  --time_out_real                         305.
% 1.99/0.99  --time_out_virtual                      -1.
% 1.99/0.99  --symbol_type_check                     false
% 1.99/0.99  --clausify_out                          false
% 1.99/0.99  --sig_cnt_out                           false
% 1.99/0.99  --trig_cnt_out                          false
% 1.99/0.99  --trig_cnt_out_tolerance                1.
% 1.99/0.99  --trig_cnt_out_sk_spl                   false
% 1.99/0.99  --abstr_cl_out                          false
% 1.99/0.99  
% 1.99/0.99  ------ Global Options
% 1.99/0.99  
% 1.99/0.99  --schedule                              default
% 1.99/0.99  --add_important_lit                     false
% 1.99/0.99  --prop_solver_per_cl                    1000
% 1.99/0.99  --min_unsat_core                        false
% 1.99/0.99  --soft_assumptions                      false
% 1.99/0.99  --soft_lemma_size                       3
% 1.99/0.99  --prop_impl_unit_size                   0
% 1.99/0.99  --prop_impl_unit                        []
% 1.99/0.99  --share_sel_clauses                     true
% 1.99/0.99  --reset_solvers                         false
% 1.99/0.99  --bc_imp_inh                            [conj_cone]
% 1.99/0.99  --conj_cone_tolerance                   3.
% 1.99/0.99  --extra_neg_conj                        none
% 1.99/0.99  --large_theory_mode                     true
% 1.99/0.99  --prolific_symb_bound                   200
% 1.99/0.99  --lt_threshold                          2000
% 1.99/0.99  --clause_weak_htbl                      true
% 1.99/0.99  --gc_record_bc_elim                     false
% 1.99/0.99  
% 1.99/0.99  ------ Preprocessing Options
% 1.99/0.99  
% 1.99/0.99  --preprocessing_flag                    true
% 1.99/0.99  --time_out_prep_mult                    0.1
% 1.99/0.99  --splitting_mode                        input
% 1.99/0.99  --splitting_grd                         true
% 1.99/0.99  --splitting_cvd                         false
% 1.99/0.99  --splitting_cvd_svl                     false
% 1.99/0.99  --splitting_nvd                         32
% 1.99/0.99  --sub_typing                            true
% 1.99/0.99  --prep_gs_sim                           true
% 1.99/0.99  --prep_unflatten                        true
% 1.99/0.99  --prep_res_sim                          true
% 1.99/0.99  --prep_upred                            true
% 1.99/0.99  --prep_sem_filter                       exhaustive
% 1.99/0.99  --prep_sem_filter_out                   false
% 1.99/0.99  --pred_elim                             true
% 1.99/0.99  --res_sim_input                         true
% 1.99/0.99  --eq_ax_congr_red                       true
% 1.99/0.99  --pure_diseq_elim                       true
% 1.99/0.99  --brand_transform                       false
% 1.99/0.99  --non_eq_to_eq                          false
% 1.99/0.99  --prep_def_merge                        true
% 1.99/0.99  --prep_def_merge_prop_impl              false
% 1.99/0.99  --prep_def_merge_mbd                    true
% 1.99/0.99  --prep_def_merge_tr_red                 false
% 1.99/0.99  --prep_def_merge_tr_cl                  false
% 1.99/0.99  --smt_preprocessing                     true
% 1.99/0.99  --smt_ac_axioms                         fast
% 1.99/0.99  --preprocessed_out                      false
% 1.99/0.99  --preprocessed_stats                    false
% 1.99/0.99  
% 1.99/0.99  ------ Abstraction refinement Options
% 1.99/0.99  
% 1.99/0.99  --abstr_ref                             []
% 1.99/0.99  --abstr_ref_prep                        false
% 1.99/0.99  --abstr_ref_until_sat                   false
% 1.99/0.99  --abstr_ref_sig_restrict                funpre
% 1.99/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 1.99/0.99  --abstr_ref_under                       []
% 1.99/0.99  
% 1.99/0.99  ------ SAT Options
% 1.99/0.99  
% 1.99/0.99  --sat_mode                              false
% 1.99/0.99  --sat_fm_restart_options                ""
% 1.99/0.99  --sat_gr_def                            false
% 1.99/0.99  --sat_epr_types                         true
% 1.99/0.99  --sat_non_cyclic_types                  false
% 1.99/0.99  --sat_finite_models                     false
% 1.99/0.99  --sat_fm_lemmas                         false
% 1.99/0.99  --sat_fm_prep                           false
% 1.99/0.99  --sat_fm_uc_incr                        true
% 1.99/0.99  --sat_out_model                         small
% 1.99/0.99  --sat_out_clauses                       false
% 1.99/0.99  
% 1.99/0.99  ------ QBF Options
% 1.99/0.99  
% 1.99/0.99  --qbf_mode                              false
% 1.99/0.99  --qbf_elim_univ                         false
% 1.99/0.99  --qbf_dom_inst                          none
% 1.99/0.99  --qbf_dom_pre_inst                      false
% 1.99/0.99  --qbf_sk_in                             false
% 1.99/0.99  --qbf_pred_elim                         true
% 1.99/0.99  --qbf_split                             512
% 1.99/0.99  
% 1.99/0.99  ------ BMC1 Options
% 1.99/0.99  
% 1.99/0.99  --bmc1_incremental                      false
% 1.99/0.99  --bmc1_axioms                           reachable_all
% 1.99/0.99  --bmc1_min_bound                        0
% 1.99/0.99  --bmc1_max_bound                        -1
% 1.99/0.99  --bmc1_max_bound_default                -1
% 1.99/0.99  --bmc1_symbol_reachability              true
% 1.99/0.99  --bmc1_property_lemmas                  false
% 1.99/0.99  --bmc1_k_induction                      false
% 1.99/0.99  --bmc1_non_equiv_states                 false
% 1.99/0.99  --bmc1_deadlock                         false
% 1.99/0.99  --bmc1_ucm                              false
% 1.99/0.99  --bmc1_add_unsat_core                   none
% 1.99/0.99  --bmc1_unsat_core_children              false
% 1.99/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 1.99/0.99  --bmc1_out_stat                         full
% 1.99/0.99  --bmc1_ground_init                      false
% 1.99/0.99  --bmc1_pre_inst_next_state              false
% 1.99/0.99  --bmc1_pre_inst_state                   false
% 1.99/0.99  --bmc1_pre_inst_reach_state             false
% 1.99/0.99  --bmc1_out_unsat_core                   false
% 1.99/0.99  --bmc1_aig_witness_out                  false
% 1.99/0.99  --bmc1_verbose                          false
% 1.99/0.99  --bmc1_dump_clauses_tptp                false
% 1.99/0.99  --bmc1_dump_unsat_core_tptp             false
% 1.99/0.99  --bmc1_dump_file                        -
% 1.99/0.99  --bmc1_ucm_expand_uc_limit              128
% 1.99/0.99  --bmc1_ucm_n_expand_iterations          6
% 1.99/0.99  --bmc1_ucm_extend_mode                  1
% 1.99/0.99  --bmc1_ucm_init_mode                    2
% 1.99/0.99  --bmc1_ucm_cone_mode                    none
% 1.99/0.99  --bmc1_ucm_reduced_relation_type        0
% 1.99/0.99  --bmc1_ucm_relax_model                  4
% 1.99/0.99  --bmc1_ucm_full_tr_after_sat            true
% 1.99/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 1.99/0.99  --bmc1_ucm_layered_model                none
% 1.99/0.99  --bmc1_ucm_max_lemma_size               10
% 1.99/0.99  
% 1.99/0.99  ------ AIG Options
% 1.99/0.99  
% 1.99/0.99  --aig_mode                              false
% 1.99/0.99  
% 1.99/0.99  ------ Instantiation Options
% 1.99/0.99  
% 1.99/0.99  --instantiation_flag                    true
% 1.99/0.99  --inst_sos_flag                         false
% 1.99/0.99  --inst_sos_phase                        true
% 1.99/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.99/0.99  --inst_lit_sel_side                     none
% 1.99/0.99  --inst_solver_per_active                1400
% 1.99/0.99  --inst_solver_calls_frac                1.
% 1.99/0.99  --inst_passive_queue_type               priority_queues
% 1.99/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.99/1.00  --inst_passive_queues_freq              [25;2]
% 1.99/1.00  --inst_dismatching                      true
% 1.99/1.00  --inst_eager_unprocessed_to_passive     true
% 1.99/1.00  --inst_prop_sim_given                   true
% 1.99/1.00  --inst_prop_sim_new                     false
% 1.99/1.00  --inst_subs_new                         false
% 1.99/1.00  --inst_eq_res_simp                      false
% 1.99/1.00  --inst_subs_given                       false
% 1.99/1.00  --inst_orphan_elimination               true
% 1.99/1.00  --inst_learning_loop_flag               true
% 1.99/1.00  --inst_learning_start                   3000
% 1.99/1.00  --inst_learning_factor                  2
% 1.99/1.00  --inst_start_prop_sim_after_learn       3
% 1.99/1.00  --inst_sel_renew                        solver
% 1.99/1.00  --inst_lit_activity_flag                true
% 1.99/1.00  --inst_restr_to_given                   false
% 1.99/1.00  --inst_activity_threshold               500
% 1.99/1.00  --inst_out_proof                        true
% 1.99/1.00  
% 1.99/1.00  ------ Resolution Options
% 1.99/1.00  
% 1.99/1.00  --resolution_flag                       false
% 1.99/1.00  --res_lit_sel                           adaptive
% 1.99/1.00  --res_lit_sel_side                      none
% 1.99/1.00  --res_ordering                          kbo
% 1.99/1.00  --res_to_prop_solver                    active
% 1.99/1.00  --res_prop_simpl_new                    false
% 1.99/1.00  --res_prop_simpl_given                  true
% 1.99/1.00  --res_passive_queue_type                priority_queues
% 1.99/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.99/1.00  --res_passive_queues_freq               [15;5]
% 1.99/1.00  --res_forward_subs                      full
% 1.99/1.00  --res_backward_subs                     full
% 1.99/1.00  --res_forward_subs_resolution           true
% 1.99/1.00  --res_backward_subs_resolution          true
% 1.99/1.00  --res_orphan_elimination                true
% 1.99/1.00  --res_time_limit                        2.
% 1.99/1.00  --res_out_proof                         true
% 1.99/1.00  
% 1.99/1.00  ------ Superposition Options
% 1.99/1.00  
% 1.99/1.00  --superposition_flag                    true
% 1.99/1.00  --sup_passive_queue_type                priority_queues
% 1.99/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.99/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.99/1.00  --demod_completeness_check              fast
% 1.99/1.00  --demod_use_ground                      true
% 1.99/1.00  --sup_to_prop_solver                    passive
% 1.99/1.00  --sup_prop_simpl_new                    true
% 1.99/1.00  --sup_prop_simpl_given                  true
% 1.99/1.00  --sup_fun_splitting                     false
% 1.99/1.00  --sup_smt_interval                      50000
% 1.99/1.00  
% 1.99/1.00  ------ Superposition Simplification Setup
% 1.99/1.00  
% 1.99/1.00  --sup_indices_passive                   []
% 1.99/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.99/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.99/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_full_bw                           [BwDemod]
% 1.99/1.00  --sup_immed_triv                        [TrivRules]
% 1.99/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.99/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_immed_bw_main                     []
% 1.99/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.99/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.99/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.99/1.00  
% 1.99/1.00  ------ Combination Options
% 1.99/1.00  
% 1.99/1.00  --comb_res_mult                         3
% 1.99/1.00  --comb_sup_mult                         2
% 1.99/1.00  --comb_inst_mult                        10
% 1.99/1.00  
% 1.99/1.00  ------ Debug Options
% 1.99/1.00  
% 1.99/1.00  --dbg_backtrace                         false
% 1.99/1.00  --dbg_dump_prop_clauses                 false
% 1.99/1.00  --dbg_dump_prop_clauses_file            -
% 1.99/1.00  --dbg_out_stat                          false
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  ------ Proving...
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  % SZS status Theorem for theBenchmark.p
% 1.99/1.00  
% 1.99/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 1.99/1.00  
% 1.99/1.00  fof(f11,axiom,(
% 1.99/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f22,plain,(
% 1.99/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.99/1.00    inference(ennf_transformation,[],[f11])).
% 1.99/1.00  
% 1.99/1.00  fof(f44,plain,(
% 1.99/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.99/1.00    inference(nnf_transformation,[],[f22])).
% 1.99/1.00  
% 1.99/1.00  fof(f64,plain,(
% 1.99/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f44])).
% 1.99/1.00  
% 1.99/1.00  fof(f16,axiom,(
% 1.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f29,plain,(
% 1.99/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.00    inference(ennf_transformation,[],[f16])).
% 1.99/1.00  
% 1.99/1.00  fof(f71,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/1.00    inference(cnf_transformation,[],[f29])).
% 1.99/1.00  
% 1.99/1.00  fof(f19,conjecture,(
% 1.99/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f20,negated_conjecture,(
% 1.99/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => r2_hidden(k1_funct_1(X2,X0),X1)))),
% 1.99/1.00    inference(negated_conjecture,[],[f19])).
% 1.99/1.00  
% 1.99/1.00  fof(f33,plain,(
% 1.99/1.00    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.99/1.00    inference(ennf_transformation,[],[f20])).
% 1.99/1.00  
% 1.99/1.00  fof(f34,plain,(
% 1.99/1.00    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.99/1.00    inference(flattening,[],[f33])).
% 1.99/1.00  
% 1.99/1.00  fof(f46,plain,(
% 1.99/1.00    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),X1) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 1.99/1.00    introduced(choice_axiom,[])).
% 1.99/1.00  
% 1.99/1.00  fof(f47,plain,(
% 1.99/1.00    ~r2_hidden(k1_funct_1(sK3,sK1),sK2) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 1.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f34,f46])).
% 1.99/1.00  
% 1.99/1.00  fof(f77,plain,(
% 1.99/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.99/1.00    inference(cnf_transformation,[],[f47])).
% 1.99/1.00  
% 1.99/1.00  fof(f5,axiom,(
% 1.99/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f55,plain,(
% 1.99/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f5])).
% 1.99/1.00  
% 1.99/1.00  fof(f6,axiom,(
% 1.99/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f56,plain,(
% 1.99/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f6])).
% 1.99/1.00  
% 1.99/1.00  fof(f7,axiom,(
% 1.99/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f57,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f7])).
% 1.99/1.00  
% 1.99/1.00  fof(f80,plain,(
% 1.99/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.99/1.00    inference(definition_unfolding,[],[f56,f57])).
% 1.99/1.00  
% 1.99/1.00  fof(f81,plain,(
% 1.99/1.00    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.99/1.00    inference(definition_unfolding,[],[f55,f80])).
% 1.99/1.00  
% 1.99/1.00  fof(f88,plain,(
% 1.99/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 1.99/1.00    inference(definition_unfolding,[],[f77,f81])).
% 1.99/1.00  
% 1.99/1.00  fof(f15,axiom,(
% 1.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f28,plain,(
% 1.99/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.00    inference(ennf_transformation,[],[f15])).
% 1.99/1.00  
% 1.99/1.00  fof(f70,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/1.00    inference(cnf_transformation,[],[f28])).
% 1.99/1.00  
% 1.99/1.00  fof(f10,axiom,(
% 1.99/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f42,plain,(
% 1.99/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.99/1.00    inference(nnf_transformation,[],[f10])).
% 1.99/1.00  
% 1.99/1.00  fof(f43,plain,(
% 1.99/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.99/1.00    inference(flattening,[],[f42])).
% 1.99/1.00  
% 1.99/1.00  fof(f61,plain,(
% 1.99/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.99/1.00    inference(cnf_transformation,[],[f43])).
% 1.99/1.00  
% 1.99/1.00  fof(f87,plain,(
% 1.99/1.00    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.99/1.00    inference(definition_unfolding,[],[f61,f81,f81])).
% 1.99/1.00  
% 1.99/1.00  fof(f2,axiom,(
% 1.99/1.00    v1_xboole_0(k1_xboole_0)),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f50,plain,(
% 1.99/1.00    v1_xboole_0(k1_xboole_0)),
% 1.99/1.00    inference(cnf_transformation,[],[f2])).
% 1.99/1.00  
% 1.99/1.00  fof(f13,axiom,(
% 1.99/1.00    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f25,plain,(
% 1.99/1.00    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.99/1.00    inference(ennf_transformation,[],[f13])).
% 1.99/1.00  
% 1.99/1.00  fof(f45,plain,(
% 1.99/1.00    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.99/1.00    inference(nnf_transformation,[],[f25])).
% 1.99/1.00  
% 1.99/1.00  fof(f67,plain,(
% 1.99/1.00    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f45])).
% 1.99/1.00  
% 1.99/1.00  fof(f12,axiom,(
% 1.99/1.00    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f23,plain,(
% 1.99/1.00    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.99/1.00    inference(ennf_transformation,[],[f12])).
% 1.99/1.00  
% 1.99/1.00  fof(f24,plain,(
% 1.99/1.00    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.99/1.00    inference(flattening,[],[f23])).
% 1.99/1.00  
% 1.99/1.00  fof(f66,plain,(
% 1.99/1.00    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f24])).
% 1.99/1.00  
% 1.99/1.00  fof(f1,axiom,(
% 1.99/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f35,plain,(
% 1.99/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.99/1.00    inference(nnf_transformation,[],[f1])).
% 1.99/1.00  
% 1.99/1.00  fof(f36,plain,(
% 1.99/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.99/1.00    inference(rectify,[],[f35])).
% 1.99/1.00  
% 1.99/1.00  fof(f37,plain,(
% 1.99/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.99/1.00    introduced(choice_axiom,[])).
% 1.99/1.00  
% 1.99/1.00  fof(f38,plain,(
% 1.99/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.99/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f36,f37])).
% 1.99/1.00  
% 1.99/1.00  fof(f49,plain,(
% 1.99/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f18,axiom,(
% 1.99/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f31,plain,(
% 1.99/1.00    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.99/1.00    inference(ennf_transformation,[],[f18])).
% 1.99/1.00  
% 1.99/1.00  fof(f32,plain,(
% 1.99/1.00    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.99/1.00    inference(flattening,[],[f31])).
% 1.99/1.00  
% 1.99/1.00  fof(f74,plain,(
% 1.99/1.00    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f32])).
% 1.99/1.00  
% 1.99/1.00  fof(f76,plain,(
% 1.99/1.00    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 1.99/1.00    inference(cnf_transformation,[],[f47])).
% 1.99/1.00  
% 1.99/1.00  fof(f89,plain,(
% 1.99/1.00    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 1.99/1.00    inference(definition_unfolding,[],[f76,f81])).
% 1.99/1.00  
% 1.99/1.00  fof(f75,plain,(
% 1.99/1.00    v1_funct_1(sK3)),
% 1.99/1.00    inference(cnf_transformation,[],[f47])).
% 1.99/1.00  
% 1.99/1.00  fof(f78,plain,(
% 1.99/1.00    k1_xboole_0 != sK2),
% 1.99/1.00    inference(cnf_transformation,[],[f47])).
% 1.99/1.00  
% 1.99/1.00  fof(f17,axiom,(
% 1.99/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f30,plain,(
% 1.99/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.99/1.00    inference(ennf_transformation,[],[f17])).
% 1.99/1.00  
% 1.99/1.00  fof(f73,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/1.00    inference(cnf_transformation,[],[f30])).
% 1.99/1.00  
% 1.99/1.00  fof(f8,axiom,(
% 1.99/1.00    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f58,plain,(
% 1.99/1.00    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.99/1.00    inference(cnf_transformation,[],[f8])).
% 1.99/1.00  
% 1.99/1.00  fof(f82,plain,(
% 1.99/1.00    ( ! [X0] : (~v1_xboole_0(k2_enumset1(X0,X0,X0,X0))) )),
% 1.99/1.00    inference(definition_unfolding,[],[f58,f81])).
% 1.99/1.00  
% 1.99/1.00  fof(f48,plain,(
% 1.99/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f38])).
% 1.99/1.00  
% 1.99/1.00  fof(f4,axiom,(
% 1.99/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f39,plain,(
% 1.99/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/1.00    inference(nnf_transformation,[],[f4])).
% 1.99/1.00  
% 1.99/1.00  fof(f40,plain,(
% 1.99/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.99/1.00    inference(flattening,[],[f39])).
% 1.99/1.00  
% 1.99/1.00  fof(f52,plain,(
% 1.99/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.99/1.00    inference(cnf_transformation,[],[f40])).
% 1.99/1.00  
% 1.99/1.00  fof(f91,plain,(
% 1.99/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.99/1.00    inference(equality_resolution,[],[f52])).
% 1.99/1.00  
% 1.99/1.00  fof(f9,axiom,(
% 1.99/1.00    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f41,plain,(
% 1.99/1.00    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 1.99/1.00    inference(nnf_transformation,[],[f9])).
% 1.99/1.00  
% 1.99/1.00  fof(f59,plain,(
% 1.99/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f41])).
% 1.99/1.00  
% 1.99/1.00  fof(f84,plain,(
% 1.99/1.00    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.99/1.00    inference(definition_unfolding,[],[f59,f81])).
% 1.99/1.00  
% 1.99/1.00  fof(f14,axiom,(
% 1.99/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 1.99/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.99/1.00  
% 1.99/1.00  fof(f26,plain,(
% 1.99/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.99/1.00    inference(ennf_transformation,[],[f14])).
% 1.99/1.00  
% 1.99/1.00  fof(f27,plain,(
% 1.99/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.99/1.00    inference(flattening,[],[f26])).
% 1.99/1.00  
% 1.99/1.00  fof(f69,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.99/1.00    inference(cnf_transformation,[],[f27])).
% 1.99/1.00  
% 1.99/1.00  fof(f72,plain,(
% 1.99/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.99/1.00    inference(cnf_transformation,[],[f29])).
% 1.99/1.00  
% 1.99/1.00  fof(f79,plain,(
% 1.99/1.00    ~r2_hidden(k1_funct_1(sK3,sK1),sK2)),
% 1.99/1.00    inference(cnf_transformation,[],[f47])).
% 1.99/1.00  
% 1.99/1.00  cnf(c_14,plain,
% 1.99/1.00      ( ~ v4_relat_1(X0,X1)
% 1.99/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 1.99/1.00      | ~ v1_relat_1(X0) ),
% 1.99/1.00      inference(cnf_transformation,[],[f64]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_21,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | v4_relat_1(X0,X1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f71]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_26,negated_conjecture,
% 1.99/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 1.99/1.00      inference(cnf_transformation,[],[f88]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_443,plain,
% 1.99/1.00      ( v4_relat_1(X0,X1)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.99/1.00      | sK3 != X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_444,plain,
% 1.99/1.00      ( v4_relat_1(sK3,X0)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_443]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_498,plain,
% 1.99/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 1.99/1.00      | ~ v1_relat_1(X0)
% 1.99/1.00      | X2 != X1
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 1.99/1.00      | sK3 != X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_14,c_444]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_499,plain,
% 1.99/1.00      ( r1_tarski(k1_relat_1(sK3),X0)
% 1.99/1.00      | ~ v1_relat_1(sK3)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_498]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_19,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | v1_relat_1(X0) ),
% 1.99/1.00      inference(cnf_transformation,[],[f70]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_455,plain,
% 1.99/1.00      ( v1_relat_1(X0)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.99/1.00      | sK3 != X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_456,plain,
% 1.99/1.00      ( v1_relat_1(sK3)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_455]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_503,plain,
% 1.99/1.00      ( r1_tarski(k1_relat_1(sK3),X0)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_499,c_456]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1240,plain,
% 1.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.00      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_503]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1494,plain,
% 1.99/1.00      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 1.99/1.00      inference(equality_resolution,[status(thm)],[c_1240]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_12,plain,
% 1.99/1.00      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 1.99/1.00      | k2_enumset1(X1,X1,X1,X1) = X0
% 1.99/1.00      | k1_xboole_0 = X0 ),
% 1.99/1.00      inference(cnf_transformation,[],[f87]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1243,plain,
% 1.99/1.00      ( k2_enumset1(X0,X0,X0,X0) = X1
% 1.99/1.00      | k1_xboole_0 = X1
% 1.99/1.00      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2056,plain,
% 1.99/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 1.99/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.99/1.00      inference(superposition,[status(thm)],[c_1494,c_1243]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2,plain,
% 1.99/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 1.99/1.00      inference(cnf_transformation,[],[f50]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_94,plain,
% 1.99/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_17,plain,
% 1.99/1.00      ( ~ v1_relat_1(X0)
% 1.99/1.00      | k2_relat_1(X0) = k1_xboole_0
% 1.99/1.00      | k1_relat_1(X0) != k1_xboole_0 ),
% 1.99/1.00      inference(cnf_transformation,[],[f67]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_519,plain,
% 1.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.00      | k2_relat_1(X2) = k1_xboole_0
% 1.99/1.00      | k1_relat_1(X2) != k1_xboole_0
% 1.99/1.00      | sK3 != X2 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_456]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_520,plain,
% 1.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.00      | k2_relat_1(sK3) = k1_xboole_0
% 1.99/1.00      | k1_relat_1(sK3) != k1_xboole_0 ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_519]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_737,plain,
% 1.99/1.00      ( sP0_iProver_split
% 1.99/1.00      | k2_relat_1(sK3) = k1_xboole_0
% 1.99/1.00      | k1_relat_1(sK3) != k1_xboole_0 ),
% 1.99/1.00      inference(splitting,
% 1.99/1.00                [splitting(split),new_symbols(definition,[])],
% 1.99/1.00                [c_520]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_741,plain,
% 1.99/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 1.99/1.00      theory(equality) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1405,plain,
% 1.99/1.00      ( ~ v1_xboole_0(X0)
% 1.99/1.00      | v1_xboole_0(k2_relat_1(sK3))
% 1.99/1.00      | k2_relat_1(sK3) != X0 ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_741]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1406,plain,
% 1.99/1.00      ( k2_relat_1(sK3) != X0
% 1.99/1.00      | v1_xboole_0(X0) != iProver_top
% 1.99/1.00      | v1_xboole_0(k2_relat_1(sK3)) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_1405]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1408,plain,
% 1.99/1.00      ( k2_relat_1(sK3) != k1_xboole_0
% 1.99/1.00      | v1_xboole_0(k2_relat_1(sK3)) = iProver_top
% 1.99/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_1406]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_15,plain,
% 1.99/1.00      ( ~ v1_relat_1(X0)
% 1.99/1.00      | v1_xboole_0(X0)
% 1.99/1.00      | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 1.99/1.00      inference(cnf_transformation,[],[f66]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_543,plain,
% 1.99/1.00      ( v1_xboole_0(X0)
% 1.99/1.00      | ~ v1_xboole_0(k2_relat_1(X0))
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 1.99/1.00      | sK3 != X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_456]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_544,plain,
% 1.99/1.00      ( ~ v1_xboole_0(k2_relat_1(sK3))
% 1.99/1.00      | v1_xboole_0(sK3)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_543]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_734,plain,
% 1.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.00      | ~ sP0_iProver_split ),
% 1.99/1.00      inference(splitting,
% 1.99/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 1.99/1.00                [c_544]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1235,plain,
% 1.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.00      | sP0_iProver_split != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_734]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1457,plain,
% 1.99/1.00      ( sP0_iProver_split != iProver_top ),
% 1.99/1.00      inference(equality_resolution,[status(thm)],[c_1235]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1458,plain,
% 1.99/1.00      ( ~ sP0_iProver_split ),
% 1.99/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1457]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_0,plain,
% 1.99/1.00      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 1.99/1.00      inference(cnf_transformation,[],[f49]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1254,plain,
% 1.99/1.00      ( r2_hidden(sK0(X0),X0) = iProver_top
% 1.99/1.00      | v1_xboole_0(X0) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_23,plain,
% 1.99/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 1.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | ~ r2_hidden(X3,X1)
% 1.99/1.00      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 1.99/1.00      | ~ v1_funct_1(X0)
% 1.99/1.00      | k1_xboole_0 = X2 ),
% 1.99/1.00      inference(cnf_transformation,[],[f74]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_27,negated_conjecture,
% 1.99/1.00      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 1.99/1.00      inference(cnf_transformation,[],[f89]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_394,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | ~ r2_hidden(X3,X1)
% 1.99/1.00      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 1.99/1.00      | ~ v1_funct_1(X0)
% 1.99/1.00      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 1.99/1.00      | sK2 != X2
% 1.99/1.00      | sK3 != X0
% 1.99/1.00      | k1_xboole_0 = X2 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_395,plain,
% 1.99/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 1.99/1.00      | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 1.99/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
% 1.99/1.00      | ~ v1_funct_1(sK3)
% 1.99/1.00      | k1_xboole_0 = sK2 ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_394]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_28,negated_conjecture,
% 1.99/1.00      ( v1_funct_1(sK3) ),
% 1.99/1.00      inference(cnf_transformation,[],[f75]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_25,negated_conjecture,
% 1.99/1.00      ( k1_xboole_0 != sK2 ),
% 1.99/1.00      inference(cnf_transformation,[],[f78]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_399,plain,
% 1.99/1.00      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 1.99/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_395,c_28,c_26,c_25]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1241,plain,
% 1.99/1.00      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 1.99/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_22,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.99/1.00      inference(cnf_transformation,[],[f73]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_434,plain,
% 1.99/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.00      | sK3 != X2 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_435,plain,
% 1.99/1.00      ( k2_relset_1(X0,X1,sK3) = k2_relat_1(sK3)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_434]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1412,plain,
% 1.99/1.00      ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 1.99/1.00      inference(equality_resolution,[status(thm)],[c_435]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1448,plain,
% 1.99/1.00      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 1.99/1.00      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 1.99/1.00      inference(light_normalisation,[status(thm)],[c_1241,c_1412]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2064,plain,
% 1.99/1.00      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),k2_relat_1(sK3)) = iProver_top
% 1.99/1.00      | v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) = iProver_top ),
% 1.99/1.00      inference(superposition,[status(thm)],[c_1254,c_1448]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_7,plain,
% 1.99/1.00      ( ~ v1_xboole_0(k2_enumset1(X0,X0,X0,X0)) ),
% 1.99/1.00      inference(cnf_transformation,[],[f82]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1749,plain,
% 1.99/1.00      ( ~ v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) ),
% 1.99/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1750,plain,
% 1.99/1.00      ( v1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_1749]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2260,plain,
% 1.99/1.00      ( r2_hidden(k1_funct_1(sK3,sK0(k2_enumset1(sK1,sK1,sK1,sK1))),k2_relat_1(sK3)) = iProver_top ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_2064,c_1750]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1,plain,
% 1.99/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f48]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1253,plain,
% 1.99/1.00      ( r2_hidden(X0,X1) != iProver_top
% 1.99/1.00      | v1_xboole_0(X1) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2265,plain,
% 1.99/1.00      ( v1_xboole_0(k2_relat_1(sK3)) != iProver_top ),
% 1.99/1.00      inference(superposition,[status(thm)],[c_2260,c_1253]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2446,plain,
% 1.99/1.00      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3) ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_2056,c_94,c_737,c_1408,c_1458,c_2265]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_6,plain,
% 1.99/1.00      ( r1_tarski(X0,X0) ),
% 1.99/1.00      inference(cnf_transformation,[],[f91]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1249,plain,
% 1.99/1.00      ( r1_tarski(X0,X0) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_9,plain,
% 1.99/1.00      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | r2_hidden(X0,X1) ),
% 1.99/1.00      inference(cnf_transformation,[],[f84]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1246,plain,
% 1.99/1.00      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) != iProver_top
% 1.99/1.00      | r2_hidden(X0,X1) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2156,plain,
% 1.99/1.00      ( r2_hidden(X0,k2_enumset1(X0,X0,X0,X0)) = iProver_top ),
% 1.99/1.00      inference(superposition,[status(thm)],[c_1249,c_1246]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_2812,plain,
% 1.99/1.00      ( r2_hidden(sK1,k1_relat_1(sK3)) = iProver_top ),
% 1.99/1.00      inference(superposition,[status(thm)],[c_2446,c_2156]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_18,plain,
% 1.99/1.00      ( ~ v5_relat_1(X0,X1)
% 1.99/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 1.99/1.00      | r2_hidden(k1_funct_1(X0,X2),X1)
% 1.99/1.00      | ~ v1_funct_1(X0)
% 1.99/1.00      | ~ v1_relat_1(X0) ),
% 1.99/1.00      inference(cnf_transformation,[],[f69]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_20,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | v5_relat_1(X0,X2) ),
% 1.99/1.00      inference(cnf_transformation,[],[f72]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_365,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | ~ r2_hidden(X3,k1_relat_1(X4))
% 1.99/1.00      | r2_hidden(k1_funct_1(X4,X3),X5)
% 1.99/1.00      | ~ v1_funct_1(X4)
% 1.99/1.00      | ~ v1_relat_1(X4)
% 1.99/1.00      | X0 != X4
% 1.99/1.00      | X2 != X5 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_20]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_366,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 1.99/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.99/1.00      | ~ v1_funct_1(X0)
% 1.99/1.00      | ~ v1_relat_1(X0) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_365]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_370,plain,
% 1.99/1.00      ( ~ v1_funct_1(X0)
% 1.99/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.99/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 1.99/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.99/1.00      inference(global_propositional_subsumption,
% 1.99/1.00                [status(thm)],
% 1.99/1.00                [c_366,c_19]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_371,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 1.99/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.99/1.00      | ~ v1_funct_1(X0) ),
% 1.99/1.00      inference(renaming,[status(thm)],[c_370]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_415,plain,
% 1.99/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.99/1.00      | ~ r2_hidden(X3,k1_relat_1(X0))
% 1.99/1.00      | r2_hidden(k1_funct_1(X0,X3),X2)
% 1.99/1.00      | sK3 != X0 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_371,c_28]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_416,plain,
% 1.99/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.99/1.00      | ~ r2_hidden(X2,k1_relat_1(sK3))
% 1.99/1.00      | r2_hidden(k1_funct_1(sK3,X2),X1) ),
% 1.99/1.00      inference(unflattening,[status(thm)],[c_415]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_467,plain,
% 1.99/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.99/1.00      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1))
% 1.99/1.00      | sK3 != sK3 ),
% 1.99/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_416]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_587,plain,
% 1.99/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 1.99/1.00      | r2_hidden(k1_funct_1(sK3,X0),X1)
% 1.99/1.00      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X2,X1)) ),
% 1.99/1.00      inference(equality_resolution_simp,[status(thm)],[c_467]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1233,plain,
% 1.99/1.00      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 1.99/1.00      | r2_hidden(X2,k1_relat_1(sK3)) != iProver_top
% 1.99/1.00      | r2_hidden(k1_funct_1(sK3,X2),X1) = iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1500,plain,
% 1.99/1.00      ( r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 1.99/1.00      | r2_hidden(k1_funct_1(sK3,X0),sK2) = iProver_top ),
% 1.99/1.00      inference(equality_resolution,[status(thm)],[c_1233]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_24,negated_conjecture,
% 1.99/1.00      ( ~ r2_hidden(k1_funct_1(sK3,sK1),sK2) ),
% 1.99/1.00      inference(cnf_transformation,[],[f79]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1242,plain,
% 1.99/1.00      ( r2_hidden(k1_funct_1(sK3,sK1),sK2) != iProver_top ),
% 1.99/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(c_1885,plain,
% 1.99/1.00      ( r2_hidden(sK1,k1_relat_1(sK3)) != iProver_top ),
% 1.99/1.00      inference(superposition,[status(thm)],[c_1500,c_1242]) ).
% 1.99/1.00  
% 1.99/1.00  cnf(contradiction,plain,
% 1.99/1.00      ( $false ),
% 1.99/1.00      inference(minisat,[status(thm)],[c_2812,c_1885]) ).
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 1.99/1.00  
% 1.99/1.00  ------                               Statistics
% 1.99/1.00  
% 1.99/1.00  ------ General
% 1.99/1.00  
% 1.99/1.00  abstr_ref_over_cycles:                  0
% 1.99/1.00  abstr_ref_under_cycles:                 0
% 1.99/1.00  gc_basic_clause_elim:                   0
% 1.99/1.00  forced_gc_time:                         0
% 1.99/1.00  parsing_time:                           0.009
% 1.99/1.00  unif_index_cands_time:                  0.
% 1.99/1.00  unif_index_add_time:                    0.
% 1.99/1.00  orderings_time:                         0.
% 1.99/1.00  out_proof_time:                         0.019
% 1.99/1.00  total_time:                             0.135
% 1.99/1.00  num_of_symbols:                         53
% 1.99/1.00  num_of_terms:                           2229
% 1.99/1.00  
% 1.99/1.00  ------ Preprocessing
% 1.99/1.00  
% 1.99/1.00  num_of_splits:                          3
% 1.99/1.00  num_of_split_atoms:                     1
% 1.99/1.00  num_of_reused_defs:                     2
% 1.99/1.00  num_eq_ax_congr_red:                    13
% 1.99/1.00  num_of_sem_filtered_clauses:            1
% 1.99/1.00  num_of_subtypes:                        0
% 1.99/1.00  monotx_restored_types:                  0
% 1.99/1.00  sat_num_of_epr_types:                   0
% 1.99/1.00  sat_num_of_non_cyclic_types:            0
% 1.99/1.00  sat_guarded_non_collapsed_types:        0
% 1.99/1.00  num_pure_diseq_elim:                    0
% 1.99/1.00  simp_replaced_by:                       0
% 1.99/1.00  res_preprocessed:                       118
% 1.99/1.00  prep_upred:                             0
% 1.99/1.00  prep_unflattend:                        14
% 1.99/1.00  smt_new_axioms:                         0
% 1.99/1.00  pred_elim_cands:                        3
% 1.99/1.00  pred_elim:                              6
% 1.99/1.00  pred_elim_cl:                           7
% 1.99/1.00  pred_elim_cycles:                       8
% 1.99/1.00  merged_defs:                            8
% 1.99/1.00  merged_defs_ncl:                        0
% 1.99/1.00  bin_hyper_res:                          8
% 1.99/1.00  prep_cycles:                            4
% 1.99/1.00  pred_elim_time:                         0.018
% 1.99/1.00  splitting_time:                         0.
% 1.99/1.00  sem_filter_time:                        0.
% 1.99/1.00  monotx_time:                            0.
% 1.99/1.00  subtype_inf_time:                       0.
% 1.99/1.00  
% 1.99/1.00  ------ Problem properties
% 1.99/1.00  
% 1.99/1.00  clauses:                                24
% 1.99/1.00  conjectures:                            2
% 1.99/1.00  epr:                                    6
% 1.99/1.00  horn:                                   19
% 1.99/1.00  ground:                                 6
% 1.99/1.00  unary:                                  7
% 1.99/1.00  binary:                                 11
% 1.99/1.00  lits:                                   47
% 1.99/1.00  lits_eq:                                16
% 1.99/1.00  fd_pure:                                0
% 1.99/1.00  fd_pseudo:                              0
% 1.99/1.00  fd_cond:                                1
% 1.99/1.00  fd_pseudo_cond:                         2
% 1.99/1.00  ac_symbols:                             0
% 1.99/1.00  
% 1.99/1.00  ------ Propositional Solver
% 1.99/1.00  
% 1.99/1.00  prop_solver_calls:                      27
% 1.99/1.00  prop_fast_solver_calls:                 639
% 1.99/1.00  smt_solver_calls:                       0
% 1.99/1.00  smt_fast_solver_calls:                  0
% 1.99/1.00  prop_num_of_clauses:                    904
% 1.99/1.00  prop_preprocess_simplified:             4071
% 1.99/1.00  prop_fo_subsumed:                       11
% 1.99/1.00  prop_solver_time:                       0.
% 1.99/1.00  smt_solver_time:                        0.
% 1.99/1.00  smt_fast_solver_time:                   0.
% 1.99/1.00  prop_fast_solver_time:                  0.
% 1.99/1.00  prop_unsat_core_time:                   0.
% 1.99/1.00  
% 1.99/1.00  ------ QBF
% 1.99/1.00  
% 1.99/1.00  qbf_q_res:                              0
% 1.99/1.00  qbf_num_tautologies:                    0
% 1.99/1.00  qbf_prep_cycles:                        0
% 1.99/1.00  
% 1.99/1.00  ------ BMC1
% 1.99/1.00  
% 1.99/1.00  bmc1_current_bound:                     -1
% 1.99/1.00  bmc1_last_solved_bound:                 -1
% 1.99/1.00  bmc1_unsat_core_size:                   -1
% 1.99/1.00  bmc1_unsat_core_parents_size:           -1
% 1.99/1.00  bmc1_merge_next_fun:                    0
% 1.99/1.00  bmc1_unsat_core_clauses_time:           0.
% 1.99/1.00  
% 1.99/1.00  ------ Instantiation
% 1.99/1.00  
% 1.99/1.00  inst_num_of_clauses:                    286
% 1.99/1.00  inst_num_in_passive:                    83
% 1.99/1.00  inst_num_in_active:                     150
% 1.99/1.00  inst_num_in_unprocessed:                53
% 1.99/1.00  inst_num_of_loops:                      170
% 1.99/1.00  inst_num_of_learning_restarts:          0
% 1.99/1.00  inst_num_moves_active_passive:          17
% 1.99/1.00  inst_lit_activity:                      0
% 1.99/1.00  inst_lit_activity_moves:                0
% 1.99/1.00  inst_num_tautologies:                   0
% 1.99/1.00  inst_num_prop_implied:                  0
% 1.99/1.00  inst_num_existing_simplified:           0
% 1.99/1.00  inst_num_eq_res_simplified:             0
% 1.99/1.00  inst_num_child_elim:                    0
% 1.99/1.00  inst_num_of_dismatching_blockings:      32
% 1.99/1.00  inst_num_of_non_proper_insts:           266
% 1.99/1.00  inst_num_of_duplicates:                 0
% 1.99/1.00  inst_inst_num_from_inst_to_res:         0
% 1.99/1.00  inst_dismatching_checking_time:         0.
% 1.99/1.00  
% 1.99/1.00  ------ Resolution
% 1.99/1.00  
% 1.99/1.00  res_num_of_clauses:                     0
% 1.99/1.00  res_num_in_passive:                     0
% 1.99/1.00  res_num_in_active:                      0
% 1.99/1.00  res_num_of_loops:                       122
% 1.99/1.00  res_forward_subset_subsumed:            68
% 1.99/1.00  res_backward_subset_subsumed:           0
% 1.99/1.00  res_forward_subsumed:                   0
% 1.99/1.00  res_backward_subsumed:                  0
% 1.99/1.00  res_forward_subsumption_resolution:     0
% 1.99/1.00  res_backward_subsumption_resolution:    0
% 1.99/1.00  res_clause_to_clause_subsumption:       74
% 1.99/1.00  res_orphan_elimination:                 0
% 1.99/1.00  res_tautology_del:                      31
% 1.99/1.00  res_num_eq_res_simplified:              1
% 1.99/1.00  res_num_sel_changes:                    0
% 1.99/1.00  res_moves_from_active_to_pass:          0
% 1.99/1.00  
% 1.99/1.00  ------ Superposition
% 1.99/1.00  
% 1.99/1.00  sup_time_total:                         0.
% 1.99/1.00  sup_time_generating:                    0.
% 1.99/1.00  sup_time_sim_full:                      0.
% 1.99/1.00  sup_time_sim_immed:                     0.
% 1.99/1.00  
% 1.99/1.00  sup_num_of_clauses:                     36
% 1.99/1.00  sup_num_in_active:                      25
% 1.99/1.00  sup_num_in_passive:                     11
% 1.99/1.00  sup_num_of_loops:                       33
% 1.99/1.00  sup_fw_superposition:                   8
% 1.99/1.00  sup_bw_superposition:                   12
% 1.99/1.00  sup_immediate_simplified:               4
% 1.99/1.00  sup_given_eliminated:                   0
% 1.99/1.00  comparisons_done:                       0
% 1.99/1.00  comparisons_avoided:                    0
% 1.99/1.00  
% 1.99/1.00  ------ Simplifications
% 1.99/1.00  
% 1.99/1.00  
% 1.99/1.00  sim_fw_subset_subsumed:                 2
% 1.99/1.00  sim_bw_subset_subsumed:                 1
% 1.99/1.00  sim_fw_subsumed:                        2
% 1.99/1.00  sim_bw_subsumed:                        0
% 1.99/1.00  sim_fw_subsumption_res:                 0
% 1.99/1.00  sim_bw_subsumption_res:                 0
% 1.99/1.00  sim_tautology_del:                      2
% 1.99/1.00  sim_eq_tautology_del:                   3
% 1.99/1.00  sim_eq_res_simp:                        0
% 1.99/1.00  sim_fw_demodulated:                     1
% 1.99/1.00  sim_bw_demodulated:                     8
% 1.99/1.00  sim_light_normalised:                   1
% 1.99/1.00  sim_joinable_taut:                      0
% 1.99/1.00  sim_joinable_simp:                      0
% 1.99/1.00  sim_ac_normalised:                      0
% 1.99/1.00  sim_smt_subsumption:                    0
% 1.99/1.00  
%------------------------------------------------------------------------------
