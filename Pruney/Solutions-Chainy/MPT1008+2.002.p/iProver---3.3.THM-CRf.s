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
% DateTime   : Thu Dec  3 12:05:04 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 578 expanded)
%              Number of clauses        :   70 ( 127 expanded)
%              Number of leaves         :   22 ( 148 expanded)
%              Depth                    :   19
%              Number of atoms          :  352 (1409 expanded)
%              Number of equality atoms :  167 ( 716 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f40])).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f41])).

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

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f45,plain,
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

fof(f46,plain,
    ( k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)
    & k1_xboole_0 != sK2
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))
    & v1_funct_2(sK3,k1_tarski(sK1),sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f45])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f76])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f73,f77])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f72,plain,(
    v1_funct_2(sK3,k1_tarski(sK1),sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f84,plain,(
    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(definition_unfolding,[],[f72,f77])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f74,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f7,axiom,(
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
    inference(nnf_transformation,[],[f7])).

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

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f77,f77])).

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

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(definition_unfolding,[],[f75,f77,f77])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f65,f77,f77])).

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

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f60,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_962,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK0(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_955,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_956,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1508,plain,
    ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_955,c_956])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_269,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK1,sK1,sK1,sK1) != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_270,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
    | ~ v1_funct_1(sK3)
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_269])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_22,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_274,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_270,c_25,c_23,c_22])).

cnf(c_954,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_274])).

cnf(c_1516,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1508,c_954])).

cnf(c_10,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_328,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_9])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_332,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_328,c_17])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_332])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(X3,X3,X3,X3) != X1
    | k2_enumset1(X3,X3,X3,X3) = X4
    | k1_relat_1(X0) != X4
    | k1_xboole_0 = X4 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_333])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)))
    | k2_enumset1(X1,X1,X1,X1) = k1_relat_1(X0)
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_950,plain,
    ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X1)
    | k1_xboole_0 = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_494])).

cnf(c_1587,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_955,c_950])).

cnf(c_21,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1085,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1099,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
    | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_681,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1093,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != X0
    | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
    | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_1140,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
    | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3)
    | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1093])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_290,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_25])).

cnf(c_291,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_290])).

cnf(c_1168,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
    | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_291])).

cnf(c_1789,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1587,c_23,c_21,c_1085,c_1099,c_1140,c_1168])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_958,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1800,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1789,c_958])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1086,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1085])).

cnf(c_1803,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1800,c_28,c_1086])).

cnf(c_1900,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
    | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1516,c_10,c_1803])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_466,plain,
    ( ~ r2_hidden(X0,X1)
    | X0 != X2
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_16])).

cnf(c_467,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_952,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_1903,plain,
    ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1900,c_952])).

cnf(c_1907,plain,
    ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_962,c_1903])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_14,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_260,plain,
    ( v1_funct_1(X0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_14])).

cnf(c_261,plain,
    ( v1_funct_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_260])).

cnf(c_305,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_261])).

cnf(c_306,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(k1_xboole_0)
    | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_305])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(k1_xboole_0)
    | k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3)) = k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_306])).

cnf(c_378,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_enumset1(X2,X2,X2,X2) != k1_relat_1(k1_xboole_0)
    | k2_enumset1(k1_funct_1(k1_xboole_0,X2),k1_funct_1(k1_xboole_0,X2),k1_funct_1(k1_xboole_0,X2),k1_funct_1(k1_xboole_0,X2)) = k2_relat_1(k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_388,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(k1_xboole_0)
    | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_378,c_6])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1017,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
    | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_388,c_10,c_11])).

cnf(c_1998,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1907,c_1017])).

cnf(c_1517,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_1508,c_21])).

cnf(c_1808,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) != k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_1803,c_1517])).

cnf(c_1816,plain,
    ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_1808,c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_1998,c_1816])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:01:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.91/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.00  
% 1.91/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.91/1.00  
% 1.91/1.00  ------  iProver source info
% 1.91/1.00  
% 1.91/1.00  git: date: 2020-06-30 10:37:57 +0100
% 1.91/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.91/1.00  git: non_committed_changes: false
% 1.91/1.00  git: last_make_outside_of_git: false
% 1.91/1.00  
% 1.91/1.00  ------ 
% 1.91/1.00  
% 1.91/1.00  ------ Input Options
% 1.91/1.00  
% 1.91/1.00  --out_options                           all
% 1.91/1.00  --tptp_safe_out                         true
% 1.91/1.00  --problem_path                          ""
% 1.91/1.00  --include_path                          ""
% 1.91/1.00  --clausifier                            res/vclausify_rel
% 1.91/1.00  --clausifier_options                    --mode clausify
% 1.91/1.00  --stdin                                 false
% 1.91/1.00  --stats_out                             all
% 1.91/1.00  
% 1.91/1.00  ------ General Options
% 1.91/1.00  
% 1.91/1.00  --fof                                   false
% 1.91/1.00  --time_out_real                         305.
% 1.91/1.00  --time_out_virtual                      -1.
% 1.91/1.00  --symbol_type_check                     false
% 1.91/1.00  --clausify_out                          false
% 1.91/1.00  --sig_cnt_out                           false
% 1.91/1.00  --trig_cnt_out                          false
% 1.91/1.00  --trig_cnt_out_tolerance                1.
% 1.91/1.00  --trig_cnt_out_sk_spl                   false
% 1.91/1.00  --abstr_cl_out                          false
% 1.91/1.00  
% 1.91/1.00  ------ Global Options
% 1.91/1.00  
% 1.91/1.00  --schedule                              default
% 1.91/1.00  --add_important_lit                     false
% 1.91/1.00  --prop_solver_per_cl                    1000
% 1.91/1.00  --min_unsat_core                        false
% 1.91/1.00  --soft_assumptions                      false
% 1.91/1.00  --soft_lemma_size                       3
% 1.91/1.00  --prop_impl_unit_size                   0
% 1.91/1.00  --prop_impl_unit                        []
% 1.91/1.00  --share_sel_clauses                     true
% 1.91/1.00  --reset_solvers                         false
% 1.91/1.00  --bc_imp_inh                            [conj_cone]
% 1.91/1.00  --conj_cone_tolerance                   3.
% 1.91/1.00  --extra_neg_conj                        none
% 1.91/1.00  --large_theory_mode                     true
% 1.91/1.00  --prolific_symb_bound                   200
% 1.91/1.00  --lt_threshold                          2000
% 1.91/1.00  --clause_weak_htbl                      true
% 1.91/1.00  --gc_record_bc_elim                     false
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing Options
% 1.91/1.00  
% 1.91/1.00  --preprocessing_flag                    true
% 1.91/1.00  --time_out_prep_mult                    0.1
% 1.91/1.00  --splitting_mode                        input
% 1.91/1.00  --splitting_grd                         true
% 1.91/1.00  --splitting_cvd                         false
% 1.91/1.00  --splitting_cvd_svl                     false
% 1.91/1.00  --splitting_nvd                         32
% 1.91/1.00  --sub_typing                            true
% 1.91/1.00  --prep_gs_sim                           true
% 1.91/1.00  --prep_unflatten                        true
% 1.91/1.00  --prep_res_sim                          true
% 1.91/1.00  --prep_upred                            true
% 1.91/1.00  --prep_sem_filter                       exhaustive
% 1.91/1.00  --prep_sem_filter_out                   false
% 1.91/1.00  --pred_elim                             true
% 1.91/1.00  --res_sim_input                         true
% 1.91/1.00  --eq_ax_congr_red                       true
% 1.91/1.00  --pure_diseq_elim                       true
% 1.91/1.00  --brand_transform                       false
% 1.91/1.00  --non_eq_to_eq                          false
% 1.91/1.00  --prep_def_merge                        true
% 1.91/1.00  --prep_def_merge_prop_impl              false
% 1.91/1.00  --prep_def_merge_mbd                    true
% 1.91/1.00  --prep_def_merge_tr_red                 false
% 1.91/1.00  --prep_def_merge_tr_cl                  false
% 1.91/1.00  --smt_preprocessing                     true
% 1.91/1.00  --smt_ac_axioms                         fast
% 1.91/1.00  --preprocessed_out                      false
% 1.91/1.00  --preprocessed_stats                    false
% 1.91/1.00  
% 1.91/1.00  ------ Abstraction refinement Options
% 1.91/1.00  
% 1.91/1.00  --abstr_ref                             []
% 1.91/1.00  --abstr_ref_prep                        false
% 1.91/1.00  --abstr_ref_until_sat                   false
% 1.91/1.00  --abstr_ref_sig_restrict                funpre
% 1.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/1.00  --abstr_ref_under                       []
% 1.91/1.00  
% 1.91/1.00  ------ SAT Options
% 1.91/1.00  
% 1.91/1.00  --sat_mode                              false
% 1.91/1.00  --sat_fm_restart_options                ""
% 1.91/1.00  --sat_gr_def                            false
% 1.91/1.00  --sat_epr_types                         true
% 1.91/1.00  --sat_non_cyclic_types                  false
% 1.91/1.00  --sat_finite_models                     false
% 1.91/1.00  --sat_fm_lemmas                         false
% 1.91/1.00  --sat_fm_prep                           false
% 1.91/1.00  --sat_fm_uc_incr                        true
% 1.91/1.00  --sat_out_model                         small
% 1.91/1.00  --sat_out_clauses                       false
% 1.91/1.00  
% 1.91/1.00  ------ QBF Options
% 1.91/1.00  
% 1.91/1.00  --qbf_mode                              false
% 1.91/1.00  --qbf_elim_univ                         false
% 1.91/1.00  --qbf_dom_inst                          none
% 1.91/1.00  --qbf_dom_pre_inst                      false
% 1.91/1.00  --qbf_sk_in                             false
% 1.91/1.00  --qbf_pred_elim                         true
% 1.91/1.00  --qbf_split                             512
% 1.91/1.00  
% 1.91/1.00  ------ BMC1 Options
% 1.91/1.00  
% 1.91/1.00  --bmc1_incremental                      false
% 1.91/1.00  --bmc1_axioms                           reachable_all
% 1.91/1.00  --bmc1_min_bound                        0
% 1.91/1.00  --bmc1_max_bound                        -1
% 1.91/1.00  --bmc1_max_bound_default                -1
% 1.91/1.00  --bmc1_symbol_reachability              true
% 1.91/1.00  --bmc1_property_lemmas                  false
% 1.91/1.00  --bmc1_k_induction                      false
% 1.91/1.00  --bmc1_non_equiv_states                 false
% 1.91/1.00  --bmc1_deadlock                         false
% 1.91/1.00  --bmc1_ucm                              false
% 1.91/1.00  --bmc1_add_unsat_core                   none
% 1.91/1.00  --bmc1_unsat_core_children              false
% 1.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/1.00  --bmc1_out_stat                         full
% 1.91/1.00  --bmc1_ground_init                      false
% 1.91/1.00  --bmc1_pre_inst_next_state              false
% 1.91/1.00  --bmc1_pre_inst_state                   false
% 1.91/1.00  --bmc1_pre_inst_reach_state             false
% 1.91/1.00  --bmc1_out_unsat_core                   false
% 1.91/1.00  --bmc1_aig_witness_out                  false
% 1.91/1.00  --bmc1_verbose                          false
% 1.91/1.00  --bmc1_dump_clauses_tptp                false
% 1.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.91/1.00  --bmc1_dump_file                        -
% 1.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.91/1.00  --bmc1_ucm_extend_mode                  1
% 1.91/1.00  --bmc1_ucm_init_mode                    2
% 1.91/1.00  --bmc1_ucm_cone_mode                    none
% 1.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.91/1.00  --bmc1_ucm_relax_model                  4
% 1.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/1.00  --bmc1_ucm_layered_model                none
% 1.91/1.00  --bmc1_ucm_max_lemma_size               10
% 1.91/1.00  
% 1.91/1.00  ------ AIG Options
% 1.91/1.00  
% 1.91/1.00  --aig_mode                              false
% 1.91/1.00  
% 1.91/1.00  ------ Instantiation Options
% 1.91/1.00  
% 1.91/1.00  --instantiation_flag                    true
% 1.91/1.00  --inst_sos_flag                         false
% 1.91/1.00  --inst_sos_phase                        true
% 1.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/1.00  --inst_lit_sel_side                     num_symb
% 1.91/1.00  --inst_solver_per_active                1400
% 1.91/1.00  --inst_solver_calls_frac                1.
% 1.91/1.00  --inst_passive_queue_type               priority_queues
% 1.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/1.00  --inst_passive_queues_freq              [25;2]
% 1.91/1.00  --inst_dismatching                      true
% 1.91/1.00  --inst_eager_unprocessed_to_passive     true
% 1.91/1.00  --inst_prop_sim_given                   true
% 1.91/1.00  --inst_prop_sim_new                     false
% 1.91/1.00  --inst_subs_new                         false
% 1.91/1.00  --inst_eq_res_simp                      false
% 1.91/1.00  --inst_subs_given                       false
% 1.91/1.00  --inst_orphan_elimination               true
% 1.91/1.00  --inst_learning_loop_flag               true
% 1.91/1.00  --inst_learning_start                   3000
% 1.91/1.00  --inst_learning_factor                  2
% 1.91/1.00  --inst_start_prop_sim_after_learn       3
% 1.91/1.00  --inst_sel_renew                        solver
% 1.91/1.00  --inst_lit_activity_flag                true
% 1.91/1.00  --inst_restr_to_given                   false
% 1.91/1.00  --inst_activity_threshold               500
% 1.91/1.00  --inst_out_proof                        true
% 1.91/1.00  
% 1.91/1.00  ------ Resolution Options
% 1.91/1.00  
% 1.91/1.00  --resolution_flag                       true
% 1.91/1.00  --res_lit_sel                           adaptive
% 1.91/1.00  --res_lit_sel_side                      none
% 1.91/1.00  --res_ordering                          kbo
% 1.91/1.00  --res_to_prop_solver                    active
% 1.91/1.00  --res_prop_simpl_new                    false
% 1.91/1.00  --res_prop_simpl_given                  true
% 1.91/1.00  --res_passive_queue_type                priority_queues
% 1.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/1.00  --res_passive_queues_freq               [15;5]
% 1.91/1.00  --res_forward_subs                      full
% 1.91/1.00  --res_backward_subs                     full
% 1.91/1.00  --res_forward_subs_resolution           true
% 1.91/1.00  --res_backward_subs_resolution          true
% 1.91/1.00  --res_orphan_elimination                true
% 1.91/1.00  --res_time_limit                        2.
% 1.91/1.00  --res_out_proof                         true
% 1.91/1.00  
% 1.91/1.00  ------ Superposition Options
% 1.91/1.00  
% 1.91/1.00  --superposition_flag                    true
% 1.91/1.00  --sup_passive_queue_type                priority_queues
% 1.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.91/1.00  --demod_completeness_check              fast
% 1.91/1.00  --demod_use_ground                      true
% 1.91/1.00  --sup_to_prop_solver                    passive
% 1.91/1.00  --sup_prop_simpl_new                    true
% 1.91/1.00  --sup_prop_simpl_given                  true
% 1.91/1.00  --sup_fun_splitting                     false
% 1.91/1.00  --sup_smt_interval                      50000
% 1.91/1.00  
% 1.91/1.00  ------ Superposition Simplification Setup
% 1.91/1.00  
% 1.91/1.00  --sup_indices_passive                   []
% 1.91/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_full_bw                           [BwDemod]
% 1.91/1.00  --sup_immed_triv                        [TrivRules]
% 1.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_immed_bw_main                     []
% 1.91/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.00  
% 1.91/1.00  ------ Combination Options
% 1.91/1.00  
% 1.91/1.00  --comb_res_mult                         3
% 1.91/1.00  --comb_sup_mult                         2
% 1.91/1.00  --comb_inst_mult                        10
% 1.91/1.00  
% 1.91/1.00  ------ Debug Options
% 1.91/1.00  
% 1.91/1.00  --dbg_backtrace                         false
% 1.91/1.00  --dbg_dump_prop_clauses                 false
% 1.91/1.00  --dbg_dump_prop_clauses_file            -
% 1.91/1.00  --dbg_out_stat                          false
% 1.91/1.00  ------ Parsing...
% 1.91/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.91/1.00  ------ Proving...
% 1.91/1.00  ------ Problem Properties 
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  clauses                                 19
% 1.91/1.00  conjectures                             3
% 1.91/1.00  EPR                                     2
% 1.91/1.00  Horn                                    17
% 1.91/1.00  unary                                   8
% 1.91/1.00  binary                                  6
% 1.91/1.00  lits                                    35
% 1.91/1.00  lits eq                                 16
% 1.91/1.00  fd_pure                                 0
% 1.91/1.00  fd_pseudo                               0
% 1.91/1.00  fd_cond                                 3
% 1.91/1.00  fd_pseudo_cond                          0
% 1.91/1.00  AC symbols                              0
% 1.91/1.00  
% 1.91/1.00  ------ Schedule dynamic 5 is on 
% 1.91/1.00  
% 1.91/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.91/1.00  
% 1.91/1.00  
% 1.91/1.00  ------ 
% 1.91/1.00  Current options:
% 1.91/1.00  ------ 
% 1.91/1.00  
% 1.91/1.00  ------ Input Options
% 1.91/1.00  
% 1.91/1.00  --out_options                           all
% 1.91/1.00  --tptp_safe_out                         true
% 1.91/1.00  --problem_path                          ""
% 1.91/1.00  --include_path                          ""
% 1.91/1.00  --clausifier                            res/vclausify_rel
% 1.91/1.00  --clausifier_options                    --mode clausify
% 1.91/1.00  --stdin                                 false
% 1.91/1.00  --stats_out                             all
% 1.91/1.00  
% 1.91/1.00  ------ General Options
% 1.91/1.00  
% 1.91/1.00  --fof                                   false
% 1.91/1.00  --time_out_real                         305.
% 1.91/1.00  --time_out_virtual                      -1.
% 1.91/1.00  --symbol_type_check                     false
% 1.91/1.00  --clausify_out                          false
% 1.91/1.00  --sig_cnt_out                           false
% 1.91/1.00  --trig_cnt_out                          false
% 1.91/1.00  --trig_cnt_out_tolerance                1.
% 1.91/1.00  --trig_cnt_out_sk_spl                   false
% 1.91/1.00  --abstr_cl_out                          false
% 1.91/1.00  
% 1.91/1.00  ------ Global Options
% 1.91/1.00  
% 1.91/1.00  --schedule                              default
% 1.91/1.00  --add_important_lit                     false
% 1.91/1.00  --prop_solver_per_cl                    1000
% 1.91/1.00  --min_unsat_core                        false
% 1.91/1.00  --soft_assumptions                      false
% 1.91/1.00  --soft_lemma_size                       3
% 1.91/1.00  --prop_impl_unit_size                   0
% 1.91/1.00  --prop_impl_unit                        []
% 1.91/1.00  --share_sel_clauses                     true
% 1.91/1.00  --reset_solvers                         false
% 1.91/1.00  --bc_imp_inh                            [conj_cone]
% 1.91/1.00  --conj_cone_tolerance                   3.
% 1.91/1.00  --extra_neg_conj                        none
% 1.91/1.00  --large_theory_mode                     true
% 1.91/1.00  --prolific_symb_bound                   200
% 1.91/1.00  --lt_threshold                          2000
% 1.91/1.00  --clause_weak_htbl                      true
% 1.91/1.00  --gc_record_bc_elim                     false
% 1.91/1.00  
% 1.91/1.00  ------ Preprocessing Options
% 1.91/1.00  
% 1.91/1.00  --preprocessing_flag                    true
% 1.91/1.00  --time_out_prep_mult                    0.1
% 1.91/1.00  --splitting_mode                        input
% 1.91/1.00  --splitting_grd                         true
% 1.91/1.00  --splitting_cvd                         false
% 1.91/1.00  --splitting_cvd_svl                     false
% 1.91/1.00  --splitting_nvd                         32
% 1.91/1.00  --sub_typing                            true
% 1.91/1.00  --prep_gs_sim                           true
% 1.91/1.00  --prep_unflatten                        true
% 1.91/1.00  --prep_res_sim                          true
% 1.91/1.00  --prep_upred                            true
% 1.91/1.00  --prep_sem_filter                       exhaustive
% 1.91/1.00  --prep_sem_filter_out                   false
% 1.91/1.00  --pred_elim                             true
% 1.91/1.00  --res_sim_input                         true
% 1.91/1.00  --eq_ax_congr_red                       true
% 1.91/1.00  --pure_diseq_elim                       true
% 1.91/1.00  --brand_transform                       false
% 1.91/1.00  --non_eq_to_eq                          false
% 1.91/1.00  --prep_def_merge                        true
% 1.91/1.00  --prep_def_merge_prop_impl              false
% 1.91/1.00  --prep_def_merge_mbd                    true
% 1.91/1.00  --prep_def_merge_tr_red                 false
% 1.91/1.00  --prep_def_merge_tr_cl                  false
% 1.91/1.00  --smt_preprocessing                     true
% 1.91/1.00  --smt_ac_axioms                         fast
% 1.91/1.00  --preprocessed_out                      false
% 1.91/1.00  --preprocessed_stats                    false
% 1.91/1.00  
% 1.91/1.00  ------ Abstraction refinement Options
% 1.91/1.00  
% 1.91/1.00  --abstr_ref                             []
% 1.91/1.00  --abstr_ref_prep                        false
% 1.91/1.00  --abstr_ref_until_sat                   false
% 1.91/1.00  --abstr_ref_sig_restrict                funpre
% 1.91/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 1.91/1.00  --abstr_ref_under                       []
% 1.91/1.00  
% 1.91/1.00  ------ SAT Options
% 1.91/1.00  
% 1.91/1.00  --sat_mode                              false
% 1.91/1.00  --sat_fm_restart_options                ""
% 1.91/1.00  --sat_gr_def                            false
% 1.91/1.00  --sat_epr_types                         true
% 1.91/1.00  --sat_non_cyclic_types                  false
% 1.91/1.00  --sat_finite_models                     false
% 1.91/1.00  --sat_fm_lemmas                         false
% 1.91/1.00  --sat_fm_prep                           false
% 1.91/1.00  --sat_fm_uc_incr                        true
% 1.91/1.00  --sat_out_model                         small
% 1.91/1.00  --sat_out_clauses                       false
% 1.91/1.00  
% 1.91/1.00  ------ QBF Options
% 1.91/1.00  
% 1.91/1.00  --qbf_mode                              false
% 1.91/1.00  --qbf_elim_univ                         false
% 1.91/1.00  --qbf_dom_inst                          none
% 1.91/1.00  --qbf_dom_pre_inst                      false
% 1.91/1.00  --qbf_sk_in                             false
% 1.91/1.00  --qbf_pred_elim                         true
% 1.91/1.00  --qbf_split                             512
% 1.91/1.00  
% 1.91/1.00  ------ BMC1 Options
% 1.91/1.00  
% 1.91/1.00  --bmc1_incremental                      false
% 1.91/1.00  --bmc1_axioms                           reachable_all
% 1.91/1.00  --bmc1_min_bound                        0
% 1.91/1.00  --bmc1_max_bound                        -1
% 1.91/1.00  --bmc1_max_bound_default                -1
% 1.91/1.00  --bmc1_symbol_reachability              true
% 1.91/1.00  --bmc1_property_lemmas                  false
% 1.91/1.00  --bmc1_k_induction                      false
% 1.91/1.00  --bmc1_non_equiv_states                 false
% 1.91/1.00  --bmc1_deadlock                         false
% 1.91/1.00  --bmc1_ucm                              false
% 1.91/1.00  --bmc1_add_unsat_core                   none
% 1.91/1.00  --bmc1_unsat_core_children              false
% 1.91/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 1.91/1.00  --bmc1_out_stat                         full
% 1.91/1.00  --bmc1_ground_init                      false
% 1.91/1.00  --bmc1_pre_inst_next_state              false
% 1.91/1.00  --bmc1_pre_inst_state                   false
% 1.91/1.00  --bmc1_pre_inst_reach_state             false
% 1.91/1.00  --bmc1_out_unsat_core                   false
% 1.91/1.00  --bmc1_aig_witness_out                  false
% 1.91/1.00  --bmc1_verbose                          false
% 1.91/1.00  --bmc1_dump_clauses_tptp                false
% 1.91/1.00  --bmc1_dump_unsat_core_tptp             false
% 1.91/1.00  --bmc1_dump_file                        -
% 1.91/1.00  --bmc1_ucm_expand_uc_limit              128
% 1.91/1.00  --bmc1_ucm_n_expand_iterations          6
% 1.91/1.00  --bmc1_ucm_extend_mode                  1
% 1.91/1.00  --bmc1_ucm_init_mode                    2
% 1.91/1.00  --bmc1_ucm_cone_mode                    none
% 1.91/1.00  --bmc1_ucm_reduced_relation_type        0
% 1.91/1.00  --bmc1_ucm_relax_model                  4
% 1.91/1.00  --bmc1_ucm_full_tr_after_sat            true
% 1.91/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 1.91/1.00  --bmc1_ucm_layered_model                none
% 1.91/1.00  --bmc1_ucm_max_lemma_size               10
% 1.91/1.00  
% 1.91/1.00  ------ AIG Options
% 1.91/1.00  
% 1.91/1.00  --aig_mode                              false
% 1.91/1.00  
% 1.91/1.00  ------ Instantiation Options
% 1.91/1.00  
% 1.91/1.00  --instantiation_flag                    true
% 1.91/1.00  --inst_sos_flag                         false
% 1.91/1.00  --inst_sos_phase                        true
% 1.91/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.91/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.91/1.00  --inst_lit_sel_side                     none
% 1.91/1.00  --inst_solver_per_active                1400
% 1.91/1.00  --inst_solver_calls_frac                1.
% 1.91/1.00  --inst_passive_queue_type               priority_queues
% 1.91/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.91/1.00  --inst_passive_queues_freq              [25;2]
% 1.91/1.00  --inst_dismatching                      true
% 1.91/1.00  --inst_eager_unprocessed_to_passive     true
% 1.91/1.00  --inst_prop_sim_given                   true
% 1.91/1.00  --inst_prop_sim_new                     false
% 1.91/1.00  --inst_subs_new                         false
% 1.91/1.00  --inst_eq_res_simp                      false
% 1.91/1.00  --inst_subs_given                       false
% 1.91/1.00  --inst_orphan_elimination               true
% 1.91/1.00  --inst_learning_loop_flag               true
% 1.91/1.00  --inst_learning_start                   3000
% 1.91/1.00  --inst_learning_factor                  2
% 1.91/1.00  --inst_start_prop_sim_after_learn       3
% 1.91/1.00  --inst_sel_renew                        solver
% 1.91/1.00  --inst_lit_activity_flag                true
% 1.91/1.00  --inst_restr_to_given                   false
% 1.91/1.00  --inst_activity_threshold               500
% 1.91/1.00  --inst_out_proof                        true
% 1.91/1.00  
% 1.91/1.00  ------ Resolution Options
% 1.91/1.00  
% 1.91/1.00  --resolution_flag                       false
% 1.91/1.00  --res_lit_sel                           adaptive
% 1.91/1.00  --res_lit_sel_side                      none
% 1.91/1.00  --res_ordering                          kbo
% 1.91/1.00  --res_to_prop_solver                    active
% 1.91/1.00  --res_prop_simpl_new                    false
% 1.91/1.00  --res_prop_simpl_given                  true
% 1.91/1.00  --res_passive_queue_type                priority_queues
% 1.91/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.91/1.00  --res_passive_queues_freq               [15;5]
% 1.91/1.00  --res_forward_subs                      full
% 1.91/1.00  --res_backward_subs                     full
% 1.91/1.00  --res_forward_subs_resolution           true
% 1.91/1.00  --res_backward_subs_resolution          true
% 1.91/1.00  --res_orphan_elimination                true
% 1.91/1.00  --res_time_limit                        2.
% 1.91/1.00  --res_out_proof                         true
% 1.91/1.00  
% 1.91/1.00  ------ Superposition Options
% 1.91/1.00  
% 1.91/1.00  --superposition_flag                    true
% 1.91/1.00  --sup_passive_queue_type                priority_queues
% 1.91/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.91/1.00  --sup_passive_queues_freq               [8;1;4]
% 1.91/1.00  --demod_completeness_check              fast
% 1.91/1.00  --demod_use_ground                      true
% 1.91/1.00  --sup_to_prop_solver                    passive
% 1.91/1.00  --sup_prop_simpl_new                    true
% 1.91/1.00  --sup_prop_simpl_given                  true
% 1.91/1.00  --sup_fun_splitting                     false
% 1.91/1.00  --sup_smt_interval                      50000
% 1.91/1.00  
% 1.91/1.00  ------ Superposition Simplification Setup
% 1.91/1.00  
% 1.91/1.00  --sup_indices_passive                   []
% 1.91/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.91/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 1.91/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.00  --sup_full_bw                           [BwDemod]
% 1.91/1.00  --sup_immed_triv                        [TrivRules]
% 1.91/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.91/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.01  --sup_immed_bw_main                     []
% 1.91/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 1.91/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.91/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.91/1.01  
% 1.91/1.01  ------ Combination Options
% 1.91/1.01  
% 1.91/1.01  --comb_res_mult                         3
% 1.91/1.01  --comb_sup_mult                         2
% 1.91/1.01  --comb_inst_mult                        10
% 1.91/1.01  
% 1.91/1.01  ------ Debug Options
% 1.91/1.01  
% 1.91/1.01  --dbg_backtrace                         false
% 1.91/1.01  --dbg_dump_prop_clauses                 false
% 1.91/1.01  --dbg_dump_prop_clauses_file            -
% 1.91/1.01  --dbg_out_stat                          false
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  ------ Proving...
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  % SZS status Theorem for theBenchmark.p
% 1.91/1.01  
% 1.91/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 1.91/1.01  
% 1.91/1.01  fof(f2,axiom,(
% 1.91/1.01    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f23,plain,(
% 1.91/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.91/1.01    inference(ennf_transformation,[],[f2])).
% 1.91/1.01  
% 1.91/1.01  fof(f40,plain,(
% 1.91/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.91/1.01    introduced(choice_axiom,[])).
% 1.91/1.01  
% 1.91/1.01  fof(f41,plain,(
% 1.91/1.01    ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0)),
% 1.91/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f40])).
% 1.91/1.01  
% 1.91/1.01  fof(f48,plain,(
% 1.91/1.01    ( ! [X0] : (r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0) )),
% 1.91/1.01    inference(cnf_transformation,[],[f41])).
% 1.91/1.01  
% 1.91/1.01  fof(f20,conjecture,(
% 1.91/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f21,negated_conjecture,(
% 1.91/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 1.91/1.01    inference(negated_conjecture,[],[f20])).
% 1.91/1.01  
% 1.91/1.01  fof(f38,plain,(
% 1.91/1.01    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 1.91/1.01    inference(ennf_transformation,[],[f21])).
% 1.91/1.01  
% 1.91/1.01  fof(f39,plain,(
% 1.91/1.01    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 1.91/1.01    inference(flattening,[],[f38])).
% 1.91/1.01  
% 1.91/1.01  fof(f45,plain,(
% 1.91/1.01    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3))),
% 1.91/1.01    introduced(choice_axiom,[])).
% 1.91/1.01  
% 1.91/1.01  fof(f46,plain,(
% 1.91/1.01    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3) & k1_xboole_0 != sK2 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2))) & v1_funct_2(sK3,k1_tarski(sK1),sK2) & v1_funct_1(sK3)),
% 1.91/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f45])).
% 1.91/1.01  
% 1.91/1.01  fof(f73,plain,(
% 1.91/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 1.91/1.01    inference(cnf_transformation,[],[f46])).
% 1.91/1.01  
% 1.91/1.01  fof(f4,axiom,(
% 1.91/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f50,plain,(
% 1.91/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f4])).
% 1.91/1.01  
% 1.91/1.01  fof(f5,axiom,(
% 1.91/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f51,plain,(
% 1.91/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f5])).
% 1.91/1.01  
% 1.91/1.01  fof(f6,axiom,(
% 1.91/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f52,plain,(
% 1.91/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f6])).
% 1.91/1.01  
% 1.91/1.01  fof(f76,plain,(
% 1.91/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.91/1.01    inference(definition_unfolding,[],[f51,f52])).
% 1.91/1.01  
% 1.91/1.01  fof(f77,plain,(
% 1.91/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.91/1.01    inference(definition_unfolding,[],[f50,f76])).
% 1.91/1.01  
% 1.91/1.01  fof(f83,plain,(
% 1.91/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))),
% 1.91/1.01    inference(definition_unfolding,[],[f73,f77])).
% 1.91/1.01  
% 1.91/1.01  fof(f18,axiom,(
% 1.91/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f35,plain,(
% 1.91/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/1.01    inference(ennf_transformation,[],[f18])).
% 1.91/1.01  
% 1.91/1.01  fof(f69,plain,(
% 1.91/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/1.01    inference(cnf_transformation,[],[f35])).
% 1.91/1.01  
% 1.91/1.01  fof(f19,axiom,(
% 1.91/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f36,plain,(
% 1.91/1.01    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.91/1.01    inference(ennf_transformation,[],[f19])).
% 1.91/1.01  
% 1.91/1.01  fof(f37,plain,(
% 1.91/1.01    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.91/1.01    inference(flattening,[],[f36])).
% 1.91/1.01  
% 1.91/1.01  fof(f70,plain,(
% 1.91/1.01    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f37])).
% 1.91/1.01  
% 1.91/1.01  fof(f72,plain,(
% 1.91/1.01    v1_funct_2(sK3,k1_tarski(sK1),sK2)),
% 1.91/1.01    inference(cnf_transformation,[],[f46])).
% 1.91/1.01  
% 1.91/1.01  fof(f84,plain,(
% 1.91/1.01    v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2)),
% 1.91/1.01    inference(definition_unfolding,[],[f72,f77])).
% 1.91/1.01  
% 1.91/1.01  fof(f71,plain,(
% 1.91/1.01    v1_funct_1(sK3)),
% 1.91/1.01    inference(cnf_transformation,[],[f46])).
% 1.91/1.01  
% 1.91/1.01  fof(f74,plain,(
% 1.91/1.01    k1_xboole_0 != sK2),
% 1.91/1.01    inference(cnf_transformation,[],[f46])).
% 1.91/1.01  
% 1.91/1.01  fof(f11,axiom,(
% 1.91/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f61,plain,(
% 1.91/1.01    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.91/1.01    inference(cnf_transformation,[],[f11])).
% 1.91/1.01  
% 1.91/1.01  fof(f7,axiom,(
% 1.91/1.01    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f42,plain,(
% 1.91/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.91/1.01    inference(nnf_transformation,[],[f7])).
% 1.91/1.01  
% 1.91/1.01  fof(f43,plain,(
% 1.91/1.01    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.91/1.01    inference(flattening,[],[f42])).
% 1.91/1.01  
% 1.91/1.01  fof(f53,plain,(
% 1.91/1.01    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.91/1.01    inference(cnf_transformation,[],[f43])).
% 1.91/1.01  
% 1.91/1.01  fof(f80,plain,(
% 1.91/1.01    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.91/1.01    inference(definition_unfolding,[],[f53,f77,f77])).
% 1.91/1.01  
% 1.91/1.01  fof(f17,axiom,(
% 1.91/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f22,plain,(
% 1.91/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.91/1.01    inference(pure_predicate_removal,[],[f17])).
% 1.91/1.01  
% 1.91/1.01  fof(f34,plain,(
% 1.91/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/1.01    inference(ennf_transformation,[],[f22])).
% 1.91/1.01  
% 1.91/1.01  fof(f68,plain,(
% 1.91/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/1.01    inference(cnf_transformation,[],[f34])).
% 1.91/1.01  
% 1.91/1.01  fof(f10,axiom,(
% 1.91/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f26,plain,(
% 1.91/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.91/1.01    inference(ennf_transformation,[],[f10])).
% 1.91/1.01  
% 1.91/1.01  fof(f44,plain,(
% 1.91/1.01    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.91/1.01    inference(nnf_transformation,[],[f26])).
% 1.91/1.01  
% 1.91/1.01  fof(f58,plain,(
% 1.91/1.01    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f44])).
% 1.91/1.01  
% 1.91/1.01  fof(f16,axiom,(
% 1.91/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f33,plain,(
% 1.91/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.91/1.01    inference(ennf_transformation,[],[f16])).
% 1.91/1.01  
% 1.91/1.01  fof(f67,plain,(
% 1.91/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.91/1.01    inference(cnf_transformation,[],[f33])).
% 1.91/1.01  
% 1.91/1.01  fof(f75,plain,(
% 1.91/1.01    k1_tarski(k1_funct_1(sK3,sK1)) != k2_relset_1(k1_tarski(sK1),sK2,sK3)),
% 1.91/1.01    inference(cnf_transformation,[],[f46])).
% 1.91/1.01  
% 1.91/1.01  fof(f82,plain,(
% 1.91/1.01    k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)),
% 1.91/1.01    inference(definition_unfolding,[],[f75,f77,f77])).
% 1.91/1.01  
% 1.91/1.01  fof(f14,axiom,(
% 1.91/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f30,plain,(
% 1.91/1.01    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.91/1.01    inference(ennf_transformation,[],[f14])).
% 1.91/1.01  
% 1.91/1.01  fof(f31,plain,(
% 1.91/1.01    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.91/1.01    inference(flattening,[],[f30])).
% 1.91/1.01  
% 1.91/1.01  fof(f65,plain,(
% 1.91/1.01    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f31])).
% 1.91/1.01  
% 1.91/1.01  fof(f81,plain,(
% 1.91/1.01    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.91/1.01    inference(definition_unfolding,[],[f65,f77,f77])).
% 1.91/1.01  
% 1.91/1.01  fof(f12,axiom,(
% 1.91/1.01    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f27,plain,(
% 1.91/1.01    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.91/1.01    inference(ennf_transformation,[],[f12])).
% 1.91/1.01  
% 1.91/1.01  fof(f28,plain,(
% 1.91/1.01    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.91/1.01    inference(flattening,[],[f27])).
% 1.91/1.01  
% 1.91/1.01  fof(f62,plain,(
% 1.91/1.01    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f28])).
% 1.91/1.01  
% 1.91/1.01  fof(f3,axiom,(
% 1.91/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f49,plain,(
% 1.91/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f3])).
% 1.91/1.01  
% 1.91/1.01  fof(f15,axiom,(
% 1.91/1.01    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f32,plain,(
% 1.91/1.01    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.91/1.01    inference(ennf_transformation,[],[f15])).
% 1.91/1.01  
% 1.91/1.01  fof(f66,plain,(
% 1.91/1.01    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f32])).
% 1.91/1.01  
% 1.91/1.01  fof(f1,axiom,(
% 1.91/1.01    v1_xboole_0(k1_xboole_0)),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f47,plain,(
% 1.91/1.01    v1_xboole_0(k1_xboole_0)),
% 1.91/1.01    inference(cnf_transformation,[],[f1])).
% 1.91/1.01  
% 1.91/1.01  fof(f13,axiom,(
% 1.91/1.01    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f29,plain,(
% 1.91/1.01    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 1.91/1.01    inference(ennf_transformation,[],[f13])).
% 1.91/1.01  
% 1.91/1.01  fof(f64,plain,(
% 1.91/1.01    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 1.91/1.01    inference(cnf_transformation,[],[f29])).
% 1.91/1.01  
% 1.91/1.01  fof(f8,axiom,(
% 1.91/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.91/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.91/1.01  
% 1.91/1.01  fof(f56,plain,(
% 1.91/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.91/1.01    inference(cnf_transformation,[],[f8])).
% 1.91/1.01  
% 1.91/1.01  fof(f60,plain,(
% 1.91/1.01    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.91/1.01    inference(cnf_transformation,[],[f11])).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1,plain,
% 1.91/1.01      ( r2_hidden(sK0(X0),X0) | k1_xboole_0 = X0 ),
% 1.91/1.01      inference(cnf_transformation,[],[f48]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_962,plain,
% 1.91/1.01      ( k1_xboole_0 = X0 | r2_hidden(sK0(X0),X0) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_23,negated_conjecture,
% 1.91/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) ),
% 1.91/1.01      inference(cnf_transformation,[],[f83]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_955,plain,
% 1.91/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_19,plain,
% 1.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f69]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_956,plain,
% 1.91/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.91/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1508,plain,
% 1.91/1.01      ( k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_955,c_956]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_20,plain,
% 1.91/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/1.01      | ~ r2_hidden(X3,X1)
% 1.91/1.01      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 1.91/1.01      | ~ v1_funct_1(X0)
% 1.91/1.01      | k1_xboole_0 = X2 ),
% 1.91/1.01      inference(cnf_transformation,[],[f70]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_24,negated_conjecture,
% 1.91/1.01      ( v1_funct_2(sK3,k2_enumset1(sK1,sK1,sK1,sK1),sK2) ),
% 1.91/1.01      inference(cnf_transformation,[],[f84]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_269,plain,
% 1.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/1.01      | ~ r2_hidden(X3,X1)
% 1.91/1.01      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 1.91/1.01      | ~ v1_funct_1(X0)
% 1.91/1.01      | k2_enumset1(sK1,sK1,sK1,sK1) != X1
% 1.91/1.01      | sK2 != X2
% 1.91/1.01      | sK3 != X0
% 1.91/1.01      | k1_xboole_0 = X2 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_270,plain,
% 1.91/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 1.91/1.01      | ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 1.91/1.01      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3))
% 1.91/1.01      | ~ v1_funct_1(sK3)
% 1.91/1.01      | k1_xboole_0 = sK2 ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_269]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_25,negated_conjecture,
% 1.91/1.01      ( v1_funct_1(sK3) ),
% 1.91/1.01      inference(cnf_transformation,[],[f71]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_22,negated_conjecture,
% 1.91/1.01      ( k1_xboole_0 != sK2 ),
% 1.91/1.01      inference(cnf_transformation,[],[f74]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_274,plain,
% 1.91/1.01      ( ~ r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1))
% 1.91/1.01      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) ),
% 1.91/1.01      inference(global_propositional_subsumption,
% 1.91/1.01                [status(thm)],
% 1.91/1.01                [c_270,c_25,c_23,c_22]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_954,plain,
% 1.91/1.01      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 1.91/1.01      | r2_hidden(k1_funct_1(sK3,X0),k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_274]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1516,plain,
% 1.91/1.01      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 1.91/1.01      | r2_hidden(k1_funct_1(sK3,X0),k2_relat_1(sK3)) = iProver_top ),
% 1.91/1.01      inference(demodulation,[status(thm)],[c_1508,c_954]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_10,plain,
% 1.91/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.91/1.01      inference(cnf_transformation,[],[f61]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_5,plain,
% 1.91/1.01      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 1.91/1.01      | k2_enumset1(X1,X1,X1,X1) = X0
% 1.91/1.01      | k1_xboole_0 = X0 ),
% 1.91/1.01      inference(cnf_transformation,[],[f80]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_18,plain,
% 1.91/1.01      ( v4_relat_1(X0,X1)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.91/1.01      inference(cnf_transformation,[],[f68]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_9,plain,
% 1.91/1.01      ( ~ v4_relat_1(X0,X1)
% 1.91/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 1.91/1.01      | ~ v1_relat_1(X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f58]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_328,plain,
% 1.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/1.01      | r1_tarski(k1_relat_1(X0),X1)
% 1.91/1.01      | ~ v1_relat_1(X0) ),
% 1.91/1.01      inference(resolution,[status(thm)],[c_18,c_9]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_17,plain,
% 1.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/1.01      | v1_relat_1(X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f67]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_332,plain,
% 1.91/1.01      ( r1_tarski(k1_relat_1(X0),X1)
% 1.91/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.91/1.01      inference(global_propositional_subsumption,
% 1.91/1.01                [status(thm)],
% 1.91/1.01                [c_328,c_17]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_333,plain,
% 1.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/1.01      | r1_tarski(k1_relat_1(X0),X1) ),
% 1.91/1.01      inference(renaming,[status(thm)],[c_332]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_493,plain,
% 1.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/1.01      | k2_enumset1(X3,X3,X3,X3) != X1
% 1.91/1.01      | k2_enumset1(X3,X3,X3,X3) = X4
% 1.91/1.01      | k1_relat_1(X0) != X4
% 1.91/1.01      | k1_xboole_0 = X4 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_333]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_494,plain,
% 1.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X1,X1,X1,X1),X2)))
% 1.91/1.01      | k2_enumset1(X1,X1,X1,X1) = k1_relat_1(X0)
% 1.91/1.01      | k1_xboole_0 = k1_relat_1(X0) ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_493]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_950,plain,
% 1.91/1.01      ( k2_enumset1(X0,X0,X0,X0) = k1_relat_1(X1)
% 1.91/1.01      | k1_xboole_0 = k1_relat_1(X1)
% 1.91/1.01      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(X0,X0,X0,X0),X2))) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_494]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1587,plain,
% 1.91/1.01      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_relat_1(sK3)
% 1.91/1.01      | k1_relat_1(sK3) = k1_xboole_0 ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_955,c_950]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_21,negated_conjecture,
% 1.91/1.01      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) ),
% 1.91/1.01      inference(cnf_transformation,[],[f82]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1085,plain,
% 1.91/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 1.91/1.01      | v1_relat_1(sK3) ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1099,plain,
% 1.91/1.01      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2)))
% 1.91/1.01      | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) = k2_relat_1(sK3) ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_19]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_681,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1093,plain,
% 1.91/1.01      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != X0
% 1.91/1.01      | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
% 1.91/1.01      | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != X0 ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_681]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1140,plain,
% 1.91/1.01      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3)
% 1.91/1.01      | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3)
% 1.91/1.01      | k2_relset_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2,sK3) != k2_relat_1(sK3) ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_1093]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_15,plain,
% 1.91/1.01      ( ~ v1_funct_1(X0)
% 1.91/1.01      | ~ v1_relat_1(X0)
% 1.91/1.01      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 1.91/1.01      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f81]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_290,plain,
% 1.91/1.01      ( ~ v1_relat_1(X0)
% 1.91/1.01      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 1.91/1.01      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 1.91/1.01      | sK3 != X0 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_25]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_291,plain,
% 1.91/1.01      ( ~ v1_relat_1(sK3)
% 1.91/1.01      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 1.91/1.01      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_290]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1168,plain,
% 1.91/1.01      ( ~ v1_relat_1(sK3)
% 1.91/1.01      | k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) = k2_relat_1(sK3)
% 1.91/1.01      | k2_enumset1(sK1,sK1,sK1,sK1) != k1_relat_1(sK3) ),
% 1.91/1.01      inference(instantiation,[status(thm)],[c_291]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1789,plain,
% 1.91/1.01      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 1.91/1.01      inference(global_propositional_subsumption,
% 1.91/1.01                [status(thm)],
% 1.91/1.01                [c_1587,c_23,c_21,c_1085,c_1099,c_1140,c_1168]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_13,plain,
% 1.91/1.01      ( ~ v1_relat_1(X0)
% 1.91/1.01      | k1_relat_1(X0) != k1_xboole_0
% 1.91/1.01      | k1_xboole_0 = X0 ),
% 1.91/1.01      inference(cnf_transformation,[],[f62]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_958,plain,
% 1.91/1.01      ( k1_relat_1(X0) != k1_xboole_0
% 1.91/1.01      | k1_xboole_0 = X0
% 1.91/1.01      | v1_relat_1(X0) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1800,plain,
% 1.91/1.01      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_1789,c_958]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_28,plain,
% 1.91/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1086,plain,
% 1.91/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK1,sK1,sK1,sK1),sK2))) != iProver_top
% 1.91/1.01      | v1_relat_1(sK3) = iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_1085]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1803,plain,
% 1.91/1.01      ( sK3 = k1_xboole_0 ),
% 1.91/1.01      inference(global_propositional_subsumption,
% 1.91/1.01                [status(thm)],
% 1.91/1.01                [c_1800,c_28,c_1086]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1900,plain,
% 1.91/1.01      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top
% 1.91/1.01      | r2_hidden(k1_funct_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 1.91/1.01      inference(light_normalisation,[status(thm)],[c_1516,c_10,c_1803]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_2,plain,
% 1.91/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f49]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_16,plain,
% 1.91/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f66]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_466,plain,
% 1.91/1.01      ( ~ r2_hidden(X0,X1) | X0 != X2 | k1_xboole_0 != X1 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_2,c_16]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_467,plain,
% 1.91/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_466]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_952,plain,
% 1.91/1.01      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 1.91/1.01      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1903,plain,
% 1.91/1.01      ( r2_hidden(X0,k2_enumset1(sK1,sK1,sK1,sK1)) != iProver_top ),
% 1.91/1.01      inference(forward_subsumption_resolution,
% 1.91/1.01                [status(thm)],
% 1.91/1.01                [c_1900,c_952]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1907,plain,
% 1.91/1.01      ( k2_enumset1(sK1,sK1,sK1,sK1) = k1_xboole_0 ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_962,c_1903]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_0,plain,
% 1.91/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f47]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_14,plain,
% 1.91/1.01      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 1.91/1.01      inference(cnf_transformation,[],[f64]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_260,plain,
% 1.91/1.01      ( v1_funct_1(X0) | k1_xboole_0 != X0 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_14]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_261,plain,
% 1.91/1.01      ( v1_funct_1(k1_xboole_0) ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_260]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_305,plain,
% 1.91/1.01      ( ~ v1_relat_1(X0)
% 1.91/1.01      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 1.91/1.01      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 1.91/1.01      | k1_xboole_0 != X0 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_261]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_306,plain,
% 1.91/1.01      ( ~ v1_relat_1(k1_xboole_0)
% 1.91/1.01      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(k1_xboole_0)
% 1.91/1.01      | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_305]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_377,plain,
% 1.91/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.91/1.01      | k2_enumset1(X3,X3,X3,X3) != k1_relat_1(k1_xboole_0)
% 1.91/1.01      | k2_enumset1(k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3),k1_funct_1(k1_xboole_0,X3)) = k2_relat_1(k1_xboole_0)
% 1.91/1.01      | k1_xboole_0 != X0 ),
% 1.91/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_306]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_378,plain,
% 1.91/1.01      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.91/1.01      | k2_enumset1(X2,X2,X2,X2) != k1_relat_1(k1_xboole_0)
% 1.91/1.01      | k2_enumset1(k1_funct_1(k1_xboole_0,X2),k1_funct_1(k1_xboole_0,X2),k1_funct_1(k1_xboole_0,X2),k1_funct_1(k1_xboole_0,X2)) = k2_relat_1(k1_xboole_0) ),
% 1.91/1.01      inference(unflattening,[status(thm)],[c_377]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_6,plain,
% 1.91/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 1.91/1.01      inference(cnf_transformation,[],[f56]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_388,plain,
% 1.91/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(k1_xboole_0)
% 1.91/1.01      | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k2_relat_1(k1_xboole_0) ),
% 1.91/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_378,c_6]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_11,plain,
% 1.91/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 1.91/1.01      inference(cnf_transformation,[],[f60]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1017,plain,
% 1.91/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_xboole_0
% 1.91/1.01      | k2_enumset1(k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0),k1_funct_1(k1_xboole_0,X0)) = k1_xboole_0 ),
% 1.91/1.01      inference(light_normalisation,[status(thm)],[c_388,c_10,c_11]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1998,plain,
% 1.91/1.01      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) = k1_xboole_0 ),
% 1.91/1.01      inference(superposition,[status(thm)],[c_1907,c_1017]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1517,plain,
% 1.91/1.01      ( k2_enumset1(k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1),k1_funct_1(sK3,sK1)) != k2_relat_1(sK3) ),
% 1.91/1.01      inference(demodulation,[status(thm)],[c_1508,c_21]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1808,plain,
% 1.91/1.01      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) != k2_relat_1(k1_xboole_0) ),
% 1.91/1.01      inference(demodulation,[status(thm)],[c_1803,c_1517]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(c_1816,plain,
% 1.91/1.01      ( k2_enumset1(k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1),k1_funct_1(k1_xboole_0,sK1)) != k1_xboole_0 ),
% 1.91/1.01      inference(light_normalisation,[status(thm)],[c_1808,c_10]) ).
% 1.91/1.01  
% 1.91/1.01  cnf(contradiction,plain,
% 1.91/1.01      ( $false ),
% 1.91/1.01      inference(minisat,[status(thm)],[c_1998,c_1816]) ).
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 1.91/1.01  
% 1.91/1.01  ------                               Statistics
% 1.91/1.01  
% 1.91/1.01  ------ General
% 1.91/1.01  
% 1.91/1.01  abstr_ref_over_cycles:                  0
% 1.91/1.01  abstr_ref_under_cycles:                 0
% 1.91/1.01  gc_basic_clause_elim:                   0
% 1.91/1.01  forced_gc_time:                         0
% 1.91/1.01  parsing_time:                           0.01
% 1.91/1.01  unif_index_cands_time:                  0.
% 1.91/1.01  unif_index_add_time:                    0.
% 1.91/1.01  orderings_time:                         0.
% 1.91/1.01  out_proof_time:                         0.013
% 1.91/1.01  total_time:                             0.105
% 1.91/1.01  num_of_symbols:                         51
% 1.91/1.01  num_of_terms:                           1506
% 1.91/1.01  
% 1.91/1.01  ------ Preprocessing
% 1.91/1.01  
% 1.91/1.01  num_of_splits:                          0
% 1.91/1.01  num_of_split_atoms:                     0
% 1.91/1.01  num_of_reused_defs:                     0
% 1.91/1.01  num_eq_ax_congr_red:                    6
% 1.91/1.01  num_of_sem_filtered_clauses:            1
% 1.91/1.01  num_of_subtypes:                        0
% 1.91/1.01  monotx_restored_types:                  0
% 1.91/1.01  sat_num_of_epr_types:                   0
% 1.91/1.01  sat_num_of_non_cyclic_types:            0
% 1.91/1.01  sat_guarded_non_collapsed_types:        0
% 1.91/1.01  num_pure_diseq_elim:                    0
% 1.91/1.01  simp_replaced_by:                       0
% 1.91/1.01  res_preprocessed:                       108
% 1.91/1.01  prep_upred:                             0
% 1.91/1.01  prep_unflattend:                        24
% 1.91/1.01  smt_new_axioms:                         0
% 1.91/1.01  pred_elim_cands:                        3
% 1.91/1.01  pred_elim:                              5
% 1.91/1.01  pred_elim_cl:                           7
% 1.91/1.01  pred_elim_cycles:                       9
% 1.91/1.01  merged_defs:                            0
% 1.91/1.01  merged_defs_ncl:                        0
% 1.91/1.01  bin_hyper_res:                          0
% 1.91/1.01  prep_cycles:                            4
% 1.91/1.01  pred_elim_time:                         0.006
% 1.91/1.01  splitting_time:                         0.
% 1.91/1.01  sem_filter_time:                        0.
% 1.91/1.01  monotx_time:                            0.001
% 1.91/1.01  subtype_inf_time:                       0.
% 1.91/1.01  
% 1.91/1.01  ------ Problem properties
% 1.91/1.01  
% 1.91/1.01  clauses:                                19
% 1.91/1.01  conjectures:                            3
% 1.91/1.01  epr:                                    2
% 1.91/1.01  horn:                                   17
% 1.91/1.01  ground:                                 5
% 1.91/1.01  unary:                                  8
% 1.91/1.01  binary:                                 6
% 1.91/1.01  lits:                                   35
% 1.91/1.01  lits_eq:                                16
% 1.91/1.01  fd_pure:                                0
% 1.91/1.01  fd_pseudo:                              0
% 1.91/1.01  fd_cond:                                3
% 1.91/1.01  fd_pseudo_cond:                         0
% 1.91/1.01  ac_symbols:                             0
% 1.91/1.01  
% 1.91/1.01  ------ Propositional Solver
% 1.91/1.01  
% 1.91/1.01  prop_solver_calls:                      27
% 1.91/1.01  prop_fast_solver_calls:                 575
% 1.91/1.01  smt_solver_calls:                       0
% 1.91/1.01  smt_fast_solver_calls:                  0
% 1.91/1.01  prop_num_of_clauses:                    634
% 1.91/1.01  prop_preprocess_simplified:             3293
% 1.91/1.01  prop_fo_subsumed:                       7
% 1.91/1.01  prop_solver_time:                       0.
% 1.91/1.01  smt_solver_time:                        0.
% 1.91/1.01  smt_fast_solver_time:                   0.
% 1.91/1.01  prop_fast_solver_time:                  0.
% 1.91/1.01  prop_unsat_core_time:                   0.
% 1.91/1.01  
% 1.91/1.01  ------ QBF
% 1.91/1.01  
% 1.91/1.01  qbf_q_res:                              0
% 1.91/1.01  qbf_num_tautologies:                    0
% 1.91/1.01  qbf_prep_cycles:                        0
% 1.91/1.01  
% 1.91/1.01  ------ BMC1
% 1.91/1.01  
% 1.91/1.01  bmc1_current_bound:                     -1
% 1.91/1.01  bmc1_last_solved_bound:                 -1
% 1.91/1.01  bmc1_unsat_core_size:                   -1
% 1.91/1.01  bmc1_unsat_core_parents_size:           -1
% 1.91/1.01  bmc1_merge_next_fun:                    0
% 1.91/1.01  bmc1_unsat_core_clauses_time:           0.
% 1.91/1.01  
% 1.91/1.01  ------ Instantiation
% 1.91/1.01  
% 1.91/1.01  inst_num_of_clauses:                    243
% 1.91/1.01  inst_num_in_passive:                    111
% 1.91/1.01  inst_num_in_active:                     132
% 1.91/1.01  inst_num_in_unprocessed:                1
% 1.91/1.01  inst_num_of_loops:                      160
% 1.91/1.01  inst_num_of_learning_restarts:          0
% 1.91/1.01  inst_num_moves_active_passive:          25
% 1.91/1.01  inst_lit_activity:                      0
% 1.91/1.01  inst_lit_activity_moves:                0
% 1.91/1.01  inst_num_tautologies:                   0
% 1.91/1.01  inst_num_prop_implied:                  0
% 1.91/1.01  inst_num_existing_simplified:           0
% 1.91/1.01  inst_num_eq_res_simplified:             0
% 1.91/1.01  inst_num_child_elim:                    0
% 1.91/1.01  inst_num_of_dismatching_blockings:      29
% 1.91/1.01  inst_num_of_non_proper_insts:           134
% 1.91/1.01  inst_num_of_duplicates:                 0
% 1.91/1.01  inst_inst_num_from_inst_to_res:         0
% 1.91/1.01  inst_dismatching_checking_time:         0.
% 1.91/1.01  
% 1.91/1.01  ------ Resolution
% 1.91/1.01  
% 1.91/1.01  res_num_of_clauses:                     0
% 1.91/1.01  res_num_in_passive:                     0
% 1.91/1.01  res_num_in_active:                      0
% 1.91/1.01  res_num_of_loops:                       112
% 1.91/1.01  res_forward_subset_subsumed:            20
% 1.91/1.01  res_backward_subset_subsumed:           2
% 1.91/1.01  res_forward_subsumed:                   1
% 1.91/1.01  res_backward_subsumed:                  1
% 1.91/1.01  res_forward_subsumption_resolution:     1
% 1.91/1.01  res_backward_subsumption_resolution:    0
% 1.91/1.01  res_clause_to_clause_subsumption:       48
% 1.91/1.01  res_orphan_elimination:                 0
% 1.91/1.01  res_tautology_del:                      26
% 1.91/1.01  res_num_eq_res_simplified:              0
% 1.91/1.01  res_num_sel_changes:                    0
% 1.91/1.01  res_moves_from_active_to_pass:          0
% 1.91/1.01  
% 1.91/1.01  ------ Superposition
% 1.91/1.01  
% 1.91/1.01  sup_time_total:                         0.
% 1.91/1.01  sup_time_generating:                    0.
% 1.91/1.01  sup_time_sim_full:                      0.
% 1.91/1.01  sup_time_sim_immed:                     0.
% 1.91/1.01  
% 1.91/1.01  sup_num_of_clauses:                     23
% 1.91/1.01  sup_num_in_active:                      20
% 1.91/1.01  sup_num_in_passive:                     3
% 1.91/1.01  sup_num_of_loops:                       30
% 1.91/1.01  sup_fw_superposition:                   12
% 1.91/1.01  sup_bw_superposition:                   7
% 1.91/1.01  sup_immediate_simplified:               11
% 1.91/1.01  sup_given_eliminated:                   0
% 1.91/1.01  comparisons_done:                       0
% 1.91/1.01  comparisons_avoided:                    0
% 1.91/1.01  
% 1.91/1.01  ------ Simplifications
% 1.91/1.01  
% 1.91/1.01  
% 1.91/1.01  sim_fw_subset_subsumed:                 4
% 1.91/1.01  sim_bw_subset_subsumed:                 0
% 1.91/1.01  sim_fw_subsumed:                        4
% 1.91/1.01  sim_bw_subsumed:                        0
% 1.91/1.01  sim_fw_subsumption_res:                 1
% 1.91/1.01  sim_bw_subsumption_res:                 0
% 1.91/1.01  sim_tautology_del:                      0
% 1.91/1.01  sim_eq_tautology_del:                   1
% 1.91/1.01  sim_eq_res_simp:                        0
% 1.91/1.01  sim_fw_demodulated:                     0
% 1.91/1.01  sim_bw_demodulated:                     11
% 1.91/1.01  sim_light_normalised:                   8
% 1.91/1.01  sim_joinable_taut:                      0
% 1.91/1.01  sim_joinable_simp:                      0
% 1.91/1.01  sim_ac_normalised:                      0
% 1.91/1.01  sim_smt_subsumption:                    0
% 1.91/1.01  
%------------------------------------------------------------------------------
