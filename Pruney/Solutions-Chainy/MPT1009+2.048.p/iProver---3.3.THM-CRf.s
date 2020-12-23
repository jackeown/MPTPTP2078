%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:37 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : Number of formulae       :  183 (1470 expanded)
%              Number of clauses        :  114 ( 375 expanded)
%              Number of leaves         :   20 ( 340 expanded)
%              Depth                    :   28
%              Number of atoms          :  423 (3492 expanded)
%              Number of equality atoms :  235 (1523 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f20,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f38,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f37])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f41])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f67,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f68,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f67])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f64,f68])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f68])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( r2_hidden(X0,k1_relat_1(X1))
          | k1_xboole_0 = k11_relat_1(X1,X0) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_relat_1(X1))
      | k1_xboole_0 = k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f59,f68,f68])).

fof(f63,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(X0,k1_relat_1(X1))
       => k1_relat_1(k7_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f68])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f66,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f73,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f66,f68,f68])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f57,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_268,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_15,c_9])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_272,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_268,c_15,c_14,c_9])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_307,plain,
    ( k7_relat_1(X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_272,c_19])).

cnf(c_308,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_976,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k7_relat_1(sK3,X0_49) = sK3 ),
    inference(subtyping,[status(esa)],[c_308])).

cnf(c_1543,plain,
    ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_976])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_159,plain,
    ( ~ r2_hidden(X0,X1)
    | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
    inference(prop_impl,[status(thm)],[c_1])).

cnf(c_7,plain,
    ( r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_361,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
    | ~ v1_relat_1(X2)
    | X3 != X0
    | k11_relat_1(X2,X3) = k1_xboole_0
    | k1_relat_1(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_159,c_7])).

cnf(c_362,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k11_relat_1(X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_325,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_19])).

cnf(c_326,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_325])).

cnf(c_599,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(X1))
    | k11_relat_1(X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_362,c_326])).

cnf(c_600,plain,
    ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3))
    | k11_relat_1(sK3,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_968,plain,
    ( r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k11_relat_1(sK3,X0_52) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_600])).

cnf(c_992,plain,
    ( r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3))
    | k11_relat_1(sK3,X0_52) = k1_xboole_0
    | ~ sP5_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP5_iProver_split])],[c_968])).

cnf(c_1397,plain,
    ( k11_relat_1(sK3,X0_52) = k1_xboole_0
    | r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3)) = iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(c_993,plain,
    ( sP5_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_968])).

cnf(c_1065,plain,
    ( sP5_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_993])).

cnf(c_1066,plain,
    ( k11_relat_1(sK3,X0_52) = k1_xboole_0
    | r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3)) = iProver_top
    | sP5_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_992])).

cnf(c_1000,plain,
    ( X0_50 = X0_50 ),
    theory(equality)).

cnf(c_1550,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_1000])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_288,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_20])).

cnf(c_289,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_534,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(resolution,[status(thm)],[c_326,c_289])).

cnf(c_974,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k2_enumset1(X0_52,X0_52,X0_52,X0_52) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52)) = k2_relat_1(sK3) ),
    inference(subtyping,[status(esa)],[c_534])).

cnf(c_982,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | ~ sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP1_iProver_split])],[c_974])).

cnf(c_1551,plain,
    ( ~ sP1_iProver_split
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_982])).

cnf(c_1554,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | sP1_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1551])).

cnf(c_2158,plain,
    ( r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3)) = iProver_top
    | k11_relat_1(sK3,X0_52) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1397,c_1065,c_1066,c_1550,c_1554])).

cnf(c_2159,plain,
    ( k11_relat_1(sK3,X0_52) = k1_xboole_0
    | r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2158])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_629,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | k1_relat_1(k7_relat_1(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_326])).

cnf(c_630,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_966,plain,
    ( ~ r1_tarski(X0_49,k1_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))
    | k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_630])).

cnf(c_996,plain,
    ( ~ r1_tarski(X0_49,k1_relat_1(sK3))
    | k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49
    | ~ sP7_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP7_iProver_split])],[c_966])).

cnf(c_1403,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49
    | r1_tarski(X0_49,k1_relat_1(sK3)) != iProver_top
    | sP7_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_997,plain,
    ( sP7_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_966])).

cnf(c_1075,plain,
    ( sP7_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_997])).

cnf(c_1076,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49
    | r1_tarski(X0_49,k1_relat_1(sK3)) != iProver_top
    | sP7_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_996])).

cnf(c_1813,plain,
    ( r1_tarski(X0_49,k1_relat_1(sK3)) != iProver_top
    | k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1403,c_1075,c_1076,c_1550,c_1554])).

cnf(c_1814,plain,
    ( k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49
    | r1_tarski(X0_49,k1_relat_1(sK3)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1813])).

cnf(c_2166,plain,
    ( k11_relat_1(sK3,X0_52) = k1_xboole_0
    | k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0_52,X0_52,X0_52,X0_52))) = k2_enumset1(X0_52,X0_52,X0_52,X0_52) ),
    inference(superposition,[status(thm)],[c_2159,c_1814])).

cnf(c_2294,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k11_relat_1(sK3,sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1543,c_2166])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_569,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_326])).

cnf(c_570,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(k7_relat_1(sK3,X2)) = k9_relat_1(sK3,X2) ),
    inference(unflattening,[status(thm)],[c_569])).

cnf(c_971,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k2_relat_1(k7_relat_1(sK3,X2_49)) = k9_relat_1(sK3,X2_49) ),
    inference(subtyping,[status(esa)],[c_570])).

cnf(c_986,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0_49)) = k9_relat_1(sK3,X0_49)
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_971])).

cnf(c_1389,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0_49)) = k9_relat_1(sK3,X0_49)
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_986])).

cnf(c_987,plain,
    ( sP2_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_971])).

cnf(c_1574,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0_49)) = k9_relat_1(sK3,X0_49) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1389,c_987,c_986,c_1550,c_1551])).

cnf(c_1578,plain,
    ( k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1543,c_1574])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_590,plain,
    ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_326])).

cnf(c_591,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_590])).

cnf(c_969,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k9_relat_1(sK3,k2_enumset1(X0_52,X0_52,X0_52,X0_52)) = k11_relat_1(sK3,X0_52) ),
    inference(subtyping,[status(esa)],[c_591])).

cnf(c_990,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0_52,X0_52,X0_52,X0_52)) = k11_relat_1(sK3,X0_52)
    | ~ sP4_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP4_iProver_split])],[c_969])).

cnf(c_1395,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0_52,X0_52,X0_52,X0_52)) = k11_relat_1(sK3,X0_52)
    | sP4_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_990])).

cnf(c_991,plain,
    ( sP4_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_969])).

cnf(c_1718,plain,
    ( k9_relat_1(sK3,k2_enumset1(X0_52,X0_52,X0_52,X0_52)) = k11_relat_1(sK3,X0_52) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1395,c_991,c_990,c_1550,c_1551])).

cnf(c_1722,plain,
    ( k11_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1578,c_1718])).

cnf(c_2295,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2294,c_1722])).

cnf(c_981,plain,
    ( k2_enumset1(X0_52,X0_52,X0_52,X0_52) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52)) = k2_relat_1(sK3)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_974])).

cnf(c_1382,plain,
    ( k2_enumset1(X0_52,X0_52,X0_52,X0_52) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52)) = k2_relat_1(sK3)
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_981])).

cnf(c_983,plain,
    ( sP1_iProver_split
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_974])).

cnf(c_1871,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52)) = k2_relat_1(sK3)
    | k2_enumset1(X0_52,X0_52,X0_52,X0_52) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1382,c_983,c_981,c_1550,c_1551])).

cnf(c_1872,plain,
    ( k2_enumset1(X0_52,X0_52,X0_52,X0_52) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1871])).

cnf(c_2305,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2295,c_1872])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_316,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_19])).

cnf(c_317,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_316])).

cnf(c_975,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k7_relset_1(X0_49,X1_49,sK3,X2_49) = k9_relat_1(sK3,X2_49) ),
    inference(subtyping,[status(esa)],[c_317])).

cnf(c_1546,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0_49) = k9_relat_1(sK3,X0_49) ),
    inference(equality_resolution,[status(thm)],[c_975])).

cnf(c_17,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_978,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1379,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_978])).

cnf(c_1560,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1546,c_1379])).

cnf(c_2550,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2305,c_1560])).

cnf(c_4,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_578,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_326])).

cnf(c_579,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
    inference(unflattening,[status(thm)],[c_578])).

cnf(c_970,plain,
    ( r1_tarski(k9_relat_1(sK3,X0_49),k2_relat_1(sK3))
    | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)) ),
    inference(subtyping,[status(esa)],[c_579])).

cnf(c_989,plain,
    ( sP3_iProver_split
    | sP1_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_970])).

cnf(c_1055,plain,
    ( sP3_iProver_split = iProver_top
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_989])).

cnf(c_988,plain,
    ( r1_tarski(k9_relat_1(sK3,X0_49),k2_relat_1(sK3))
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_970])).

cnf(c_2233,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ sP3_iProver_split ),
    inference(instantiation,[status(thm)],[c_988])).

cnf(c_2238,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) = iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2233])).

cnf(c_2616,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2550,c_1055,c_1550,c_1554,c_2238])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_557,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(X2) != k1_xboole_0
    | sK3 != X2
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_326])).

cnf(c_558,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k2_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_557])).

cnf(c_972,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
    | k2_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(subtyping,[status(esa)],[c_558])).

cnf(c_985,plain,
    ( sP1_iProver_split
    | k2_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_972])).

cnf(c_1385,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3
    | sP1_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_985])).

cnf(c_2014,plain,
    ( k1_xboole_0 = sK3
    | k2_relat_1(sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1385,c_985,c_1550,c_1551])).

cnf(c_2015,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(renaming,[status(thm)],[c_2014])).

cnf(c_2627,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2616,c_2015])).

cnf(c_2639,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_2627])).

cnf(c_2688,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2639,c_1560])).

cnf(c_6,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_979,plain,
    ( k9_relat_1(k1_xboole_0,X0_49) = k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_2708,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2688,c_979])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_980,plain,
    ( r1_tarski(k1_xboole_0,X0_49) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1378,plain,
    ( r1_tarski(k1_xboole_0,X0_49) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_980])).

cnf(c_3028,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2708,c_1378])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:49:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.45/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.00  
% 2.45/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/1.00  
% 2.45/1.00  ------  iProver source info
% 2.45/1.00  
% 2.45/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.45/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/1.00  git: non_committed_changes: false
% 2.45/1.00  git: last_make_outside_of_git: false
% 2.45/1.00  
% 2.45/1.00  ------ 
% 2.45/1.00  
% 2.45/1.00  ------ Input Options
% 2.45/1.00  
% 2.45/1.00  --out_options                           all
% 2.45/1.00  --tptp_safe_out                         true
% 2.45/1.00  --problem_path                          ""
% 2.45/1.00  --include_path                          ""
% 2.45/1.00  --clausifier                            res/vclausify_rel
% 2.45/1.00  --clausifier_options                    --mode clausify
% 2.45/1.00  --stdin                                 false
% 2.45/1.00  --stats_out                             all
% 2.45/1.00  
% 2.45/1.00  ------ General Options
% 2.45/1.00  
% 2.45/1.00  --fof                                   false
% 2.45/1.00  --time_out_real                         305.
% 2.45/1.00  --time_out_virtual                      -1.
% 2.45/1.00  --symbol_type_check                     false
% 2.45/1.00  --clausify_out                          false
% 2.45/1.00  --sig_cnt_out                           false
% 2.45/1.00  --trig_cnt_out                          false
% 2.45/1.00  --trig_cnt_out_tolerance                1.
% 2.45/1.00  --trig_cnt_out_sk_spl                   false
% 2.45/1.00  --abstr_cl_out                          false
% 2.45/1.00  
% 2.45/1.00  ------ Global Options
% 2.45/1.00  
% 2.45/1.00  --schedule                              default
% 2.45/1.00  --add_important_lit                     false
% 2.45/1.00  --prop_solver_per_cl                    1000
% 2.45/1.00  --min_unsat_core                        false
% 2.45/1.00  --soft_assumptions                      false
% 2.45/1.00  --soft_lemma_size                       3
% 2.45/1.00  --prop_impl_unit_size                   0
% 2.45/1.00  --prop_impl_unit                        []
% 2.45/1.00  --share_sel_clauses                     true
% 2.45/1.00  --reset_solvers                         false
% 2.45/1.00  --bc_imp_inh                            [conj_cone]
% 2.45/1.00  --conj_cone_tolerance                   3.
% 2.45/1.00  --extra_neg_conj                        none
% 2.45/1.00  --large_theory_mode                     true
% 2.45/1.00  --prolific_symb_bound                   200
% 2.45/1.00  --lt_threshold                          2000
% 2.45/1.00  --clause_weak_htbl                      true
% 2.45/1.00  --gc_record_bc_elim                     false
% 2.45/1.00  
% 2.45/1.00  ------ Preprocessing Options
% 2.45/1.00  
% 2.45/1.00  --preprocessing_flag                    true
% 2.45/1.00  --time_out_prep_mult                    0.1
% 2.45/1.00  --splitting_mode                        input
% 2.45/1.00  --splitting_grd                         true
% 2.45/1.00  --splitting_cvd                         false
% 2.45/1.00  --splitting_cvd_svl                     false
% 2.45/1.00  --splitting_nvd                         32
% 2.45/1.00  --sub_typing                            true
% 2.45/1.00  --prep_gs_sim                           true
% 2.45/1.00  --prep_unflatten                        true
% 2.45/1.00  --prep_res_sim                          true
% 2.45/1.00  --prep_upred                            true
% 2.45/1.00  --prep_sem_filter                       exhaustive
% 2.45/1.00  --prep_sem_filter_out                   false
% 2.45/1.00  --pred_elim                             true
% 2.45/1.00  --res_sim_input                         true
% 2.45/1.00  --eq_ax_congr_red                       true
% 2.45/1.00  --pure_diseq_elim                       true
% 2.45/1.00  --brand_transform                       false
% 2.45/1.00  --non_eq_to_eq                          false
% 2.45/1.00  --prep_def_merge                        true
% 2.45/1.00  --prep_def_merge_prop_impl              false
% 2.45/1.00  --prep_def_merge_mbd                    true
% 2.45/1.00  --prep_def_merge_tr_red                 false
% 2.45/1.00  --prep_def_merge_tr_cl                  false
% 2.45/1.00  --smt_preprocessing                     true
% 2.45/1.00  --smt_ac_axioms                         fast
% 2.45/1.00  --preprocessed_out                      false
% 2.45/1.00  --preprocessed_stats                    false
% 2.45/1.00  
% 2.45/1.00  ------ Abstraction refinement Options
% 2.45/1.00  
% 2.45/1.00  --abstr_ref                             []
% 2.45/1.00  --abstr_ref_prep                        false
% 2.45/1.00  --abstr_ref_until_sat                   false
% 2.45/1.00  --abstr_ref_sig_restrict                funpre
% 2.45/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.00  --abstr_ref_under                       []
% 2.45/1.00  
% 2.45/1.00  ------ SAT Options
% 2.45/1.00  
% 2.45/1.00  --sat_mode                              false
% 2.45/1.00  --sat_fm_restart_options                ""
% 2.45/1.00  --sat_gr_def                            false
% 2.45/1.00  --sat_epr_types                         true
% 2.45/1.00  --sat_non_cyclic_types                  false
% 2.45/1.00  --sat_finite_models                     false
% 2.45/1.00  --sat_fm_lemmas                         false
% 2.45/1.00  --sat_fm_prep                           false
% 2.45/1.01  --sat_fm_uc_incr                        true
% 2.45/1.01  --sat_out_model                         small
% 2.45/1.01  --sat_out_clauses                       false
% 2.45/1.01  
% 2.45/1.01  ------ QBF Options
% 2.45/1.01  
% 2.45/1.01  --qbf_mode                              false
% 2.45/1.01  --qbf_elim_univ                         false
% 2.45/1.01  --qbf_dom_inst                          none
% 2.45/1.01  --qbf_dom_pre_inst                      false
% 2.45/1.01  --qbf_sk_in                             false
% 2.45/1.01  --qbf_pred_elim                         true
% 2.45/1.01  --qbf_split                             512
% 2.45/1.01  
% 2.45/1.01  ------ BMC1 Options
% 2.45/1.01  
% 2.45/1.01  --bmc1_incremental                      false
% 2.45/1.01  --bmc1_axioms                           reachable_all
% 2.45/1.01  --bmc1_min_bound                        0
% 2.45/1.01  --bmc1_max_bound                        -1
% 2.45/1.01  --bmc1_max_bound_default                -1
% 2.45/1.01  --bmc1_symbol_reachability              true
% 2.45/1.01  --bmc1_property_lemmas                  false
% 2.45/1.01  --bmc1_k_induction                      false
% 2.45/1.01  --bmc1_non_equiv_states                 false
% 2.45/1.01  --bmc1_deadlock                         false
% 2.45/1.01  --bmc1_ucm                              false
% 2.45/1.01  --bmc1_add_unsat_core                   none
% 2.45/1.01  --bmc1_unsat_core_children              false
% 2.45/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.01  --bmc1_out_stat                         full
% 2.45/1.01  --bmc1_ground_init                      false
% 2.45/1.01  --bmc1_pre_inst_next_state              false
% 2.45/1.01  --bmc1_pre_inst_state                   false
% 2.45/1.01  --bmc1_pre_inst_reach_state             false
% 2.45/1.01  --bmc1_out_unsat_core                   false
% 2.45/1.01  --bmc1_aig_witness_out                  false
% 2.45/1.01  --bmc1_verbose                          false
% 2.45/1.01  --bmc1_dump_clauses_tptp                false
% 2.45/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.01  --bmc1_dump_file                        -
% 2.45/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.01  --bmc1_ucm_extend_mode                  1
% 2.45/1.01  --bmc1_ucm_init_mode                    2
% 2.45/1.01  --bmc1_ucm_cone_mode                    none
% 2.45/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.01  --bmc1_ucm_relax_model                  4
% 2.45/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.01  --bmc1_ucm_layered_model                none
% 2.45/1.01  --bmc1_ucm_max_lemma_size               10
% 2.45/1.01  
% 2.45/1.01  ------ AIG Options
% 2.45/1.01  
% 2.45/1.01  --aig_mode                              false
% 2.45/1.01  
% 2.45/1.01  ------ Instantiation Options
% 2.45/1.01  
% 2.45/1.01  --instantiation_flag                    true
% 2.45/1.01  --inst_sos_flag                         false
% 2.45/1.01  --inst_sos_phase                        true
% 2.45/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel_side                     num_symb
% 2.45/1.01  --inst_solver_per_active                1400
% 2.45/1.01  --inst_solver_calls_frac                1.
% 2.45/1.01  --inst_passive_queue_type               priority_queues
% 2.45/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.01  --inst_passive_queues_freq              [25;2]
% 2.45/1.01  --inst_dismatching                      true
% 2.45/1.01  --inst_eager_unprocessed_to_passive     true
% 2.45/1.01  --inst_prop_sim_given                   true
% 2.45/1.01  --inst_prop_sim_new                     false
% 2.45/1.01  --inst_subs_new                         false
% 2.45/1.01  --inst_eq_res_simp                      false
% 2.45/1.01  --inst_subs_given                       false
% 2.45/1.01  --inst_orphan_elimination               true
% 2.45/1.01  --inst_learning_loop_flag               true
% 2.45/1.01  --inst_learning_start                   3000
% 2.45/1.01  --inst_learning_factor                  2
% 2.45/1.01  --inst_start_prop_sim_after_learn       3
% 2.45/1.01  --inst_sel_renew                        solver
% 2.45/1.01  --inst_lit_activity_flag                true
% 2.45/1.01  --inst_restr_to_given                   false
% 2.45/1.01  --inst_activity_threshold               500
% 2.45/1.01  --inst_out_proof                        true
% 2.45/1.01  
% 2.45/1.01  ------ Resolution Options
% 2.45/1.01  
% 2.45/1.01  --resolution_flag                       true
% 2.45/1.01  --res_lit_sel                           adaptive
% 2.45/1.01  --res_lit_sel_side                      none
% 2.45/1.01  --res_ordering                          kbo
% 2.45/1.01  --res_to_prop_solver                    active
% 2.45/1.01  --res_prop_simpl_new                    false
% 2.45/1.01  --res_prop_simpl_given                  true
% 2.45/1.01  --res_passive_queue_type                priority_queues
% 2.45/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.01  --res_passive_queues_freq               [15;5]
% 2.45/1.01  --res_forward_subs                      full
% 2.45/1.01  --res_backward_subs                     full
% 2.45/1.01  --res_forward_subs_resolution           true
% 2.45/1.01  --res_backward_subs_resolution          true
% 2.45/1.01  --res_orphan_elimination                true
% 2.45/1.01  --res_time_limit                        2.
% 2.45/1.01  --res_out_proof                         true
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Options
% 2.45/1.01  
% 2.45/1.01  --superposition_flag                    true
% 2.45/1.01  --sup_passive_queue_type                priority_queues
% 2.45/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.01  --demod_completeness_check              fast
% 2.45/1.01  --demod_use_ground                      true
% 2.45/1.01  --sup_to_prop_solver                    passive
% 2.45/1.01  --sup_prop_simpl_new                    true
% 2.45/1.01  --sup_prop_simpl_given                  true
% 2.45/1.01  --sup_fun_splitting                     false
% 2.45/1.01  --sup_smt_interval                      50000
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Simplification Setup
% 2.45/1.01  
% 2.45/1.01  --sup_indices_passive                   []
% 2.45/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_full_bw                           [BwDemod]
% 2.45/1.01  --sup_immed_triv                        [TrivRules]
% 2.45/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_immed_bw_main                     []
% 2.45/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  
% 2.45/1.01  ------ Combination Options
% 2.45/1.01  
% 2.45/1.01  --comb_res_mult                         3
% 2.45/1.01  --comb_sup_mult                         2
% 2.45/1.01  --comb_inst_mult                        10
% 2.45/1.01  
% 2.45/1.01  ------ Debug Options
% 2.45/1.01  
% 2.45/1.01  --dbg_backtrace                         false
% 2.45/1.01  --dbg_dump_prop_clauses                 false
% 2.45/1.01  --dbg_dump_prop_clauses_file            -
% 2.45/1.01  --dbg_out_stat                          false
% 2.45/1.01  ------ Parsing...
% 2.45/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing... gs_s  sp: 16 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/1.01  ------ Proving...
% 2.45/1.01  ------ Problem Properties 
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  clauses                                 31
% 2.45/1.01  conjectures                             2
% 2.45/1.01  EPR                                     9
% 2.45/1.01  Horn                                    21
% 2.45/1.01  unary                                   4
% 2.45/1.01  binary                                  21
% 2.45/1.01  lits                                    64
% 2.45/1.01  lits eq                                 26
% 2.45/1.01  fd_pure                                 0
% 2.45/1.01  fd_pseudo                               0
% 2.45/1.01  fd_cond                                 0
% 2.45/1.01  fd_pseudo_cond                          0
% 2.45/1.01  AC symbols                              0
% 2.45/1.01  
% 2.45/1.01  ------ Schedule dynamic 5 is on 
% 2.45/1.01  
% 2.45/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  ------ 
% 2.45/1.01  Current options:
% 2.45/1.01  ------ 
% 2.45/1.01  
% 2.45/1.01  ------ Input Options
% 2.45/1.01  
% 2.45/1.01  --out_options                           all
% 2.45/1.01  --tptp_safe_out                         true
% 2.45/1.01  --problem_path                          ""
% 2.45/1.01  --include_path                          ""
% 2.45/1.01  --clausifier                            res/vclausify_rel
% 2.45/1.01  --clausifier_options                    --mode clausify
% 2.45/1.01  --stdin                                 false
% 2.45/1.01  --stats_out                             all
% 2.45/1.01  
% 2.45/1.01  ------ General Options
% 2.45/1.01  
% 2.45/1.01  --fof                                   false
% 2.45/1.01  --time_out_real                         305.
% 2.45/1.01  --time_out_virtual                      -1.
% 2.45/1.01  --symbol_type_check                     false
% 2.45/1.01  --clausify_out                          false
% 2.45/1.01  --sig_cnt_out                           false
% 2.45/1.01  --trig_cnt_out                          false
% 2.45/1.01  --trig_cnt_out_tolerance                1.
% 2.45/1.01  --trig_cnt_out_sk_spl                   false
% 2.45/1.01  --abstr_cl_out                          false
% 2.45/1.01  
% 2.45/1.01  ------ Global Options
% 2.45/1.01  
% 2.45/1.01  --schedule                              default
% 2.45/1.01  --add_important_lit                     false
% 2.45/1.01  --prop_solver_per_cl                    1000
% 2.45/1.01  --min_unsat_core                        false
% 2.45/1.01  --soft_assumptions                      false
% 2.45/1.01  --soft_lemma_size                       3
% 2.45/1.01  --prop_impl_unit_size                   0
% 2.45/1.01  --prop_impl_unit                        []
% 2.45/1.01  --share_sel_clauses                     true
% 2.45/1.01  --reset_solvers                         false
% 2.45/1.01  --bc_imp_inh                            [conj_cone]
% 2.45/1.01  --conj_cone_tolerance                   3.
% 2.45/1.01  --extra_neg_conj                        none
% 2.45/1.01  --large_theory_mode                     true
% 2.45/1.01  --prolific_symb_bound                   200
% 2.45/1.01  --lt_threshold                          2000
% 2.45/1.01  --clause_weak_htbl                      true
% 2.45/1.01  --gc_record_bc_elim                     false
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing Options
% 2.45/1.01  
% 2.45/1.01  --preprocessing_flag                    true
% 2.45/1.01  --time_out_prep_mult                    0.1
% 2.45/1.01  --splitting_mode                        input
% 2.45/1.01  --splitting_grd                         true
% 2.45/1.01  --splitting_cvd                         false
% 2.45/1.01  --splitting_cvd_svl                     false
% 2.45/1.01  --splitting_nvd                         32
% 2.45/1.01  --sub_typing                            true
% 2.45/1.01  --prep_gs_sim                           true
% 2.45/1.01  --prep_unflatten                        true
% 2.45/1.01  --prep_res_sim                          true
% 2.45/1.01  --prep_upred                            true
% 2.45/1.01  --prep_sem_filter                       exhaustive
% 2.45/1.01  --prep_sem_filter_out                   false
% 2.45/1.01  --pred_elim                             true
% 2.45/1.01  --res_sim_input                         true
% 2.45/1.01  --eq_ax_congr_red                       true
% 2.45/1.01  --pure_diseq_elim                       true
% 2.45/1.01  --brand_transform                       false
% 2.45/1.01  --non_eq_to_eq                          false
% 2.45/1.01  --prep_def_merge                        true
% 2.45/1.01  --prep_def_merge_prop_impl              false
% 2.45/1.01  --prep_def_merge_mbd                    true
% 2.45/1.01  --prep_def_merge_tr_red                 false
% 2.45/1.01  --prep_def_merge_tr_cl                  false
% 2.45/1.01  --smt_preprocessing                     true
% 2.45/1.01  --smt_ac_axioms                         fast
% 2.45/1.01  --preprocessed_out                      false
% 2.45/1.01  --preprocessed_stats                    false
% 2.45/1.01  
% 2.45/1.01  ------ Abstraction refinement Options
% 2.45/1.01  
% 2.45/1.01  --abstr_ref                             []
% 2.45/1.01  --abstr_ref_prep                        false
% 2.45/1.01  --abstr_ref_until_sat                   false
% 2.45/1.01  --abstr_ref_sig_restrict                funpre
% 2.45/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.01  --abstr_ref_under                       []
% 2.45/1.01  
% 2.45/1.01  ------ SAT Options
% 2.45/1.01  
% 2.45/1.01  --sat_mode                              false
% 2.45/1.01  --sat_fm_restart_options                ""
% 2.45/1.01  --sat_gr_def                            false
% 2.45/1.01  --sat_epr_types                         true
% 2.45/1.01  --sat_non_cyclic_types                  false
% 2.45/1.01  --sat_finite_models                     false
% 2.45/1.01  --sat_fm_lemmas                         false
% 2.45/1.01  --sat_fm_prep                           false
% 2.45/1.01  --sat_fm_uc_incr                        true
% 2.45/1.01  --sat_out_model                         small
% 2.45/1.01  --sat_out_clauses                       false
% 2.45/1.01  
% 2.45/1.01  ------ QBF Options
% 2.45/1.01  
% 2.45/1.01  --qbf_mode                              false
% 2.45/1.01  --qbf_elim_univ                         false
% 2.45/1.01  --qbf_dom_inst                          none
% 2.45/1.01  --qbf_dom_pre_inst                      false
% 2.45/1.01  --qbf_sk_in                             false
% 2.45/1.01  --qbf_pred_elim                         true
% 2.45/1.01  --qbf_split                             512
% 2.45/1.01  
% 2.45/1.01  ------ BMC1 Options
% 2.45/1.01  
% 2.45/1.01  --bmc1_incremental                      false
% 2.45/1.01  --bmc1_axioms                           reachable_all
% 2.45/1.01  --bmc1_min_bound                        0
% 2.45/1.01  --bmc1_max_bound                        -1
% 2.45/1.01  --bmc1_max_bound_default                -1
% 2.45/1.01  --bmc1_symbol_reachability              true
% 2.45/1.01  --bmc1_property_lemmas                  false
% 2.45/1.01  --bmc1_k_induction                      false
% 2.45/1.01  --bmc1_non_equiv_states                 false
% 2.45/1.01  --bmc1_deadlock                         false
% 2.45/1.01  --bmc1_ucm                              false
% 2.45/1.01  --bmc1_add_unsat_core                   none
% 2.45/1.01  --bmc1_unsat_core_children              false
% 2.45/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.01  --bmc1_out_stat                         full
% 2.45/1.01  --bmc1_ground_init                      false
% 2.45/1.01  --bmc1_pre_inst_next_state              false
% 2.45/1.01  --bmc1_pre_inst_state                   false
% 2.45/1.01  --bmc1_pre_inst_reach_state             false
% 2.45/1.01  --bmc1_out_unsat_core                   false
% 2.45/1.01  --bmc1_aig_witness_out                  false
% 2.45/1.01  --bmc1_verbose                          false
% 2.45/1.01  --bmc1_dump_clauses_tptp                false
% 2.45/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.01  --bmc1_dump_file                        -
% 2.45/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.01  --bmc1_ucm_extend_mode                  1
% 2.45/1.01  --bmc1_ucm_init_mode                    2
% 2.45/1.01  --bmc1_ucm_cone_mode                    none
% 2.45/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.01  --bmc1_ucm_relax_model                  4
% 2.45/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.01  --bmc1_ucm_layered_model                none
% 2.45/1.01  --bmc1_ucm_max_lemma_size               10
% 2.45/1.01  
% 2.45/1.01  ------ AIG Options
% 2.45/1.01  
% 2.45/1.01  --aig_mode                              false
% 2.45/1.01  
% 2.45/1.01  ------ Instantiation Options
% 2.45/1.01  
% 2.45/1.01  --instantiation_flag                    true
% 2.45/1.01  --inst_sos_flag                         false
% 2.45/1.01  --inst_sos_phase                        true
% 2.45/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel_side                     none
% 2.45/1.01  --inst_solver_per_active                1400
% 2.45/1.01  --inst_solver_calls_frac                1.
% 2.45/1.01  --inst_passive_queue_type               priority_queues
% 2.45/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.01  --inst_passive_queues_freq              [25;2]
% 2.45/1.01  --inst_dismatching                      true
% 2.45/1.01  --inst_eager_unprocessed_to_passive     true
% 2.45/1.01  --inst_prop_sim_given                   true
% 2.45/1.01  --inst_prop_sim_new                     false
% 2.45/1.01  --inst_subs_new                         false
% 2.45/1.01  --inst_eq_res_simp                      false
% 2.45/1.01  --inst_subs_given                       false
% 2.45/1.01  --inst_orphan_elimination               true
% 2.45/1.01  --inst_learning_loop_flag               true
% 2.45/1.01  --inst_learning_start                   3000
% 2.45/1.01  --inst_learning_factor                  2
% 2.45/1.01  --inst_start_prop_sim_after_learn       3
% 2.45/1.01  --inst_sel_renew                        solver
% 2.45/1.01  --inst_lit_activity_flag                true
% 2.45/1.01  --inst_restr_to_given                   false
% 2.45/1.01  --inst_activity_threshold               500
% 2.45/1.01  --inst_out_proof                        true
% 2.45/1.01  
% 2.45/1.01  ------ Resolution Options
% 2.45/1.01  
% 2.45/1.01  --resolution_flag                       false
% 2.45/1.01  --res_lit_sel                           adaptive
% 2.45/1.01  --res_lit_sel_side                      none
% 2.45/1.01  --res_ordering                          kbo
% 2.45/1.01  --res_to_prop_solver                    active
% 2.45/1.01  --res_prop_simpl_new                    false
% 2.45/1.01  --res_prop_simpl_given                  true
% 2.45/1.01  --res_passive_queue_type                priority_queues
% 2.45/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.01  --res_passive_queues_freq               [15;5]
% 2.45/1.01  --res_forward_subs                      full
% 2.45/1.01  --res_backward_subs                     full
% 2.45/1.01  --res_forward_subs_resolution           true
% 2.45/1.01  --res_backward_subs_resolution          true
% 2.45/1.01  --res_orphan_elimination                true
% 2.45/1.01  --res_time_limit                        2.
% 2.45/1.01  --res_out_proof                         true
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Options
% 2.45/1.01  
% 2.45/1.01  --superposition_flag                    true
% 2.45/1.01  --sup_passive_queue_type                priority_queues
% 2.45/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.01  --demod_completeness_check              fast
% 2.45/1.01  --demod_use_ground                      true
% 2.45/1.01  --sup_to_prop_solver                    passive
% 2.45/1.01  --sup_prop_simpl_new                    true
% 2.45/1.01  --sup_prop_simpl_given                  true
% 2.45/1.01  --sup_fun_splitting                     false
% 2.45/1.01  --sup_smt_interval                      50000
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Simplification Setup
% 2.45/1.01  
% 2.45/1.01  --sup_indices_passive                   []
% 2.45/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_full_bw                           [BwDemod]
% 2.45/1.01  --sup_immed_triv                        [TrivRules]
% 2.45/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_immed_bw_main                     []
% 2.45/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  
% 2.45/1.01  ------ Combination Options
% 2.45/1.01  
% 2.45/1.01  --comb_res_mult                         3
% 2.45/1.01  --comb_sup_mult                         2
% 2.45/1.01  --comb_inst_mult                        10
% 2.45/1.01  
% 2.45/1.01  ------ Debug Options
% 2.45/1.01  
% 2.45/1.01  --dbg_backtrace                         false
% 2.45/1.01  --dbg_dump_prop_clauses                 false
% 2.45/1.01  --dbg_dump_prop_clauses_file            -
% 2.45/1.01  --dbg_out_stat                          false
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  ------ Proving...
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  % SZS status Theorem for theBenchmark.p
% 2.45/1.01  
% 2.45/1.01   Resolution empty clause
% 2.45/1.01  
% 2.45/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/1.01  
% 2.45/1.01  fof(f16,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f21,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.45/1.01    inference(pure_predicate_removal,[],[f16])).
% 2.45/1.01  
% 2.45/1.01  fof(f35,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.01    inference(ennf_transformation,[],[f21])).
% 2.45/1.01  
% 2.45/1.01  fof(f61,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.01    inference(cnf_transformation,[],[f35])).
% 2.45/1.01  
% 2.45/1.01  fof(f11,axiom,(
% 2.45/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f26,plain,(
% 2.45/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.45/1.01    inference(ennf_transformation,[],[f11])).
% 2.45/1.01  
% 2.45/1.01  fof(f27,plain,(
% 2.45/1.01    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.45/1.01    inference(flattening,[],[f26])).
% 2.45/1.01  
% 2.45/1.01  fof(f55,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f27])).
% 2.45/1.01  
% 2.45/1.01  fof(f15,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f34,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.01    inference(ennf_transformation,[],[f15])).
% 2.45/1.01  
% 2.45/1.01  fof(f60,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.01    inference(cnf_transformation,[],[f34])).
% 2.45/1.01  
% 2.45/1.01  fof(f18,conjecture,(
% 2.45/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f19,negated_conjecture,(
% 2.45/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.45/1.01    inference(negated_conjecture,[],[f18])).
% 2.45/1.01  
% 2.45/1.01  fof(f20,plain,(
% 2.45/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.45/1.01    inference(pure_predicate_removal,[],[f19])).
% 2.45/1.01  
% 2.45/1.01  fof(f37,plain,(
% 2.45/1.01    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.45/1.01    inference(ennf_transformation,[],[f20])).
% 2.45/1.01  
% 2.45/1.01  fof(f38,plain,(
% 2.45/1.01    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.45/1.01    inference(flattening,[],[f37])).
% 2.45/1.01  
% 2.45/1.01  fof(f41,plain,(
% 2.45/1.01    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.45/1.01    introduced(choice_axiom,[])).
% 2.45/1.01  
% 2.45/1.01  fof(f42,plain,(
% 2.45/1.01    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.45/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f41])).
% 2.45/1.01  
% 2.45/1.01  fof(f64,plain,(
% 2.45/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.45/1.01    inference(cnf_transformation,[],[f42])).
% 2.45/1.01  
% 2.45/1.01  fof(f2,axiom,(
% 2.45/1.01    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f44,plain,(
% 2.45/1.01    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f2])).
% 2.45/1.01  
% 2.45/1.01  fof(f3,axiom,(
% 2.45/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f45,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f3])).
% 2.45/1.01  
% 2.45/1.01  fof(f4,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f46,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f4])).
% 2.45/1.01  
% 2.45/1.01  fof(f67,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.45/1.01    inference(definition_unfolding,[],[f45,f46])).
% 2.45/1.01  
% 2.45/1.01  fof(f68,plain,(
% 2.45/1.01    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.45/1.01    inference(definition_unfolding,[],[f44,f67])).
% 2.45/1.01  
% 2.45/1.01  fof(f74,plain,(
% 2.45/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.45/1.01    inference(definition_unfolding,[],[f64,f68])).
% 2.45/1.01  
% 2.45/1.01  fof(f5,axiom,(
% 2.45/1.01    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f39,plain,(
% 2.45/1.01    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 2.45/1.01    inference(nnf_transformation,[],[f5])).
% 2.45/1.01  
% 2.45/1.01  fof(f48,plain,(
% 2.45/1.01    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f39])).
% 2.45/1.01  
% 2.45/1.01  fof(f69,plain,(
% 2.45/1.01    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.45/1.01    inference(definition_unfolding,[],[f48,f68])).
% 2.45/1.01  
% 2.45/1.01  fof(f10,axiom,(
% 2.45/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f25,plain,(
% 2.45/1.01    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.45/1.01    inference(ennf_transformation,[],[f10])).
% 2.45/1.01  
% 2.45/1.01  fof(f40,plain,(
% 2.45/1.01    ! [X0,X1] : (((r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0)) & (k1_xboole_0 != k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1)))) | ~v1_relat_1(X1))),
% 2.45/1.01    inference(nnf_transformation,[],[f25])).
% 2.45/1.01  
% 2.45/1.01  fof(f54,plain,(
% 2.45/1.01    ( ! [X0,X1] : (r2_hidden(X0,k1_relat_1(X1)) | k1_xboole_0 = k11_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f40])).
% 2.45/1.01  
% 2.45/1.01  fof(f14,axiom,(
% 2.45/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f32,plain,(
% 2.45/1.01    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.45/1.01    inference(ennf_transformation,[],[f14])).
% 2.45/1.01  
% 2.45/1.01  fof(f33,plain,(
% 2.45/1.01    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.45/1.01    inference(flattening,[],[f32])).
% 2.45/1.01  
% 2.45/1.01  fof(f59,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f33])).
% 2.45/1.01  
% 2.45/1.01  fof(f72,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.45/1.01    inference(definition_unfolding,[],[f59,f68,f68])).
% 2.45/1.01  
% 2.45/1.01  fof(f63,plain,(
% 2.45/1.01    v1_funct_1(sK3)),
% 2.45/1.01    inference(cnf_transformation,[],[f42])).
% 2.45/1.01  
% 2.45/1.01  fof(f13,axiom,(
% 2.45/1.01    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(X0,k1_relat_1(X1)) => k1_relat_1(k7_relat_1(X1,X0)) = X0))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f30,plain,(
% 2.45/1.01    ! [X0,X1] : ((k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 2.45/1.01    inference(ennf_transformation,[],[f13])).
% 2.45/1.01  
% 2.45/1.01  fof(f31,plain,(
% 2.45/1.01    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.45/1.01    inference(flattening,[],[f30])).
% 2.45/1.01  
% 2.45/1.01  fof(f58,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f31])).
% 2.45/1.01  
% 2.45/1.01  fof(f8,axiom,(
% 2.45/1.01    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f24,plain,(
% 2.45/1.01    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.45/1.01    inference(ennf_transformation,[],[f8])).
% 2.45/1.01  
% 2.45/1.01  fof(f51,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f24])).
% 2.45/1.01  
% 2.45/1.01  fof(f6,axiom,(
% 2.45/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f22,plain,(
% 2.45/1.01    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 2.45/1.01    inference(ennf_transformation,[],[f6])).
% 2.45/1.01  
% 2.45/1.01  fof(f49,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f22])).
% 2.45/1.01  
% 2.45/1.01  fof(f71,plain,(
% 2.45/1.01    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) | ~v1_relat_1(X0)) )),
% 2.45/1.01    inference(definition_unfolding,[],[f49,f68])).
% 2.45/1.01  
% 2.45/1.01  fof(f17,axiom,(
% 2.45/1.01    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f36,plain,(
% 2.45/1.01    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.01    inference(ennf_transformation,[],[f17])).
% 2.45/1.01  
% 2.45/1.01  fof(f62,plain,(
% 2.45/1.01    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.01    inference(cnf_transformation,[],[f36])).
% 2.45/1.01  
% 2.45/1.01  fof(f66,plain,(
% 2.45/1.01    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.45/1.01    inference(cnf_transformation,[],[f42])).
% 2.45/1.01  
% 2.45/1.01  fof(f73,plain,(
% 2.45/1.01    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.45/1.01    inference(definition_unfolding,[],[f66,f68,f68])).
% 2.45/1.01  
% 2.45/1.01  fof(f7,axiom,(
% 2.45/1.01    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f23,plain,(
% 2.45/1.01    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.45/1.01    inference(ennf_transformation,[],[f7])).
% 2.45/1.01  
% 2.45/1.01  fof(f50,plain,(
% 2.45/1.01    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f23])).
% 2.45/1.01  
% 2.45/1.01  fof(f12,axiom,(
% 2.45/1.01    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f28,plain,(
% 2.45/1.01    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.45/1.01    inference(ennf_transformation,[],[f12])).
% 2.45/1.01  
% 2.45/1.01  fof(f29,plain,(
% 2.45/1.01    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.45/1.01    inference(flattening,[],[f28])).
% 2.45/1.01  
% 2.45/1.01  fof(f57,plain,(
% 2.45/1.01    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f29])).
% 2.45/1.01  
% 2.45/1.01  fof(f9,axiom,(
% 2.45/1.01    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f52,plain,(
% 2.45/1.01    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f9])).
% 2.45/1.01  
% 2.45/1.01  fof(f1,axiom,(
% 2.45/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f43,plain,(
% 2.45/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f1])).
% 2.45/1.01  
% 2.45/1.01  cnf(c_15,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v4_relat_1(X0,X1) ),
% 2.45/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_9,plain,
% 2.45/1.01      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.45/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_268,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.01      | ~ v1_relat_1(X0)
% 2.45/1.01      | k7_relat_1(X0,X1) = X0 ),
% 2.45/1.01      inference(resolution,[status(thm)],[c_15,c_9]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_14,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.45/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_272,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.01      | k7_relat_1(X0,X1) = X0 ),
% 2.45/1.01      inference(global_propositional_subsumption,
% 2.45/1.01                [status(thm)],
% 2.45/1.01                [c_268,c_15,c_14,c_9]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_19,negated_conjecture,
% 2.45/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.45/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_307,plain,
% 2.45/1.01      ( k7_relat_1(X0,X1) = X0
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.45/1.01      | sK3 != X0 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_272,c_19]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_308,plain,
% 2.45/1.01      ( k7_relat_1(sK3,X0) = sK3
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_307]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_976,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 2.45/1.01      | k7_relat_1(sK3,X0_49) = sK3 ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_308]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1543,plain,
% 2.45/1.01      ( k7_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = sK3 ),
% 2.45/1.01      inference(equality_resolution,[status(thm)],[c_976]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1,plain,
% 2.45/1.01      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 2.45/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_159,plain,
% 2.45/1.01      ( ~ r2_hidden(X0,X1) | r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) ),
% 2.45/1.01      inference(prop_impl,[status(thm)],[c_1]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_7,plain,
% 2.45/1.01      ( r2_hidden(X0,k1_relat_1(X1))
% 2.45/1.01      | ~ v1_relat_1(X1)
% 2.45/1.01      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 2.45/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_361,plain,
% 2.45/1.01      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
% 2.45/1.01      | ~ v1_relat_1(X2)
% 2.45/1.01      | X3 != X0
% 2.45/1.01      | k11_relat_1(X2,X3) = k1_xboole_0
% 2.45/1.01      | k1_relat_1(X2) != X1 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_159,c_7]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_362,plain,
% 2.45/1.01      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(X1))
% 2.45/1.01      | ~ v1_relat_1(X1)
% 2.45/1.01      | k11_relat_1(X1,X0) = k1_xboole_0 ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_361]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_325,plain,
% 2.45/1.01      ( v1_relat_1(X0)
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.45/1.01      | sK3 != X0 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_19]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_326,plain,
% 2.45/1.01      ( v1_relat_1(sK3)
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_325]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_599,plain,
% 2.45/1.01      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(X1))
% 2.45/1.01      | k11_relat_1(X1,X0) = k1_xboole_0
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.45/1.01      | sK3 != X1 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_362,c_326]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_600,plain,
% 2.45/1.01      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),k1_relat_1(sK3))
% 2.45/1.01      | k11_relat_1(sK3,X0) = k1_xboole_0
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_599]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_968,plain,
% 2.45/1.01      ( r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3))
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 2.45/1.01      | k11_relat_1(sK3,X0_52) = k1_xboole_0 ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_600]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_992,plain,
% 2.45/1.01      ( r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3))
% 2.45/1.01      | k11_relat_1(sK3,X0_52) = k1_xboole_0
% 2.45/1.01      | ~ sP5_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[sP5_iProver_split])],
% 2.45/1.01                [c_968]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1397,plain,
% 2.45/1.01      ( k11_relat_1(sK3,X0_52) = k1_xboole_0
% 2.45/1.01      | r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3)) = iProver_top
% 2.45/1.01      | sP5_iProver_split != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_993,plain,
% 2.45/1.01      ( sP5_iProver_split | sP1_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[])],
% 2.45/1.01                [c_968]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1065,plain,
% 2.45/1.01      ( sP5_iProver_split = iProver_top | sP1_iProver_split = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_993]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1066,plain,
% 2.45/1.01      ( k11_relat_1(sK3,X0_52) = k1_xboole_0
% 2.45/1.01      | r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3)) = iProver_top
% 2.45/1.01      | sP5_iProver_split != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_992]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1000,plain,( X0_50 = X0_50 ),theory(equality) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1550,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.45/1.01      inference(instantiation,[status(thm)],[c_1000]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_13,plain,
% 2.45/1.01      ( ~ v1_funct_1(X0)
% 2.45/1.01      | ~ v1_relat_1(X0)
% 2.45/1.01      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.45/1.01      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.45/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_20,negated_conjecture,
% 2.45/1.01      ( v1_funct_1(sK3) ),
% 2.45/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_288,plain,
% 2.45/1.01      ( ~ v1_relat_1(X0)
% 2.45/1.01      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.45/1.01      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.45/1.01      | sK3 != X0 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_20]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_289,plain,
% 2.45/1.01      ( ~ v1_relat_1(sK3)
% 2.45/1.01      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.45/1.01      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_288]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_534,plain,
% 2.45/1.01      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.45/1.01      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.45/1.01      inference(resolution,[status(thm)],[c_326,c_289]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_974,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 2.45/1.01      | k2_enumset1(X0_52,X0_52,X0_52,X0_52) != k1_relat_1(sK3)
% 2.45/1.01      | k2_enumset1(k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52)) = k2_relat_1(sK3) ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_534]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_982,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 2.45/1.01      | ~ sP1_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[sP1_iProver_split])],
% 2.45/1.01                [c_974]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1551,plain,
% 2.45/1.01      ( ~ sP1_iProver_split
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) ),
% 2.45/1.01      inference(instantiation,[status(thm)],[c_982]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1554,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
% 2.45/1.01      | sP1_iProver_split != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_1551]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2158,plain,
% 2.45/1.01      ( r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3)) = iProver_top
% 2.45/1.01      | k11_relat_1(sK3,X0_52) = k1_xboole_0 ),
% 2.45/1.01      inference(global_propositional_subsumption,
% 2.45/1.01                [status(thm)],
% 2.45/1.01                [c_1397,c_1065,c_1066,c_1550,c_1554]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2159,plain,
% 2.45/1.01      ( k11_relat_1(sK3,X0_52) = k1_xboole_0
% 2.45/1.01      | r1_tarski(k2_enumset1(X0_52,X0_52,X0_52,X0_52),k1_relat_1(sK3)) = iProver_top ),
% 2.45/1.01      inference(renaming,[status(thm)],[c_2158]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_12,plain,
% 2.45/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.45/1.01      | ~ v1_relat_1(X1)
% 2.45/1.01      | k1_relat_1(k7_relat_1(X1,X0)) = X0 ),
% 2.45/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_629,plain,
% 2.45/1.01      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.45/1.01      | k1_relat_1(k7_relat_1(X1,X0)) = X0
% 2.45/1.01      | sK3 != X1 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_326]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_630,plain,
% 2.45/1.01      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.45/1.01      | k1_relat_1(k7_relat_1(sK3,X0)) = X0 ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_629]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_966,plain,
% 2.45/1.01      ( ~ r1_tarski(X0_49,k1_relat_1(sK3))
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49))
% 2.45/1.01      | k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49 ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_630]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_996,plain,
% 2.45/1.01      ( ~ r1_tarski(X0_49,k1_relat_1(sK3))
% 2.45/1.01      | k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49
% 2.45/1.01      | ~ sP7_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[sP7_iProver_split])],
% 2.45/1.01                [c_966]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1403,plain,
% 2.45/1.01      ( k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49
% 2.45/1.01      | r1_tarski(X0_49,k1_relat_1(sK3)) != iProver_top
% 2.45/1.01      | sP7_iProver_split != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_997,plain,
% 2.45/1.01      ( sP7_iProver_split | sP1_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[])],
% 2.45/1.01                [c_966]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1075,plain,
% 2.45/1.01      ( sP7_iProver_split = iProver_top | sP1_iProver_split = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_997]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1076,plain,
% 2.45/1.01      ( k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49
% 2.45/1.01      | r1_tarski(X0_49,k1_relat_1(sK3)) != iProver_top
% 2.45/1.01      | sP7_iProver_split != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_996]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1813,plain,
% 2.45/1.01      ( r1_tarski(X0_49,k1_relat_1(sK3)) != iProver_top
% 2.45/1.01      | k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49 ),
% 2.45/1.01      inference(global_propositional_subsumption,
% 2.45/1.01                [status(thm)],
% 2.45/1.01                [c_1403,c_1075,c_1076,c_1550,c_1554]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1814,plain,
% 2.45/1.01      ( k1_relat_1(k7_relat_1(sK3,X0_49)) = X0_49
% 2.45/1.01      | r1_tarski(X0_49,k1_relat_1(sK3)) != iProver_top ),
% 2.45/1.01      inference(renaming,[status(thm)],[c_1813]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2166,plain,
% 2.45/1.01      ( k11_relat_1(sK3,X0_52) = k1_xboole_0
% 2.45/1.01      | k1_relat_1(k7_relat_1(sK3,k2_enumset1(X0_52,X0_52,X0_52,X0_52))) = k2_enumset1(X0_52,X0_52,X0_52,X0_52) ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_2159,c_1814]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2294,plain,
% 2.45/1.01      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.45/1.01      | k11_relat_1(sK3,sK0) = k1_xboole_0 ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_1543,c_2166]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_5,plain,
% 2.45/1.01      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.45/1.01      inference(cnf_transformation,[],[f51]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_569,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.45/1.01      | k2_relat_1(k7_relat_1(X2,X3)) = k9_relat_1(X2,X3)
% 2.45/1.01      | sK3 != X2 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_5,c_326]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_570,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.45/1.01      | k2_relat_1(k7_relat_1(sK3,X2)) = k9_relat_1(sK3,X2) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_569]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_971,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 2.45/1.01      | k2_relat_1(k7_relat_1(sK3,X2_49)) = k9_relat_1(sK3,X2_49) ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_570]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_986,plain,
% 2.45/1.01      ( k2_relat_1(k7_relat_1(sK3,X0_49)) = k9_relat_1(sK3,X0_49)
% 2.45/1.01      | ~ sP2_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 2.45/1.01                [c_971]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1389,plain,
% 2.45/1.01      ( k2_relat_1(k7_relat_1(sK3,X0_49)) = k9_relat_1(sK3,X0_49)
% 2.45/1.01      | sP2_iProver_split != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_986]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_987,plain,
% 2.45/1.01      ( sP2_iProver_split | sP1_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[])],
% 2.45/1.01                [c_971]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1574,plain,
% 2.45/1.01      ( k2_relat_1(k7_relat_1(sK3,X0_49)) = k9_relat_1(sK3,X0_49) ),
% 2.45/1.01      inference(global_propositional_subsumption,
% 2.45/1.01                [status(thm)],
% 2.45/1.01                [c_1389,c_987,c_986,c_1550,c_1551]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1578,plain,
% 2.45/1.01      ( k9_relat_1(sK3,k2_enumset1(sK0,sK0,sK0,sK0)) = k2_relat_1(sK3) ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_1543,c_1574]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_3,plain,
% 2.45/1.01      ( ~ v1_relat_1(X0)
% 2.45/1.01      | k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1) ),
% 2.45/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_590,plain,
% 2.45/1.01      ( k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) = k11_relat_1(X0,X1)
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.45/1.01      | sK3 != X0 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_3,c_326]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_591,plain,
% 2.45/1.01      ( k9_relat_1(sK3,k2_enumset1(X0,X0,X0,X0)) = k11_relat_1(sK3,X0)
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_590]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_969,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 2.45/1.01      | k9_relat_1(sK3,k2_enumset1(X0_52,X0_52,X0_52,X0_52)) = k11_relat_1(sK3,X0_52) ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_591]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_990,plain,
% 2.45/1.01      ( k9_relat_1(sK3,k2_enumset1(X0_52,X0_52,X0_52,X0_52)) = k11_relat_1(sK3,X0_52)
% 2.45/1.01      | ~ sP4_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[sP4_iProver_split])],
% 2.45/1.01                [c_969]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1395,plain,
% 2.45/1.01      ( k9_relat_1(sK3,k2_enumset1(X0_52,X0_52,X0_52,X0_52)) = k11_relat_1(sK3,X0_52)
% 2.45/1.01      | sP4_iProver_split != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_990]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_991,plain,
% 2.45/1.01      ( sP4_iProver_split | sP1_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[])],
% 2.45/1.01                [c_969]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1718,plain,
% 2.45/1.01      ( k9_relat_1(sK3,k2_enumset1(X0_52,X0_52,X0_52,X0_52)) = k11_relat_1(sK3,X0_52) ),
% 2.45/1.01      inference(global_propositional_subsumption,
% 2.45/1.01                [status(thm)],
% 2.45/1.01                [c_1395,c_991,c_990,c_1550,c_1551]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1722,plain,
% 2.45/1.01      ( k11_relat_1(sK3,sK0) = k2_relat_1(sK3) ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_1578,c_1718]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2295,plain,
% 2.45/1.01      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.45/1.01      | k2_relat_1(sK3) = k1_xboole_0 ),
% 2.45/1.01      inference(demodulation,[status(thm)],[c_2294,c_1722]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_981,plain,
% 2.45/1.01      ( k2_enumset1(X0_52,X0_52,X0_52,X0_52) != k1_relat_1(sK3)
% 2.45/1.01      | k2_enumset1(k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52)) = k2_relat_1(sK3)
% 2.45/1.01      | ~ sP0_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.45/1.01                [c_974]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1382,plain,
% 2.45/1.01      ( k2_enumset1(X0_52,X0_52,X0_52,X0_52) != k1_relat_1(sK3)
% 2.45/1.01      | k2_enumset1(k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52)) = k2_relat_1(sK3)
% 2.45/1.01      | sP0_iProver_split != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_981]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_983,plain,
% 2.45/1.01      ( sP1_iProver_split | sP0_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[])],
% 2.45/1.01                [c_974]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1871,plain,
% 2.45/1.01      ( k2_enumset1(k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52)) = k2_relat_1(sK3)
% 2.45/1.01      | k2_enumset1(X0_52,X0_52,X0_52,X0_52) != k1_relat_1(sK3) ),
% 2.45/1.01      inference(global_propositional_subsumption,
% 2.45/1.01                [status(thm)],
% 2.45/1.01                [c_1382,c_983,c_981,c_1550,c_1551]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1872,plain,
% 2.45/1.01      ( k2_enumset1(X0_52,X0_52,X0_52,X0_52) != k1_relat_1(sK3)
% 2.45/1.01      | k2_enumset1(k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52),k1_funct_1(sK3,X0_52)) = k2_relat_1(sK3) ),
% 2.45/1.01      inference(renaming,[status(thm)],[c_1871]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2305,plain,
% 2.45/1.01      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.45/1.01      | k2_relat_1(sK3) = k1_xboole_0 ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_2295,c_1872]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_16,plain,
% 2.45/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.01      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.45/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_316,plain,
% 2.45/1.01      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.45/1.01      | sK3 != X2 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_19]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_317,plain,
% 2.45/1.01      ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_316]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_975,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 2.45/1.01      | k7_relset_1(X0_49,X1_49,sK3,X2_49) = k9_relat_1(sK3,X2_49) ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_317]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1546,plain,
% 2.45/1.01      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0_49) = k9_relat_1(sK3,X0_49) ),
% 2.45/1.01      inference(equality_resolution,[status(thm)],[c_975]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_17,negated_conjecture,
% 2.45/1.01      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.45/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_978,negated_conjecture,
% 2.45/1.01      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1379,plain,
% 2.45/1.01      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_978]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1560,plain,
% 2.45/1.01      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.45/1.01      inference(demodulation,[status(thm)],[c_1546,c_1379]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2550,plain,
% 2.45/1.01      ( k2_relat_1(sK3) = k1_xboole_0
% 2.45/1.01      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 2.45/1.01      inference(superposition,[status(thm)],[c_2305,c_1560]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_4,plain,
% 2.45/1.01      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.45/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_578,plain,
% 2.45/1.01      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.45/1.01      | sK3 != X0 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_4,c_326]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_579,plain,
% 2.45/1.01      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2)) ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_578]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_970,plain,
% 2.45/1.01      ( r1_tarski(k9_relat_1(sK3,X0_49),k2_relat_1(sK3))
% 2.45/1.01      | k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1_49,X2_49)) ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_579]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_989,plain,
% 2.45/1.01      ( sP3_iProver_split | sP1_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[])],
% 2.45/1.01                [c_970]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1055,plain,
% 2.45/1.01      ( sP3_iProver_split = iProver_top | sP1_iProver_split = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_989]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_988,plain,
% 2.45/1.01      ( r1_tarski(k9_relat_1(sK3,X0_49),k2_relat_1(sK3))
% 2.45/1.01      | ~ sP3_iProver_split ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 2.45/1.01                [c_970]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2233,plain,
% 2.45/1.01      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ sP3_iProver_split ),
% 2.45/1.01      inference(instantiation,[status(thm)],[c_988]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2238,plain,
% 2.45/1.01      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) = iProver_top
% 2.45/1.01      | sP3_iProver_split != iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_2233]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2616,plain,
% 2.45/1.01      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 2.45/1.01      inference(global_propositional_subsumption,
% 2.45/1.01                [status(thm)],
% 2.45/1.01                [c_2550,c_1055,c_1550,c_1554,c_2238]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_10,plain,
% 2.45/1.01      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.45/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_557,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.45/1.01      | k2_relat_1(X2) != k1_xboole_0
% 2.45/1.01      | sK3 != X2
% 2.45/1.01      | k1_xboole_0 = X2 ),
% 2.45/1.01      inference(resolution_lifted,[status(thm)],[c_10,c_326]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_558,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.45/1.01      | k2_relat_1(sK3) != k1_xboole_0
% 2.45/1.01      | k1_xboole_0 = sK3 ),
% 2.45/1.01      inference(unflattening,[status(thm)],[c_557]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_972,plain,
% 2.45/1.01      ( k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0_49,X1_49))
% 2.45/1.01      | k2_relat_1(sK3) != k1_xboole_0
% 2.45/1.01      | k1_xboole_0 = sK3 ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_558]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_985,plain,
% 2.45/1.01      ( sP1_iProver_split
% 2.45/1.01      | k2_relat_1(sK3) != k1_xboole_0
% 2.45/1.01      | k1_xboole_0 = sK3 ),
% 2.45/1.01      inference(splitting,
% 2.45/1.01                [splitting(split),new_symbols(definition,[])],
% 2.45/1.01                [c_972]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1385,plain,
% 2.45/1.01      ( k2_relat_1(sK3) != k1_xboole_0
% 2.45/1.01      | k1_xboole_0 = sK3
% 2.45/1.01      | sP1_iProver_split = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_985]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2014,plain,
% 2.45/1.01      ( k1_xboole_0 = sK3 | k2_relat_1(sK3) != k1_xboole_0 ),
% 2.45/1.01      inference(global_propositional_subsumption,
% 2.45/1.01                [status(thm)],
% 2.45/1.01                [c_1385,c_985,c_1550,c_1551]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2015,plain,
% 2.45/1.01      ( k2_relat_1(sK3) != k1_xboole_0 | k1_xboole_0 = sK3 ),
% 2.45/1.01      inference(renaming,[status(thm)],[c_2014]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2627,plain,
% 2.45/1.01      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.45/1.01      inference(demodulation,[status(thm)],[c_2616,c_2015]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2639,plain,
% 2.45/1.01      ( sK3 = k1_xboole_0 ),
% 2.45/1.01      inference(equality_resolution_simp,[status(thm)],[c_2627]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2688,plain,
% 2.45/1.01      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.45/1.01      inference(demodulation,[status(thm)],[c_2639,c_1560]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_6,plain,
% 2.45/1.01      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.45/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_979,plain,
% 2.45/1.01      ( k9_relat_1(k1_xboole_0,X0_49) = k1_xboole_0 ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_2708,plain,
% 2.45/1.01      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.45/1.01      inference(demodulation,[status(thm)],[c_2688,c_979]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_0,plain,
% 2.45/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.45/1.01      inference(cnf_transformation,[],[f43]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_980,plain,
% 2.45/1.01      ( r1_tarski(k1_xboole_0,X0_49) ),
% 2.45/1.01      inference(subtyping,[status(esa)],[c_0]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_1378,plain,
% 2.45/1.01      ( r1_tarski(k1_xboole_0,X0_49) = iProver_top ),
% 2.45/1.01      inference(predicate_to_equality,[status(thm)],[c_980]) ).
% 2.45/1.01  
% 2.45/1.01  cnf(c_3028,plain,
% 2.45/1.01      ( $false ),
% 2.45/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_2708,c_1378]) ).
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/1.01  
% 2.45/1.01  ------                               Statistics
% 2.45/1.01  
% 2.45/1.01  ------ General
% 2.45/1.01  
% 2.45/1.01  abstr_ref_over_cycles:                  0
% 2.45/1.01  abstr_ref_under_cycles:                 0
% 2.45/1.01  gc_basic_clause_elim:                   0
% 2.45/1.01  forced_gc_time:                         0
% 2.45/1.01  parsing_time:                           0.009
% 2.45/1.01  unif_index_cands_time:                  0.
% 2.45/1.01  unif_index_add_time:                    0.
% 2.45/1.01  orderings_time:                         0.
% 2.45/1.01  out_proof_time:                         0.015
% 2.45/1.01  total_time:                             0.136
% 2.45/1.01  num_of_symbols:                         64
% 2.45/1.01  num_of_terms:                           2556
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing
% 2.45/1.01  
% 2.45/1.01  num_of_splits:                          16
% 2.45/1.01  num_of_split_atoms:                     8
% 2.45/1.01  num_of_reused_defs:                     8
% 2.45/1.01  num_eq_ax_congr_red:                    12
% 2.45/1.01  num_of_sem_filtered_clauses:            1
% 2.45/1.01  num_of_subtypes:                        4
% 2.45/1.01  monotx_restored_types:                  0
% 2.45/1.01  sat_num_of_epr_types:                   0
% 2.45/1.01  sat_num_of_non_cyclic_types:            0
% 2.45/1.01  sat_guarded_non_collapsed_types:        1
% 2.45/1.01  num_pure_diseq_elim:                    0
% 2.45/1.01  simp_replaced_by:                       0
% 2.45/1.01  res_preprocessed:                       117
% 2.45/1.01  prep_upred:                             0
% 2.45/1.01  prep_unflattend:                        34
% 2.45/1.01  smt_new_axioms:                         0
% 2.45/1.01  pred_elim_cands:                        1
% 2.45/1.01  pred_elim:                              5
% 2.45/1.01  pred_elim_cl:                           6
% 2.45/1.01  pred_elim_cycles:                       8
% 2.45/1.01  merged_defs:                            2
% 2.45/1.01  merged_defs_ncl:                        0
% 2.45/1.01  bin_hyper_res:                          2
% 2.45/1.01  prep_cycles:                            4
% 2.45/1.01  pred_elim_time:                         0.013
% 2.45/1.01  splitting_time:                         0.
% 2.45/1.01  sem_filter_time:                        0.
% 2.45/1.01  monotx_time:                            0.
% 2.45/1.01  subtype_inf_time:                       0.
% 2.45/1.01  
% 2.45/1.01  ------ Problem properties
% 2.45/1.01  
% 2.45/1.01  clauses:                                31
% 2.45/1.01  conjectures:                            2
% 2.45/1.01  epr:                                    9
% 2.45/1.01  horn:                                   21
% 2.45/1.01  ground:                                 11
% 2.45/1.01  unary:                                  4
% 2.45/1.01  binary:                                 21
% 2.45/1.01  lits:                                   64
% 2.45/1.01  lits_eq:                                26
% 2.45/1.01  fd_pure:                                0
% 2.45/1.01  fd_pseudo:                              0
% 2.45/1.01  fd_cond:                                0
% 2.45/1.01  fd_pseudo_cond:                         0
% 2.45/1.01  ac_symbols:                             0
% 2.45/1.01  
% 2.45/1.01  ------ Propositional Solver
% 2.45/1.01  
% 2.45/1.01  prop_solver_calls:                      28
% 2.45/1.01  prop_fast_solver_calls:                 778
% 2.45/1.01  smt_solver_calls:                       0
% 2.45/1.01  smt_fast_solver_calls:                  0
% 2.45/1.01  prop_num_of_clauses:                    901
% 2.45/1.01  prop_preprocess_simplified:             3586
% 2.45/1.01  prop_fo_subsumed:                       24
% 2.45/1.01  prop_solver_time:                       0.
% 2.45/1.01  smt_solver_time:                        0.
% 2.45/1.01  smt_fast_solver_time:                   0.
% 2.45/1.01  prop_fast_solver_time:                  0.
% 2.45/1.01  prop_unsat_core_time:                   0.
% 2.45/1.01  
% 2.45/1.01  ------ QBF
% 2.45/1.01  
% 2.45/1.01  qbf_q_res:                              0
% 2.45/1.01  qbf_num_tautologies:                    0
% 2.45/1.01  qbf_prep_cycles:                        0
% 2.45/1.01  
% 2.45/1.01  ------ BMC1
% 2.45/1.01  
% 2.45/1.01  bmc1_current_bound:                     -1
% 2.45/1.01  bmc1_last_solved_bound:                 -1
% 2.45/1.01  bmc1_unsat_core_size:                   -1
% 2.45/1.01  bmc1_unsat_core_parents_size:           -1
% 2.45/1.01  bmc1_merge_next_fun:                    0
% 2.45/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.45/1.01  
% 2.45/1.01  ------ Instantiation
% 2.45/1.01  
% 2.45/1.01  inst_num_of_clauses:                    310
% 2.45/1.01  inst_num_in_passive:                    33
% 2.45/1.01  inst_num_in_active:                     197
% 2.45/1.01  inst_num_in_unprocessed:                80
% 2.45/1.01  inst_num_of_loops:                      240
% 2.45/1.01  inst_num_of_learning_restarts:          0
% 2.45/1.01  inst_num_moves_active_passive:          39
% 2.45/1.01  inst_lit_activity:                      0
% 2.45/1.01  inst_lit_activity_moves:                0
% 2.45/1.01  inst_num_tautologies:                   0
% 2.45/1.01  inst_num_prop_implied:                  0
% 2.45/1.01  inst_num_existing_simplified:           0
% 2.45/1.01  inst_num_eq_res_simplified:             0
% 2.45/1.01  inst_num_child_elim:                    0
% 2.45/1.01  inst_num_of_dismatching_blockings:      44
% 2.45/1.01  inst_num_of_non_proper_insts:           296
% 2.45/1.01  inst_num_of_duplicates:                 0
% 2.45/1.01  inst_inst_num_from_inst_to_res:         0
% 2.45/1.01  inst_dismatching_checking_time:         0.
% 2.45/1.01  
% 2.45/1.01  ------ Resolution
% 2.45/1.01  
% 2.45/1.01  res_num_of_clauses:                     0
% 2.45/1.01  res_num_in_passive:                     0
% 2.45/1.01  res_num_in_active:                      0
% 2.45/1.01  res_num_of_loops:                       121
% 2.45/1.01  res_forward_subset_subsumed:            57
% 2.45/1.01  res_backward_subset_subsumed:           0
% 2.45/1.01  res_forward_subsumed:                   0
% 2.45/1.01  res_backward_subsumed:                  0
% 2.45/1.01  res_forward_subsumption_resolution:     0
% 2.45/1.01  res_backward_subsumption_resolution:    0
% 2.45/1.01  res_clause_to_clause_subsumption:       83
% 2.45/1.01  res_orphan_elimination:                 0
% 2.45/1.01  res_tautology_del:                      52
% 2.45/1.01  res_num_eq_res_simplified:              0
% 2.45/1.01  res_num_sel_changes:                    0
% 2.45/1.01  res_moves_from_active_to_pass:          0
% 2.45/1.01  
% 2.45/1.01  ------ Superposition
% 2.45/1.01  
% 2.45/1.01  sup_time_total:                         0.
% 2.45/1.01  sup_time_generating:                    0.
% 2.45/1.01  sup_time_sim_full:                      0.
% 2.45/1.01  sup_time_sim_immed:                     0.
% 2.45/1.01  
% 2.45/1.01  sup_num_of_clauses:                     29
% 2.45/1.01  sup_num_in_active:                      17
% 2.45/1.01  sup_num_in_passive:                     12
% 2.45/1.01  sup_num_of_loops:                       47
% 2.45/1.01  sup_fw_superposition:                   7
% 2.45/1.01  sup_bw_superposition:                   20
% 2.45/1.01  sup_immediate_simplified:               26
% 2.45/1.01  sup_given_eliminated:                   0
% 2.45/1.01  comparisons_done:                       0
% 2.45/1.01  comparisons_avoided:                    12
% 2.45/1.01  
% 2.45/1.01  ------ Simplifications
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  sim_fw_subset_subsumed:                 3
% 2.45/1.01  sim_bw_subset_subsumed:                 1
% 2.45/1.01  sim_fw_subsumed:                        3
% 2.45/1.01  sim_bw_subsumed:                        3
% 2.45/1.01  sim_fw_subsumption_res:                 1
% 2.45/1.01  sim_bw_subsumption_res:                 0
% 2.45/1.01  sim_tautology_del:                      0
% 2.45/1.01  sim_eq_tautology_del:                   5
% 2.45/1.01  sim_eq_res_simp:                        3
% 2.45/1.01  sim_fw_demodulated:                     6
% 2.45/1.01  sim_bw_demodulated:                     33
% 2.45/1.01  sim_light_normalised:                   9
% 2.45/1.01  sim_joinable_taut:                      0
% 2.45/1.01  sim_joinable_simp:                      0
% 2.45/1.01  sim_ac_normalised:                      0
% 2.45/1.01  sim_smt_subsumption:                    0
% 2.45/1.01  
%------------------------------------------------------------------------------
