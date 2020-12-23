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
% DateTime   : Thu Dec  3 12:05:53 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :  157 (1597 expanded)
%              Number of clauses        :   85 ( 457 expanded)
%              Number of leaves         :   20 ( 356 expanded)
%              Depth                    :   24
%              Number of atoms          :  382 (3708 expanded)
%              Number of equality atoms :  195 (1492 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
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

fof(f74,plain,(
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

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f77])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f74,f78])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

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

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f53,f78,f78])).

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

fof(f12,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f76,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f46])).

fof(f83,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f76,f78,f78])).

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

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f69,f78,f78])).

fof(f73,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

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

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f32])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_990,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_327,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_14])).

cnf(c_987,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_327])).

cnf(c_1371,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_987])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1001,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3095,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1371,c_1001])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_998,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1652,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_998])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_184,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_185,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_184])).

cnf(c_229,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_185])).

cnf(c_989,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_1852,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_989])).

cnf(c_15,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_997,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2302,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1852,c_997])).

cnf(c_3394,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3095,c_2302])).

cnf(c_3395,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3394])).

cnf(c_3409,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_990])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_29,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1193,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1283,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1193])).

cnf(c_16,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1513,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1515,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1513])).

cnf(c_523,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1218,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_523])).

cnf(c_1282,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1218])).

cnf(c_1514,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_1517,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1514])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_308,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_309,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_988,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_309])).

cnf(c_3400,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3395,c_988])).

cnf(c_3472,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3409,c_25,c_29,c_1283,c_1515,c_1517,c_2302,c_3400])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_994,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3496,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3472,c_994])).

cnf(c_3669,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3496,c_2302])).

cnf(c_996,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3703,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3669,c_996])).

cnf(c_4872,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3703,c_2302])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1000,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_1651,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1000,c_998])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1005,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2043,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1651,c_1005])).

cnf(c_4881,plain,
    ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4872,c_2043])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_992,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2838,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_990,c_992])).

cnf(c_3171,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2838,c_998])).

cnf(c_3229,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_3171])).

cnf(c_59,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_61,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_65,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_67,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_65])).

cnf(c_1693,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1694,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
    | r1_tarski(sK3,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1693])).

cnf(c_1696,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_3170,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_2838])).

cnf(c_3674,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3669,c_3170])).

cnf(c_3847,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3229,c_61,c_67,c_1696,c_3674])).

cnf(c_3854,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3847,c_2043])).

cnf(c_5693,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4881,c_3854])).

cnf(c_993,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2202,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_990,c_993])).

cnf(c_991,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2227,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2202,c_991])).

cnf(c_5520,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3854,c_2227])).

cnf(c_5697,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5693,c_5520])).

cnf(c_5930,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5697,c_1651])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:37:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.23/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/0.98  
% 3.23/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.23/0.98  
% 3.23/0.98  ------  iProver source info
% 3.23/0.98  
% 3.23/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.23/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.23/0.98  git: non_committed_changes: false
% 3.23/0.98  git: last_make_outside_of_git: false
% 3.23/0.98  
% 3.23/0.98  ------ 
% 3.23/0.98  
% 3.23/0.98  ------ Input Options
% 3.23/0.98  
% 3.23/0.98  --out_options                           all
% 3.23/0.98  --tptp_safe_out                         true
% 3.23/0.98  --problem_path                          ""
% 3.23/0.98  --include_path                          ""
% 3.23/0.98  --clausifier                            res/vclausify_rel
% 3.23/0.98  --clausifier_options                    --mode clausify
% 3.23/0.98  --stdin                                 false
% 3.23/0.98  --stats_out                             all
% 3.23/0.98  
% 3.23/0.98  ------ General Options
% 3.23/0.98  
% 3.23/0.98  --fof                                   false
% 3.23/0.98  --time_out_real                         305.
% 3.23/0.98  --time_out_virtual                      -1.
% 3.23/0.98  --symbol_type_check                     false
% 3.23/0.98  --clausify_out                          false
% 3.23/0.98  --sig_cnt_out                           false
% 3.23/0.98  --trig_cnt_out                          false
% 3.23/0.98  --trig_cnt_out_tolerance                1.
% 3.23/0.98  --trig_cnt_out_sk_spl                   false
% 3.23/0.98  --abstr_cl_out                          false
% 3.23/0.98  
% 3.23/0.98  ------ Global Options
% 3.23/0.98  
% 3.23/0.98  --schedule                              default
% 3.23/0.98  --add_important_lit                     false
% 3.23/0.98  --prop_solver_per_cl                    1000
% 3.23/0.98  --min_unsat_core                        false
% 3.23/0.98  --soft_assumptions                      false
% 3.23/0.98  --soft_lemma_size                       3
% 3.23/0.98  --prop_impl_unit_size                   0
% 3.23/0.98  --prop_impl_unit                        []
% 3.23/0.98  --share_sel_clauses                     true
% 3.23/0.98  --reset_solvers                         false
% 3.23/0.98  --bc_imp_inh                            [conj_cone]
% 3.23/0.98  --conj_cone_tolerance                   3.
% 3.23/0.98  --extra_neg_conj                        none
% 3.23/0.98  --large_theory_mode                     true
% 3.23/0.98  --prolific_symb_bound                   200
% 3.23/0.98  --lt_threshold                          2000
% 3.23/0.98  --clause_weak_htbl                      true
% 3.23/0.98  --gc_record_bc_elim                     false
% 3.23/0.98  
% 3.23/0.98  ------ Preprocessing Options
% 3.23/0.98  
% 3.23/0.98  --preprocessing_flag                    true
% 3.23/0.98  --time_out_prep_mult                    0.1
% 3.23/0.98  --splitting_mode                        input
% 3.23/0.98  --splitting_grd                         true
% 3.23/0.98  --splitting_cvd                         false
% 3.23/0.98  --splitting_cvd_svl                     false
% 3.23/0.98  --splitting_nvd                         32
% 3.23/0.98  --sub_typing                            true
% 3.23/0.98  --prep_gs_sim                           true
% 3.23/0.98  --prep_unflatten                        true
% 3.23/0.98  --prep_res_sim                          true
% 3.23/0.98  --prep_upred                            true
% 3.23/0.98  --prep_sem_filter                       exhaustive
% 3.23/0.98  --prep_sem_filter_out                   false
% 3.23/0.98  --pred_elim                             true
% 3.23/0.98  --res_sim_input                         true
% 3.23/0.98  --eq_ax_congr_red                       true
% 3.23/0.98  --pure_diseq_elim                       true
% 3.23/0.98  --brand_transform                       false
% 3.23/0.98  --non_eq_to_eq                          false
% 3.23/0.98  --prep_def_merge                        true
% 3.23/0.98  --prep_def_merge_prop_impl              false
% 3.23/0.98  --prep_def_merge_mbd                    true
% 3.23/0.98  --prep_def_merge_tr_red                 false
% 3.23/0.98  --prep_def_merge_tr_cl                  false
% 3.23/0.98  --smt_preprocessing                     true
% 3.23/0.98  --smt_ac_axioms                         fast
% 3.23/0.98  --preprocessed_out                      false
% 3.23/0.98  --preprocessed_stats                    false
% 3.23/0.98  
% 3.23/0.98  ------ Abstraction refinement Options
% 3.23/0.98  
% 3.23/0.98  --abstr_ref                             []
% 3.23/0.98  --abstr_ref_prep                        false
% 3.23/0.98  --abstr_ref_until_sat                   false
% 3.23/0.98  --abstr_ref_sig_restrict                funpre
% 3.23/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/0.98  --abstr_ref_under                       []
% 3.23/0.98  
% 3.23/0.98  ------ SAT Options
% 3.23/0.98  
% 3.23/0.98  --sat_mode                              false
% 3.23/0.98  --sat_fm_restart_options                ""
% 3.23/0.98  --sat_gr_def                            false
% 3.23/0.98  --sat_epr_types                         true
% 3.23/0.98  --sat_non_cyclic_types                  false
% 3.23/0.98  --sat_finite_models                     false
% 3.23/0.98  --sat_fm_lemmas                         false
% 3.23/0.98  --sat_fm_prep                           false
% 3.23/0.98  --sat_fm_uc_incr                        true
% 3.23/0.98  --sat_out_model                         small
% 3.23/0.98  --sat_out_clauses                       false
% 3.23/0.98  
% 3.23/0.98  ------ QBF Options
% 3.23/0.98  
% 3.23/0.98  --qbf_mode                              false
% 3.23/0.98  --qbf_elim_univ                         false
% 3.23/0.98  --qbf_dom_inst                          none
% 3.23/0.98  --qbf_dom_pre_inst                      false
% 3.23/0.98  --qbf_sk_in                             false
% 3.23/0.98  --qbf_pred_elim                         true
% 3.23/0.98  --qbf_split                             512
% 3.23/0.98  
% 3.23/0.98  ------ BMC1 Options
% 3.23/0.98  
% 3.23/0.98  --bmc1_incremental                      false
% 3.23/0.98  --bmc1_axioms                           reachable_all
% 3.23/0.98  --bmc1_min_bound                        0
% 3.23/0.98  --bmc1_max_bound                        -1
% 3.23/0.98  --bmc1_max_bound_default                -1
% 3.23/0.98  --bmc1_symbol_reachability              true
% 3.23/0.98  --bmc1_property_lemmas                  false
% 3.23/0.98  --bmc1_k_induction                      false
% 3.23/0.98  --bmc1_non_equiv_states                 false
% 3.23/0.98  --bmc1_deadlock                         false
% 3.23/0.98  --bmc1_ucm                              false
% 3.23/0.98  --bmc1_add_unsat_core                   none
% 3.23/0.98  --bmc1_unsat_core_children              false
% 3.23/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/0.98  --bmc1_out_stat                         full
% 3.23/0.98  --bmc1_ground_init                      false
% 3.23/0.98  --bmc1_pre_inst_next_state              false
% 3.23/0.98  --bmc1_pre_inst_state                   false
% 3.23/0.98  --bmc1_pre_inst_reach_state             false
% 3.23/0.98  --bmc1_out_unsat_core                   false
% 3.23/0.98  --bmc1_aig_witness_out                  false
% 3.23/0.98  --bmc1_verbose                          false
% 3.23/0.98  --bmc1_dump_clauses_tptp                false
% 3.23/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.23/0.98  --bmc1_dump_file                        -
% 3.23/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.23/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.23/0.98  --bmc1_ucm_extend_mode                  1
% 3.23/0.98  --bmc1_ucm_init_mode                    2
% 3.23/0.98  --bmc1_ucm_cone_mode                    none
% 3.23/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.23/0.98  --bmc1_ucm_relax_model                  4
% 3.23/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.23/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/0.98  --bmc1_ucm_layered_model                none
% 3.23/0.98  --bmc1_ucm_max_lemma_size               10
% 3.23/0.98  
% 3.23/0.98  ------ AIG Options
% 3.23/0.98  
% 3.23/0.98  --aig_mode                              false
% 3.23/0.98  
% 3.23/0.98  ------ Instantiation Options
% 3.23/0.98  
% 3.23/0.98  --instantiation_flag                    true
% 3.23/0.98  --inst_sos_flag                         false
% 3.23/0.98  --inst_sos_phase                        true
% 3.23/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/0.98  --inst_lit_sel_side                     num_symb
% 3.23/0.98  --inst_solver_per_active                1400
% 3.23/0.98  --inst_solver_calls_frac                1.
% 3.23/0.98  --inst_passive_queue_type               priority_queues
% 3.23/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/0.98  --inst_passive_queues_freq              [25;2]
% 3.23/0.98  --inst_dismatching                      true
% 3.23/0.98  --inst_eager_unprocessed_to_passive     true
% 3.23/0.98  --inst_prop_sim_given                   true
% 3.23/0.98  --inst_prop_sim_new                     false
% 3.23/0.98  --inst_subs_new                         false
% 3.23/0.98  --inst_eq_res_simp                      false
% 3.23/0.98  --inst_subs_given                       false
% 3.23/0.98  --inst_orphan_elimination               true
% 3.23/0.98  --inst_learning_loop_flag               true
% 3.23/0.98  --inst_learning_start                   3000
% 3.23/0.98  --inst_learning_factor                  2
% 3.23/0.98  --inst_start_prop_sim_after_learn       3
% 3.23/0.98  --inst_sel_renew                        solver
% 3.23/0.98  --inst_lit_activity_flag                true
% 3.23/0.98  --inst_restr_to_given                   false
% 3.23/0.98  --inst_activity_threshold               500
% 3.23/0.98  --inst_out_proof                        true
% 3.23/0.98  
% 3.23/0.98  ------ Resolution Options
% 3.23/0.98  
% 3.23/0.98  --resolution_flag                       true
% 3.23/0.98  --res_lit_sel                           adaptive
% 3.23/0.98  --res_lit_sel_side                      none
% 3.23/0.98  --res_ordering                          kbo
% 3.23/0.98  --res_to_prop_solver                    active
% 3.23/0.98  --res_prop_simpl_new                    false
% 3.23/0.98  --res_prop_simpl_given                  true
% 3.23/0.98  --res_passive_queue_type                priority_queues
% 3.23/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/0.98  --res_passive_queues_freq               [15;5]
% 3.23/0.98  --res_forward_subs                      full
% 3.23/0.98  --res_backward_subs                     full
% 3.23/0.98  --res_forward_subs_resolution           true
% 3.23/0.98  --res_backward_subs_resolution          true
% 3.23/0.98  --res_orphan_elimination                true
% 3.23/0.98  --res_time_limit                        2.
% 3.23/0.98  --res_out_proof                         true
% 3.23/0.98  
% 3.23/0.98  ------ Superposition Options
% 3.23/0.98  
% 3.23/0.98  --superposition_flag                    true
% 3.23/0.98  --sup_passive_queue_type                priority_queues
% 3.23/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.23/0.98  --demod_completeness_check              fast
% 3.23/0.98  --demod_use_ground                      true
% 3.23/0.98  --sup_to_prop_solver                    passive
% 3.23/0.98  --sup_prop_simpl_new                    true
% 3.23/0.98  --sup_prop_simpl_given                  true
% 3.23/0.98  --sup_fun_splitting                     false
% 3.23/0.98  --sup_smt_interval                      50000
% 3.23/0.98  
% 3.23/0.98  ------ Superposition Simplification Setup
% 3.23/0.98  
% 3.23/0.98  --sup_indices_passive                   []
% 3.23/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.98  --sup_full_bw                           [BwDemod]
% 3.23/0.98  --sup_immed_triv                        [TrivRules]
% 3.23/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.98  --sup_immed_bw_main                     []
% 3.23/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.98  
% 3.23/0.98  ------ Combination Options
% 3.23/0.98  
% 3.23/0.98  --comb_res_mult                         3
% 3.23/0.98  --comb_sup_mult                         2
% 3.23/0.98  --comb_inst_mult                        10
% 3.23/0.98  
% 3.23/0.98  ------ Debug Options
% 3.23/0.98  
% 3.23/0.98  --dbg_backtrace                         false
% 3.23/0.98  --dbg_dump_prop_clauses                 false
% 3.23/0.98  --dbg_dump_prop_clauses_file            -
% 3.23/0.98  --dbg_out_stat                          false
% 3.23/0.98  ------ Parsing...
% 3.23/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.23/0.98  
% 3.23/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.23/0.98  
% 3.23/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.23/0.98  
% 3.23/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.23/0.98  ------ Proving...
% 3.23/0.98  ------ Problem Properties 
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  clauses                                 23
% 3.23/0.98  conjectures                             3
% 3.23/0.98  EPR                                     4
% 3.23/0.98  Horn                                    21
% 3.23/0.98  unary                                   10
% 3.23/0.98  binary                                  4
% 3.23/0.98  lits                                    45
% 3.23/0.98  lits eq                                 16
% 3.23/0.98  fd_pure                                 0
% 3.23/0.98  fd_pseudo                               0
% 3.23/0.98  fd_cond                                 1
% 3.23/0.98  fd_pseudo_cond                          2
% 3.23/0.98  AC symbols                              0
% 3.23/0.98  
% 3.23/0.98  ------ Schedule dynamic 5 is on 
% 3.23/0.98  
% 3.23/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  ------ 
% 3.23/0.98  Current options:
% 3.23/0.98  ------ 
% 3.23/0.98  
% 3.23/0.98  ------ Input Options
% 3.23/0.98  
% 3.23/0.98  --out_options                           all
% 3.23/0.98  --tptp_safe_out                         true
% 3.23/0.98  --problem_path                          ""
% 3.23/0.98  --include_path                          ""
% 3.23/0.98  --clausifier                            res/vclausify_rel
% 3.23/0.98  --clausifier_options                    --mode clausify
% 3.23/0.98  --stdin                                 false
% 3.23/0.98  --stats_out                             all
% 3.23/0.98  
% 3.23/0.98  ------ General Options
% 3.23/0.98  
% 3.23/0.98  --fof                                   false
% 3.23/0.98  --time_out_real                         305.
% 3.23/0.98  --time_out_virtual                      -1.
% 3.23/0.98  --symbol_type_check                     false
% 3.23/0.98  --clausify_out                          false
% 3.23/0.98  --sig_cnt_out                           false
% 3.23/0.98  --trig_cnt_out                          false
% 3.23/0.98  --trig_cnt_out_tolerance                1.
% 3.23/0.98  --trig_cnt_out_sk_spl                   false
% 3.23/0.98  --abstr_cl_out                          false
% 3.23/0.98  
% 3.23/0.98  ------ Global Options
% 3.23/0.98  
% 3.23/0.98  --schedule                              default
% 3.23/0.98  --add_important_lit                     false
% 3.23/0.98  --prop_solver_per_cl                    1000
% 3.23/0.98  --min_unsat_core                        false
% 3.23/0.98  --soft_assumptions                      false
% 3.23/0.98  --soft_lemma_size                       3
% 3.23/0.98  --prop_impl_unit_size                   0
% 3.23/0.98  --prop_impl_unit                        []
% 3.23/0.98  --share_sel_clauses                     true
% 3.23/0.98  --reset_solvers                         false
% 3.23/0.98  --bc_imp_inh                            [conj_cone]
% 3.23/0.98  --conj_cone_tolerance                   3.
% 3.23/0.98  --extra_neg_conj                        none
% 3.23/0.98  --large_theory_mode                     true
% 3.23/0.98  --prolific_symb_bound                   200
% 3.23/0.98  --lt_threshold                          2000
% 3.23/0.98  --clause_weak_htbl                      true
% 3.23/0.98  --gc_record_bc_elim                     false
% 3.23/0.98  
% 3.23/0.98  ------ Preprocessing Options
% 3.23/0.98  
% 3.23/0.98  --preprocessing_flag                    true
% 3.23/0.98  --time_out_prep_mult                    0.1
% 3.23/0.98  --splitting_mode                        input
% 3.23/0.98  --splitting_grd                         true
% 3.23/0.98  --splitting_cvd                         false
% 3.23/0.98  --splitting_cvd_svl                     false
% 3.23/0.98  --splitting_nvd                         32
% 3.23/0.98  --sub_typing                            true
% 3.23/0.98  --prep_gs_sim                           true
% 3.23/0.98  --prep_unflatten                        true
% 3.23/0.98  --prep_res_sim                          true
% 3.23/0.98  --prep_upred                            true
% 3.23/0.98  --prep_sem_filter                       exhaustive
% 3.23/0.98  --prep_sem_filter_out                   false
% 3.23/0.98  --pred_elim                             true
% 3.23/0.98  --res_sim_input                         true
% 3.23/0.98  --eq_ax_congr_red                       true
% 3.23/0.98  --pure_diseq_elim                       true
% 3.23/0.98  --brand_transform                       false
% 3.23/0.98  --non_eq_to_eq                          false
% 3.23/0.98  --prep_def_merge                        true
% 3.23/0.98  --prep_def_merge_prop_impl              false
% 3.23/0.98  --prep_def_merge_mbd                    true
% 3.23/0.98  --prep_def_merge_tr_red                 false
% 3.23/0.98  --prep_def_merge_tr_cl                  false
% 3.23/0.98  --smt_preprocessing                     true
% 3.23/0.98  --smt_ac_axioms                         fast
% 3.23/0.98  --preprocessed_out                      false
% 3.23/0.98  --preprocessed_stats                    false
% 3.23/0.98  
% 3.23/0.98  ------ Abstraction refinement Options
% 3.23/0.98  
% 3.23/0.98  --abstr_ref                             []
% 3.23/0.98  --abstr_ref_prep                        false
% 3.23/0.98  --abstr_ref_until_sat                   false
% 3.23/0.98  --abstr_ref_sig_restrict                funpre
% 3.23/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.23/0.98  --abstr_ref_under                       []
% 3.23/0.98  
% 3.23/0.98  ------ SAT Options
% 3.23/0.98  
% 3.23/0.98  --sat_mode                              false
% 3.23/0.98  --sat_fm_restart_options                ""
% 3.23/0.98  --sat_gr_def                            false
% 3.23/0.98  --sat_epr_types                         true
% 3.23/0.98  --sat_non_cyclic_types                  false
% 3.23/0.98  --sat_finite_models                     false
% 3.23/0.98  --sat_fm_lemmas                         false
% 3.23/0.98  --sat_fm_prep                           false
% 3.23/0.98  --sat_fm_uc_incr                        true
% 3.23/0.98  --sat_out_model                         small
% 3.23/0.98  --sat_out_clauses                       false
% 3.23/0.98  
% 3.23/0.98  ------ QBF Options
% 3.23/0.98  
% 3.23/0.98  --qbf_mode                              false
% 3.23/0.98  --qbf_elim_univ                         false
% 3.23/0.98  --qbf_dom_inst                          none
% 3.23/0.98  --qbf_dom_pre_inst                      false
% 3.23/0.98  --qbf_sk_in                             false
% 3.23/0.98  --qbf_pred_elim                         true
% 3.23/0.98  --qbf_split                             512
% 3.23/0.98  
% 3.23/0.98  ------ BMC1 Options
% 3.23/0.98  
% 3.23/0.98  --bmc1_incremental                      false
% 3.23/0.98  --bmc1_axioms                           reachable_all
% 3.23/0.98  --bmc1_min_bound                        0
% 3.23/0.98  --bmc1_max_bound                        -1
% 3.23/0.98  --bmc1_max_bound_default                -1
% 3.23/0.98  --bmc1_symbol_reachability              true
% 3.23/0.98  --bmc1_property_lemmas                  false
% 3.23/0.98  --bmc1_k_induction                      false
% 3.23/0.98  --bmc1_non_equiv_states                 false
% 3.23/0.98  --bmc1_deadlock                         false
% 3.23/0.98  --bmc1_ucm                              false
% 3.23/0.98  --bmc1_add_unsat_core                   none
% 3.23/0.98  --bmc1_unsat_core_children              false
% 3.23/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.23/0.98  --bmc1_out_stat                         full
% 3.23/0.98  --bmc1_ground_init                      false
% 3.23/0.98  --bmc1_pre_inst_next_state              false
% 3.23/0.98  --bmc1_pre_inst_state                   false
% 3.23/0.98  --bmc1_pre_inst_reach_state             false
% 3.23/0.98  --bmc1_out_unsat_core                   false
% 3.23/0.98  --bmc1_aig_witness_out                  false
% 3.23/0.98  --bmc1_verbose                          false
% 3.23/0.98  --bmc1_dump_clauses_tptp                false
% 3.23/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.23/0.98  --bmc1_dump_file                        -
% 3.23/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.23/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.23/0.98  --bmc1_ucm_extend_mode                  1
% 3.23/0.98  --bmc1_ucm_init_mode                    2
% 3.23/0.98  --bmc1_ucm_cone_mode                    none
% 3.23/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.23/0.98  --bmc1_ucm_relax_model                  4
% 3.23/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.23/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.23/0.98  --bmc1_ucm_layered_model                none
% 3.23/0.98  --bmc1_ucm_max_lemma_size               10
% 3.23/0.98  
% 3.23/0.98  ------ AIG Options
% 3.23/0.98  
% 3.23/0.98  --aig_mode                              false
% 3.23/0.98  
% 3.23/0.98  ------ Instantiation Options
% 3.23/0.98  
% 3.23/0.98  --instantiation_flag                    true
% 3.23/0.98  --inst_sos_flag                         false
% 3.23/0.98  --inst_sos_phase                        true
% 3.23/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.23/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.23/0.98  --inst_lit_sel_side                     none
% 3.23/0.98  --inst_solver_per_active                1400
% 3.23/0.98  --inst_solver_calls_frac                1.
% 3.23/0.98  --inst_passive_queue_type               priority_queues
% 3.23/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.23/0.98  --inst_passive_queues_freq              [25;2]
% 3.23/0.98  --inst_dismatching                      true
% 3.23/0.98  --inst_eager_unprocessed_to_passive     true
% 3.23/0.98  --inst_prop_sim_given                   true
% 3.23/0.98  --inst_prop_sim_new                     false
% 3.23/0.98  --inst_subs_new                         false
% 3.23/0.98  --inst_eq_res_simp                      false
% 3.23/0.98  --inst_subs_given                       false
% 3.23/0.98  --inst_orphan_elimination               true
% 3.23/0.98  --inst_learning_loop_flag               true
% 3.23/0.98  --inst_learning_start                   3000
% 3.23/0.98  --inst_learning_factor                  2
% 3.23/0.98  --inst_start_prop_sim_after_learn       3
% 3.23/0.98  --inst_sel_renew                        solver
% 3.23/0.98  --inst_lit_activity_flag                true
% 3.23/0.98  --inst_restr_to_given                   false
% 3.23/0.98  --inst_activity_threshold               500
% 3.23/0.98  --inst_out_proof                        true
% 3.23/0.98  
% 3.23/0.98  ------ Resolution Options
% 3.23/0.98  
% 3.23/0.98  --resolution_flag                       false
% 3.23/0.98  --res_lit_sel                           adaptive
% 3.23/0.98  --res_lit_sel_side                      none
% 3.23/0.98  --res_ordering                          kbo
% 3.23/0.98  --res_to_prop_solver                    active
% 3.23/0.98  --res_prop_simpl_new                    false
% 3.23/0.98  --res_prop_simpl_given                  true
% 3.23/0.98  --res_passive_queue_type                priority_queues
% 3.23/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.23/0.98  --res_passive_queues_freq               [15;5]
% 3.23/0.98  --res_forward_subs                      full
% 3.23/0.98  --res_backward_subs                     full
% 3.23/0.98  --res_forward_subs_resolution           true
% 3.23/0.98  --res_backward_subs_resolution          true
% 3.23/0.98  --res_orphan_elimination                true
% 3.23/0.98  --res_time_limit                        2.
% 3.23/0.98  --res_out_proof                         true
% 3.23/0.98  
% 3.23/0.98  ------ Superposition Options
% 3.23/0.98  
% 3.23/0.98  --superposition_flag                    true
% 3.23/0.98  --sup_passive_queue_type                priority_queues
% 3.23/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.23/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.23/0.98  --demod_completeness_check              fast
% 3.23/0.98  --demod_use_ground                      true
% 3.23/0.98  --sup_to_prop_solver                    passive
% 3.23/0.98  --sup_prop_simpl_new                    true
% 3.23/0.98  --sup_prop_simpl_given                  true
% 3.23/0.98  --sup_fun_splitting                     false
% 3.23/0.98  --sup_smt_interval                      50000
% 3.23/0.98  
% 3.23/0.98  ------ Superposition Simplification Setup
% 3.23/0.98  
% 3.23/0.98  --sup_indices_passive                   []
% 3.23/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.23/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.23/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.98  --sup_full_bw                           [BwDemod]
% 3.23/0.98  --sup_immed_triv                        [TrivRules]
% 3.23/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.23/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.98  --sup_immed_bw_main                     []
% 3.23/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.23/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.23/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.23/0.98  
% 3.23/0.98  ------ Combination Options
% 3.23/0.98  
% 3.23/0.98  --comb_res_mult                         3
% 3.23/0.98  --comb_sup_mult                         2
% 3.23/0.98  --comb_inst_mult                        10
% 3.23/0.98  
% 3.23/0.98  ------ Debug Options
% 3.23/0.98  
% 3.23/0.98  --dbg_backtrace                         false
% 3.23/0.98  --dbg_dump_prop_clauses                 false
% 3.23/0.98  --dbg_dump_prop_clauses_file            -
% 3.23/0.98  --dbg_out_stat                          false
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  ------ Proving...
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  % SZS status Theorem for theBenchmark.p
% 3.23/0.98  
% 3.23/0.98   Resolution empty clause
% 3.23/0.98  
% 3.23/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.23/0.98  
% 3.23/0.98  fof(f19,conjecture,(
% 3.23/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f20,negated_conjecture,(
% 3.23/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.23/0.98    inference(negated_conjecture,[],[f19])).
% 3.23/0.98  
% 3.23/0.98  fof(f21,plain,(
% 3.23/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.23/0.98    inference(pure_predicate_removal,[],[f20])).
% 3.23/0.98  
% 3.23/0.98  fof(f34,plain,(
% 3.23/0.98    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 3.23/0.98    inference(ennf_transformation,[],[f21])).
% 3.23/0.98  
% 3.23/0.98  fof(f35,plain,(
% 3.23/0.98    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 3.23/0.98    inference(flattening,[],[f34])).
% 3.23/0.98  
% 3.23/0.98  fof(f45,plain,(
% 3.23/0.98    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 3.23/0.98    introduced(choice_axiom,[])).
% 3.23/0.98  
% 3.23/0.98  fof(f46,plain,(
% 3.23/0.98    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 3.23/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f35,f45])).
% 3.23/0.98  
% 3.23/0.98  fof(f74,plain,(
% 3.23/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.23/0.98    inference(cnf_transformation,[],[f46])).
% 3.23/0.98  
% 3.23/0.98  fof(f2,axiom,(
% 3.23/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f50,plain,(
% 3.23/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f2])).
% 3.23/0.98  
% 3.23/0.98  fof(f3,axiom,(
% 3.23/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f51,plain,(
% 3.23/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f3])).
% 3.23/0.98  
% 3.23/0.98  fof(f4,axiom,(
% 3.23/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f52,plain,(
% 3.23/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f4])).
% 3.23/0.98  
% 3.23/0.98  fof(f77,plain,(
% 3.23/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.23/0.98    inference(definition_unfolding,[],[f51,f52])).
% 3.23/0.98  
% 3.23/0.98  fof(f78,plain,(
% 3.23/0.98    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.23/0.98    inference(definition_unfolding,[],[f50,f77])).
% 3.23/0.98  
% 3.23/0.98  fof(f84,plain,(
% 3.23/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 3.23/0.98    inference(definition_unfolding,[],[f74,f78])).
% 3.23/0.98  
% 3.23/0.98  fof(f16,axiom,(
% 3.23/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f22,plain,(
% 3.23/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.23/0.98    inference(pure_predicate_removal,[],[f16])).
% 3.23/0.98  
% 3.23/0.98  fof(f30,plain,(
% 3.23/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.98    inference(ennf_transformation,[],[f22])).
% 3.23/0.98  
% 3.23/0.98  fof(f70,plain,(
% 3.23/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.98    inference(cnf_transformation,[],[f30])).
% 3.23/0.98  
% 3.23/0.98  fof(f11,axiom,(
% 3.23/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f25,plain,(
% 3.23/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.23/0.98    inference(ennf_transformation,[],[f11])).
% 3.23/0.98  
% 3.23/0.98  fof(f43,plain,(
% 3.23/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.23/0.98    inference(nnf_transformation,[],[f25])).
% 3.23/0.98  
% 3.23/0.98  fof(f63,plain,(
% 3.23/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f43])).
% 3.23/0.98  
% 3.23/0.98  fof(f5,axiom,(
% 3.23/0.98    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f38,plain,(
% 3.23/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.23/0.98    inference(nnf_transformation,[],[f5])).
% 3.23/0.98  
% 3.23/0.98  fof(f39,plain,(
% 3.23/0.98    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.23/0.98    inference(flattening,[],[f38])).
% 3.23/0.98  
% 3.23/0.98  fof(f53,plain,(
% 3.23/0.98    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.23/0.98    inference(cnf_transformation,[],[f39])).
% 3.23/0.98  
% 3.23/0.98  fof(f81,plain,(
% 3.23/0.98    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.23/0.98    inference(definition_unfolding,[],[f53,f78,f78])).
% 3.23/0.98  
% 3.23/0.98  fof(f8,axiom,(
% 3.23/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f42,plain,(
% 3.23/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.23/0.98    inference(nnf_transformation,[],[f8])).
% 3.23/0.98  
% 3.23/0.98  fof(f60,plain,(
% 3.23/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.23/0.98    inference(cnf_transformation,[],[f42])).
% 3.23/0.98  
% 3.23/0.98  fof(f10,axiom,(
% 3.23/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f24,plain,(
% 3.23/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.23/0.98    inference(ennf_transformation,[],[f10])).
% 3.23/0.98  
% 3.23/0.98  fof(f62,plain,(
% 3.23/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f24])).
% 3.23/0.98  
% 3.23/0.98  fof(f61,plain,(
% 3.23/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f42])).
% 3.23/0.98  
% 3.23/0.98  fof(f12,axiom,(
% 3.23/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f65,plain,(
% 3.23/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.23/0.98    inference(cnf_transformation,[],[f12])).
% 3.23/0.98  
% 3.23/0.98  fof(f76,plain,(
% 3.23/0.98    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 3.23/0.98    inference(cnf_transformation,[],[f46])).
% 3.23/0.98  
% 3.23/0.98  fof(f83,plain,(
% 3.23/0.98    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 3.23/0.98    inference(definition_unfolding,[],[f76,f78,f78])).
% 3.23/0.98  
% 3.23/0.98  fof(f17,axiom,(
% 3.23/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f31,plain,(
% 3.23/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.23/0.98    inference(ennf_transformation,[],[f17])).
% 3.23/0.98  
% 3.23/0.98  fof(f71,plain,(
% 3.23/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.23/0.98    inference(cnf_transformation,[],[f31])).
% 3.23/0.98  
% 3.23/0.98  fof(f13,axiom,(
% 3.23/0.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f26,plain,(
% 3.23/0.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.23/0.98    inference(ennf_transformation,[],[f13])).
% 3.23/0.98  
% 3.23/0.98  fof(f66,plain,(
% 3.23/0.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f26])).
% 3.23/0.98  
% 3.23/0.98  fof(f15,axiom,(
% 3.23/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f28,plain,(
% 3.23/0.98    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.23/0.98    inference(ennf_transformation,[],[f15])).
% 3.23/0.98  
% 3.23/0.98  fof(f29,plain,(
% 3.23/0.98    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.23/0.98    inference(flattening,[],[f28])).
% 3.23/0.98  
% 3.23/0.98  fof(f69,plain,(
% 3.23/0.98    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f29])).
% 3.23/0.98  
% 3.23/0.98  fof(f82,plain,(
% 3.23/0.98    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.23/0.98    inference(definition_unfolding,[],[f69,f78,f78])).
% 3.23/0.98  
% 3.23/0.98  fof(f73,plain,(
% 3.23/0.98    v1_funct_1(sK3)),
% 3.23/0.98    inference(cnf_transformation,[],[f46])).
% 3.23/0.98  
% 3.23/0.98  fof(f14,axiom,(
% 3.23/0.98    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f27,plain,(
% 3.23/0.98    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.23/0.98    inference(ennf_transformation,[],[f14])).
% 3.23/0.98  
% 3.23/0.98  fof(f44,plain,(
% 3.23/0.98    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.23/0.98    inference(nnf_transformation,[],[f27])).
% 3.23/0.98  
% 3.23/0.98  fof(f67,plain,(
% 3.23/0.98    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f44])).
% 3.23/0.98  
% 3.23/0.98  fof(f7,axiom,(
% 3.23/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f59,plain,(
% 3.23/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.23/0.98    inference(cnf_transformation,[],[f7])).
% 3.23/0.98  
% 3.23/0.98  fof(f1,axiom,(
% 3.23/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f36,plain,(
% 3.23/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/0.98    inference(nnf_transformation,[],[f1])).
% 3.23/0.98  
% 3.23/0.98  fof(f37,plain,(
% 3.23/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.23/0.98    inference(flattening,[],[f36])).
% 3.23/0.98  
% 3.23/0.98  fof(f49,plain,(
% 3.23/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.23/0.98    inference(cnf_transformation,[],[f37])).
% 3.23/0.98  
% 3.23/0.98  fof(f6,axiom,(
% 3.23/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f40,plain,(
% 3.23/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.23/0.98    inference(nnf_transformation,[],[f6])).
% 3.23/0.98  
% 3.23/0.98  fof(f41,plain,(
% 3.23/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.23/0.98    inference(flattening,[],[f40])).
% 3.23/0.98  
% 3.23/0.98  fof(f58,plain,(
% 3.23/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.23/0.98    inference(cnf_transformation,[],[f41])).
% 3.23/0.98  
% 3.23/0.98  fof(f89,plain,(
% 3.23/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.23/0.98    inference(equality_resolution,[],[f58])).
% 3.23/0.98  
% 3.23/0.98  fof(f18,axiom,(
% 3.23/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.23/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.23/0.98  
% 3.23/0.98  fof(f32,plain,(
% 3.23/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.23/0.98    inference(ennf_transformation,[],[f18])).
% 3.23/0.98  
% 3.23/0.98  fof(f33,plain,(
% 3.23/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.23/0.98    inference(flattening,[],[f32])).
% 3.23/0.98  
% 3.23/0.98  fof(f72,plain,(
% 3.23/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.23/0.98    inference(cnf_transformation,[],[f33])).
% 3.23/0.98  
% 3.23/0.98  cnf(c_25,negated_conjecture,
% 3.23/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 3.23/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_990,plain,
% 3.23/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_20,plain,
% 3.23/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.23/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_14,plain,
% 3.23/0.98      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.23/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_327,plain,
% 3.23/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.23/0.98      | ~ v1_relat_1(X0) ),
% 3.23/0.98      inference(resolution,[status(thm)],[c_20,c_14]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_987,plain,
% 3.23/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.23/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.23/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_327]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1371,plain,
% 3.23/0.98      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top
% 3.23/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_990,c_987]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_5,plain,
% 3.23/0.98      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 3.23/0.98      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.23/0.98      | k1_xboole_0 = X0 ),
% 3.23/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1001,plain,
% 3.23/0.98      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.23/0.98      | k1_xboole_0 = X1
% 3.23/0.98      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3095,plain,
% 3.23/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.23/0.98      | k1_relat_1(sK3) = k1_xboole_0
% 3.23/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_1371,c_1001]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_11,plain,
% 3.23/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.23/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_998,plain,
% 3.23/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.23/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1652,plain,
% 3.23/0.98      ( r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_990,c_998]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_12,plain,
% 3.23/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.23/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_10,plain,
% 3.23/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.23/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_184,plain,
% 3.23/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.23/0.98      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_185,plain,
% 3.23/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.23/0.98      inference(renaming,[status(thm)],[c_184]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_229,plain,
% 3.23/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.23/0.98      inference(bin_hyper_res,[status(thm)],[c_12,c_185]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_989,plain,
% 3.23/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.23/0.98      | v1_relat_1(X1) != iProver_top
% 3.23/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1852,plain,
% 3.23/0.98      ( v1_relat_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 3.23/0.98      | v1_relat_1(sK3) = iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_1652,c_989]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_15,plain,
% 3.23/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.23/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_997,plain,
% 3.23/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_2302,plain,
% 3.23/0.98      ( v1_relat_1(sK3) = iProver_top ),
% 3.23/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1852,c_997]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3394,plain,
% 3.23/0.98      ( k1_relat_1(sK3) = k1_xboole_0
% 3.23/0.98      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3) ),
% 3.23/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3095,c_2302]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3395,plain,
% 3.23/0.98      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.23/0.98      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.23/0.98      inference(renaming,[status(thm)],[c_3394]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3409,plain,
% 3.23/0.98      ( k1_relat_1(sK3) = k1_xboole_0
% 3.23/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_3395,c_990]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_23,negated_conjecture,
% 3.23/0.98      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.23/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_29,plain,
% 3.23/0.98      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_21,plain,
% 3.23/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.23/0.98      inference(cnf_transformation,[],[f71]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1193,plain,
% 3.23/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.23/0.98      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.23/0.98      inference(instantiation,[status(thm)],[c_21]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1283,plain,
% 3.23/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.23/0.98      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 3.23/0.98      inference(instantiation,[status(thm)],[c_1193]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_16,plain,
% 3.23/0.98      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.23/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1513,plain,
% 3.23/0.98      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.23/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1515,plain,
% 3.23/0.98      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) = iProver_top
% 3.23/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_1513]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_523,plain,
% 3.23/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.23/0.98      theory(equality) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1218,plain,
% 3.23/0.98      ( ~ r1_tarski(X0,X1)
% 3.23/0.98      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.23/0.98      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 3.23/0.98      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 3.23/0.98      inference(instantiation,[status(thm)],[c_523]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1282,plain,
% 3.23/0.98      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.23/0.98      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 3.23/0.98      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.23/0.98      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 3.23/0.98      inference(instantiation,[status(thm)],[c_1218]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1514,plain,
% 3.23/0.98      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.23/0.98      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 3.23/0.98      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.23/0.98      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 3.23/0.98      inference(instantiation,[status(thm)],[c_1282]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1517,plain,
% 3.23/0.98      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.23/0.98      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3)
% 3.23/0.98      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top
% 3.23/0.98      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_1514]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_19,plain,
% 3.23/0.98      ( ~ v1_funct_1(X0)
% 3.23/0.98      | ~ v1_relat_1(X0)
% 3.23/0.98      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.23/0.98      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.23/0.98      inference(cnf_transformation,[],[f82]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_26,negated_conjecture,
% 3.23/0.98      ( v1_funct_1(sK3) ),
% 3.23/0.98      inference(cnf_transformation,[],[f73]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_308,plain,
% 3.23/0.98      ( ~ v1_relat_1(X0)
% 3.23/0.98      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.23/0.98      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.23/0.98      | sK3 != X0 ),
% 3.23/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_309,plain,
% 3.23/0.98      ( ~ v1_relat_1(sK3)
% 3.23/0.98      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.23/0.98      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.23/0.98      inference(unflattening,[status(thm)],[c_308]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_988,plain,
% 3.23/0.98      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.23/0.98      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.23/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_309]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3400,plain,
% 3.23/0.98      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.23/0.98      | k1_relat_1(sK3) = k1_xboole_0
% 3.23/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_3395,c_988]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3472,plain,
% 3.23/0.98      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.23/0.98      inference(global_propositional_subsumption,
% 3.23/0.98                [status(thm)],
% 3.23/0.98                [c_3409,c_25,c_29,c_1283,c_1515,c_1517,c_2302,c_3400]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_18,plain,
% 3.23/0.98      ( ~ v1_relat_1(X0)
% 3.23/0.98      | k2_relat_1(X0) = k1_xboole_0
% 3.23/0.98      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.23/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_994,plain,
% 3.23/0.98      ( k2_relat_1(X0) = k1_xboole_0
% 3.23/0.98      | k1_relat_1(X0) != k1_xboole_0
% 3.23/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3496,plain,
% 3.23/0.98      ( k2_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_3472,c_994]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3669,plain,
% 3.23/0.98      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 3.23/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3496,c_2302]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_996,plain,
% 3.23/0.98      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 3.23/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3703,plain,
% 3.23/0.98      ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top
% 3.23/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_3669,c_996]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_4872,plain,
% 3.23/0.98      ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top ),
% 3.23/0.98      inference(global_propositional_subsumption,[status(thm)],[c_3703,c_2302]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_9,plain,
% 3.23/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.23/0.98      inference(cnf_transformation,[],[f59]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1000,plain,
% 3.23/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1651,plain,
% 3.23/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_1000,c_998]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_0,plain,
% 3.23/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.23/0.98      inference(cnf_transformation,[],[f49]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1005,plain,
% 3.23/0.98      ( X0 = X1
% 3.23/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.23/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_2043,plain,
% 3.23/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_1651,c_1005]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_4881,plain,
% 3.23/0.98      ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_4872,c_2043]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_6,plain,
% 3.23/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.23/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_22,plain,
% 3.23/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.23/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.23/0.98      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 3.23/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_992,plain,
% 3.23/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.23/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 3.23/0.98      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_2838,plain,
% 3.23/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),X0))) = iProver_top
% 3.23/0.98      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_990,c_992]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3171,plain,
% 3.23/0.98      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.23/0.98      | r1_tarski(sK3,k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),X0)) = iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_2838,c_998]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3229,plain,
% 3.23/0.98      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.23/0.98      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_6,c_3171]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_59,plain,
% 3.23/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.23/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_61,plain,
% 3.23/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.23/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.23/0.98      inference(instantiation,[status(thm)],[c_59]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_65,plain,
% 3.23/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_67,plain,
% 3.23/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.23/0.98      inference(instantiation,[status(thm)],[c_65]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1693,plain,
% 3.23/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.23/0.98      inference(instantiation,[status(thm)],[c_11]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1694,plain,
% 3.23/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(X0)) != iProver_top
% 3.23/0.98      | r1_tarski(sK3,X0) = iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_1693]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_1696,plain,
% 3.23/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.23/0.98      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.23/0.98      inference(instantiation,[status(thm)],[c_1694]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3170,plain,
% 3.23/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.23/0.98      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_6,c_2838]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3674,plain,
% 3.23/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.23/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.23/0.98      inference(demodulation,[status(thm)],[c_3669,c_3170]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3847,plain,
% 3.23/0.98      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.23/0.98      inference(global_propositional_subsumption,
% 3.23/0.98                [status(thm)],
% 3.23/0.98                [c_3229,c_61,c_67,c_1696,c_3674]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_3854,plain,
% 3.23/0.98      ( sK3 = k1_xboole_0 ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_3847,c_2043]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_5693,plain,
% 3.23/0.98      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.23/0.98      inference(light_normalisation,[status(thm)],[c_4881,c_3854]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_993,plain,
% 3.23/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.23/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_2202,plain,
% 3.23/0.98      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.23/0.98      inference(superposition,[status(thm)],[c_990,c_993]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_991,plain,
% 3.23/0.98      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.23/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_2227,plain,
% 3.23/0.98      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.23/0.98      inference(demodulation,[status(thm)],[c_2202,c_991]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_5520,plain,
% 3.23/0.98      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.23/0.98      inference(demodulation,[status(thm)],[c_3854,c_2227]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_5697,plain,
% 3.23/0.98      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.23/0.98      inference(demodulation,[status(thm)],[c_5693,c_5520]) ).
% 3.23/0.98  
% 3.23/0.98  cnf(c_5930,plain,
% 3.23/0.98      ( $false ),
% 3.23/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_5697,c_1651]) ).
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.23/0.98  
% 3.23/0.98  ------                               Statistics
% 3.23/0.98  
% 3.23/0.98  ------ General
% 3.23/0.98  
% 3.23/0.98  abstr_ref_over_cycles:                  0
% 3.23/0.98  abstr_ref_under_cycles:                 0
% 3.23/0.98  gc_basic_clause_elim:                   0
% 3.23/0.98  forced_gc_time:                         0
% 3.23/0.98  parsing_time:                           0.009
% 3.23/0.98  unif_index_cands_time:                  0.
% 3.23/0.98  unif_index_add_time:                    0.
% 3.23/0.98  orderings_time:                         0.
% 3.23/0.98  out_proof_time:                         0.008
% 3.23/0.98  total_time:                             0.187
% 3.23/0.98  num_of_symbols:                         49
% 3.23/0.98  num_of_terms:                           5201
% 3.23/0.98  
% 3.23/0.98  ------ Preprocessing
% 3.23/0.98  
% 3.23/0.98  num_of_splits:                          0
% 3.23/0.98  num_of_split_atoms:                     0
% 3.23/0.98  num_of_reused_defs:                     0
% 3.23/0.98  num_eq_ax_congr_red:                    10
% 3.23/0.98  num_of_sem_filtered_clauses:            1
% 3.23/0.98  num_of_subtypes:                        0
% 3.23/0.98  monotx_restored_types:                  0
% 3.23/0.98  sat_num_of_epr_types:                   0
% 3.23/0.98  sat_num_of_non_cyclic_types:            0
% 3.23/0.98  sat_guarded_non_collapsed_types:        0
% 3.23/0.98  num_pure_diseq_elim:                    0
% 3.23/0.98  simp_replaced_by:                       0
% 3.23/0.98  res_preprocessed:                       120
% 3.23/0.98  prep_upred:                             0
% 3.23/0.98  prep_unflattend:                        1
% 3.23/0.98  smt_new_axioms:                         0
% 3.23/0.98  pred_elim_cands:                        3
% 3.23/0.98  pred_elim:                              2
% 3.23/0.98  pred_elim_cl:                           3
% 3.23/0.98  pred_elim_cycles:                       4
% 3.23/0.98  merged_defs:                            8
% 3.23/0.98  merged_defs_ncl:                        0
% 3.23/0.98  bin_hyper_res:                          9
% 3.23/0.98  prep_cycles:                            4
% 3.23/0.98  pred_elim_time:                         0.001
% 3.23/0.98  splitting_time:                         0.
% 3.23/0.98  sem_filter_time:                        0.
% 3.23/0.98  monotx_time:                            0.001
% 3.23/0.98  subtype_inf_time:                       0.
% 3.23/0.98  
% 3.23/0.98  ------ Problem properties
% 3.23/0.98  
% 3.23/0.98  clauses:                                23
% 3.23/0.98  conjectures:                            3
% 3.23/0.98  epr:                                    4
% 3.23/0.98  horn:                                   21
% 3.23/0.98  ground:                                 3
% 3.23/0.98  unary:                                  10
% 3.23/0.98  binary:                                 4
% 3.23/0.98  lits:                                   45
% 3.23/0.98  lits_eq:                                16
% 3.23/0.98  fd_pure:                                0
% 3.23/0.98  fd_pseudo:                              0
% 3.23/0.98  fd_cond:                                1
% 3.23/0.98  fd_pseudo_cond:                         2
% 3.23/0.98  ac_symbols:                             0
% 3.23/0.98  
% 3.23/0.98  ------ Propositional Solver
% 3.23/0.98  
% 3.23/0.98  prop_solver_calls:                      28
% 3.23/0.98  prop_fast_solver_calls:                 702
% 3.23/0.98  smt_solver_calls:                       0
% 3.23/0.98  smt_fast_solver_calls:                  0
% 3.23/0.98  prop_num_of_clauses:                    2228
% 3.23/0.98  prop_preprocess_simplified:             7232
% 3.23/0.98  prop_fo_subsumed:                       20
% 3.23/0.98  prop_solver_time:                       0.
% 3.23/0.98  smt_solver_time:                        0.
% 3.23/0.98  smt_fast_solver_time:                   0.
% 3.23/0.98  prop_fast_solver_time:                  0.
% 3.23/0.98  prop_unsat_core_time:                   0.
% 3.23/0.98  
% 3.23/0.98  ------ QBF
% 3.23/0.98  
% 3.23/0.98  qbf_q_res:                              0
% 3.23/0.98  qbf_num_tautologies:                    0
% 3.23/0.98  qbf_prep_cycles:                        0
% 3.23/0.98  
% 3.23/0.98  ------ BMC1
% 3.23/0.98  
% 3.23/0.98  bmc1_current_bound:                     -1
% 3.23/0.98  bmc1_last_solved_bound:                 -1
% 3.23/0.98  bmc1_unsat_core_size:                   -1
% 3.23/0.98  bmc1_unsat_core_parents_size:           -1
% 3.23/0.98  bmc1_merge_next_fun:                    0
% 3.23/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.23/0.98  
% 3.23/0.98  ------ Instantiation
% 3.23/0.98  
% 3.23/0.98  inst_num_of_clauses:                    717
% 3.23/0.98  inst_num_in_passive:                    304
% 3.23/0.98  inst_num_in_active:                     313
% 3.23/0.98  inst_num_in_unprocessed:                100
% 3.23/0.98  inst_num_of_loops:                      360
% 3.23/0.98  inst_num_of_learning_restarts:          0
% 3.23/0.98  inst_num_moves_active_passive:          45
% 3.23/0.98  inst_lit_activity:                      0
% 3.23/0.98  inst_lit_activity_moves:                0
% 3.23/0.98  inst_num_tautologies:                   0
% 3.23/0.98  inst_num_prop_implied:                  0
% 3.23/0.98  inst_num_existing_simplified:           0
% 3.23/0.98  inst_num_eq_res_simplified:             0
% 3.23/0.98  inst_num_child_elim:                    0
% 3.23/0.98  inst_num_of_dismatching_blockings:      235
% 3.23/0.98  inst_num_of_non_proper_insts:           674
% 3.23/0.98  inst_num_of_duplicates:                 0
% 3.23/0.98  inst_inst_num_from_inst_to_res:         0
% 3.23/0.98  inst_dismatching_checking_time:         0.
% 3.23/0.98  
% 3.23/0.98  ------ Resolution
% 3.23/0.98  
% 3.23/0.98  res_num_of_clauses:                     0
% 3.23/0.98  res_num_in_passive:                     0
% 3.23/0.98  res_num_in_active:                      0
% 3.23/0.98  res_num_of_loops:                       124
% 3.23/0.98  res_forward_subset_subsumed:            75
% 3.23/0.98  res_backward_subset_subsumed:           0
% 3.23/0.98  res_forward_subsumed:                   0
% 3.23/0.98  res_backward_subsumed:                  0
% 3.23/0.98  res_forward_subsumption_resolution:     0
% 3.23/0.98  res_backward_subsumption_resolution:    0
% 3.23/0.98  res_clause_to_clause_subsumption:       336
% 3.23/0.98  res_orphan_elimination:                 0
% 3.23/0.98  res_tautology_del:                      30
% 3.23/0.98  res_num_eq_res_simplified:              0
% 3.23/0.98  res_num_sel_changes:                    0
% 3.23/0.98  res_moves_from_active_to_pass:          0
% 3.23/0.98  
% 3.23/0.98  ------ Superposition
% 3.23/0.98  
% 3.23/0.98  sup_time_total:                         0.
% 3.23/0.98  sup_time_generating:                    0.
% 3.23/0.98  sup_time_sim_full:                      0.
% 3.23/0.98  sup_time_sim_immed:                     0.
% 3.23/0.98  
% 3.23/0.98  sup_num_of_clauses:                     68
% 3.23/0.98  sup_num_in_active:                      41
% 3.23/0.98  sup_num_in_passive:                     27
% 3.23/0.98  sup_num_of_loops:                       70
% 3.23/0.98  sup_fw_superposition:                   78
% 3.23/0.98  sup_bw_superposition:                   59
% 3.23/0.98  sup_immediate_simplified:               42
% 3.23/0.98  sup_given_eliminated:                   2
% 3.23/0.98  comparisons_done:                       0
% 3.23/0.98  comparisons_avoided:                    0
% 3.23/0.98  
% 3.23/0.98  ------ Simplifications
% 3.23/0.98  
% 3.23/0.98  
% 3.23/0.98  sim_fw_subset_subsumed:                 14
% 3.23/0.98  sim_bw_subset_subsumed:                 7
% 3.23/0.98  sim_fw_subsumed:                        24
% 3.23/0.98  sim_bw_subsumed:                        1
% 3.23/0.98  sim_fw_subsumption_res:                 2
% 3.23/0.98  sim_bw_subsumption_res:                 0
% 3.23/0.98  sim_tautology_del:                      6
% 3.23/0.98  sim_eq_tautology_del:                   8
% 3.23/0.98  sim_eq_res_simp:                        0
% 3.23/0.98  sim_fw_demodulated:                     3
% 3.23/0.98  sim_bw_demodulated:                     29
% 3.23/0.98  sim_light_normalised:                   8
% 3.23/0.98  sim_joinable_taut:                      0
% 3.23/0.98  sim_joinable_simp:                      0
% 3.23/0.98  sim_ac_normalised:                      0
% 3.23/0.98  sim_smt_subsumption:                    0
% 3.23/0.98  
%------------------------------------------------------------------------------
