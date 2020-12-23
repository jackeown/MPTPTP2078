%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:32 EST 2020

% Result     : Theorem 0.99s
% Output     : CNFRefutation 0.99s
% Verified   : 
% Statistics : Number of formulae       :  145 ( 503 expanded)
%              Number of clauses        :   77 ( 149 expanded)
%              Number of leaves         :   18 ( 107 expanded)
%              Depth                    :   20
%              Number of atoms          :  360 (1281 expanded)
%              Number of equality atoms :  166 ( 438 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f41,plain,(
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
    inference(cnf_transformation,[],[f41])).

fof(f61,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_1(X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f42,plain,
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

fof(f43,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f42])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f79,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f70,f73])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f36])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f49,f73,f73])).

fof(f72,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f72,f73,f73])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_enumset1(X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f63,f73,f73])).

cnf(c_15,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_14,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1445,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2850,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_15,c_1445])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1569,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1571,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1569])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1570,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1573,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1570])).

cnf(c_2855,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2850,c_1571,c_1573])).

cnf(c_1448,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_320,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_13])).

cnf(c_324,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_320,c_18])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_324])).

cnf(c_1438,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_1945,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1448,c_1438])).

cnf(c_16,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1946,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1945,c_16])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1453,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3186,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1946,c_1453])).

cnf(c_5675,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2855,c_3186])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1452,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_21,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_282,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_283,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_282])).

cnf(c_1440,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_284,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_283])).

cnf(c_1580,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1581,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1580])).

cnf(c_1586,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1440,c_28,c_284,c_1581])).

cnf(c_1587,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1586])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1446,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2153,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1587,c_1446])).

cnf(c_3188,plain,
    ( k2_zfmisc_1(k1_relat_1(sK3),X0) = sK3
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),X0),sK3) != iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2153,c_1453])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1441,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1724,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1441,c_1438])).

cnf(c_5,plain,
    ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1449,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2976,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1724,c_1449])).

cnf(c_3670,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2976,c_1441])).

cnf(c_23,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1608,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1696,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1608])).

cnf(c_1020,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1613,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_1020])).

cnf(c_1695,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1613])).

cnf(c_1855,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1695])).

cnf(c_1856,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_297,plain,
    ( ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_298,plain,
    ( ~ v1_relat_1(sK3)
    | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_297])).

cnf(c_1439,plain,
    ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_298])).

cnf(c_1628,plain,
    ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1439,c_25,c_298,c_1580])).

cnf(c_1629,plain,
    ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1628])).

cnf(c_3664,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2976,c_1629])).

cnf(c_3709,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3670,c_25,c_23,c_1580,c_1696,c_1855,c_1856,c_3664])).

cnf(c_4607,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3188,c_7,c_3709])).

cnf(c_4611,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4607,c_1946])).

cnf(c_4615,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1452,c_4611])).

cnf(c_1443,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3327,plain,
    ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1441,c_1443])).

cnf(c_1442,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3360,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3327,c_1442])).

cnf(c_4967,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4615,c_3360])).

cnf(c_5769,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5675,c_4967])).

cnf(c_5792,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5769,c_1946])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 17:31:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 0.99/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.99/1.02  
% 0.99/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.99/1.02  
% 0.99/1.02  ------  iProver source info
% 0.99/1.02  
% 0.99/1.02  git: date: 2020-06-30 10:37:57 +0100
% 0.99/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.99/1.02  git: non_committed_changes: false
% 0.99/1.02  git: last_make_outside_of_git: false
% 0.99/1.02  
% 0.99/1.02  ------ 
% 0.99/1.02  
% 0.99/1.02  ------ Input Options
% 0.99/1.02  
% 0.99/1.02  --out_options                           all
% 0.99/1.02  --tptp_safe_out                         true
% 0.99/1.02  --problem_path                          ""
% 0.99/1.02  --include_path                          ""
% 0.99/1.02  --clausifier                            res/vclausify_rel
% 0.99/1.02  --clausifier_options                    --mode clausify
% 0.99/1.02  --stdin                                 false
% 0.99/1.02  --stats_out                             all
% 0.99/1.02  
% 0.99/1.02  ------ General Options
% 0.99/1.02  
% 0.99/1.02  --fof                                   false
% 0.99/1.02  --time_out_real                         305.
% 0.99/1.02  --time_out_virtual                      -1.
% 0.99/1.02  --symbol_type_check                     false
% 0.99/1.02  --clausify_out                          false
% 0.99/1.02  --sig_cnt_out                           false
% 0.99/1.02  --trig_cnt_out                          false
% 0.99/1.02  --trig_cnt_out_tolerance                1.
% 0.99/1.02  --trig_cnt_out_sk_spl                   false
% 0.99/1.02  --abstr_cl_out                          false
% 0.99/1.02  
% 0.99/1.02  ------ Global Options
% 0.99/1.02  
% 0.99/1.02  --schedule                              default
% 0.99/1.02  --add_important_lit                     false
% 0.99/1.02  --prop_solver_per_cl                    1000
% 0.99/1.02  --min_unsat_core                        false
% 0.99/1.02  --soft_assumptions                      false
% 0.99/1.02  --soft_lemma_size                       3
% 0.99/1.02  --prop_impl_unit_size                   0
% 0.99/1.02  --prop_impl_unit                        []
% 0.99/1.02  --share_sel_clauses                     true
% 0.99/1.02  --reset_solvers                         false
% 0.99/1.02  --bc_imp_inh                            [conj_cone]
% 0.99/1.02  --conj_cone_tolerance                   3.
% 0.99/1.02  --extra_neg_conj                        none
% 0.99/1.02  --large_theory_mode                     true
% 0.99/1.02  --prolific_symb_bound                   200
% 0.99/1.02  --lt_threshold                          2000
% 0.99/1.02  --clause_weak_htbl                      true
% 0.99/1.02  --gc_record_bc_elim                     false
% 0.99/1.02  
% 0.99/1.02  ------ Preprocessing Options
% 0.99/1.02  
% 0.99/1.02  --preprocessing_flag                    true
% 0.99/1.02  --time_out_prep_mult                    0.1
% 0.99/1.02  --splitting_mode                        input
% 0.99/1.02  --splitting_grd                         true
% 0.99/1.02  --splitting_cvd                         false
% 0.99/1.02  --splitting_cvd_svl                     false
% 0.99/1.02  --splitting_nvd                         32
% 0.99/1.02  --sub_typing                            true
% 0.99/1.02  --prep_gs_sim                           true
% 0.99/1.02  --prep_unflatten                        true
% 0.99/1.02  --prep_res_sim                          true
% 0.99/1.02  --prep_upred                            true
% 0.99/1.02  --prep_sem_filter                       exhaustive
% 0.99/1.02  --prep_sem_filter_out                   false
% 0.99/1.02  --pred_elim                             true
% 0.99/1.02  --res_sim_input                         true
% 0.99/1.02  --eq_ax_congr_red                       true
% 0.99/1.02  --pure_diseq_elim                       true
% 0.99/1.02  --brand_transform                       false
% 0.99/1.02  --non_eq_to_eq                          false
% 0.99/1.02  --prep_def_merge                        true
% 0.99/1.02  --prep_def_merge_prop_impl              false
% 0.99/1.02  --prep_def_merge_mbd                    true
% 0.99/1.02  --prep_def_merge_tr_red                 false
% 0.99/1.02  --prep_def_merge_tr_cl                  false
% 0.99/1.02  --smt_preprocessing                     true
% 0.99/1.02  --smt_ac_axioms                         fast
% 0.99/1.02  --preprocessed_out                      false
% 0.99/1.02  --preprocessed_stats                    false
% 0.99/1.02  
% 0.99/1.02  ------ Abstraction refinement Options
% 0.99/1.02  
% 0.99/1.02  --abstr_ref                             []
% 0.99/1.02  --abstr_ref_prep                        false
% 0.99/1.02  --abstr_ref_until_sat                   false
% 0.99/1.02  --abstr_ref_sig_restrict                funpre
% 0.99/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/1.02  --abstr_ref_under                       []
% 0.99/1.02  
% 0.99/1.02  ------ SAT Options
% 0.99/1.02  
% 0.99/1.02  --sat_mode                              false
% 0.99/1.02  --sat_fm_restart_options                ""
% 0.99/1.02  --sat_gr_def                            false
% 0.99/1.02  --sat_epr_types                         true
% 0.99/1.02  --sat_non_cyclic_types                  false
% 0.99/1.02  --sat_finite_models                     false
% 0.99/1.02  --sat_fm_lemmas                         false
% 0.99/1.02  --sat_fm_prep                           false
% 0.99/1.02  --sat_fm_uc_incr                        true
% 0.99/1.02  --sat_out_model                         small
% 0.99/1.02  --sat_out_clauses                       false
% 0.99/1.02  
% 0.99/1.02  ------ QBF Options
% 0.99/1.02  
% 0.99/1.02  --qbf_mode                              false
% 0.99/1.02  --qbf_elim_univ                         false
% 0.99/1.02  --qbf_dom_inst                          none
% 0.99/1.02  --qbf_dom_pre_inst                      false
% 0.99/1.02  --qbf_sk_in                             false
% 0.99/1.02  --qbf_pred_elim                         true
% 0.99/1.02  --qbf_split                             512
% 0.99/1.02  
% 0.99/1.02  ------ BMC1 Options
% 0.99/1.02  
% 0.99/1.02  --bmc1_incremental                      false
% 0.99/1.02  --bmc1_axioms                           reachable_all
% 0.99/1.02  --bmc1_min_bound                        0
% 0.99/1.02  --bmc1_max_bound                        -1
% 0.99/1.02  --bmc1_max_bound_default                -1
% 0.99/1.02  --bmc1_symbol_reachability              true
% 0.99/1.02  --bmc1_property_lemmas                  false
% 0.99/1.02  --bmc1_k_induction                      false
% 0.99/1.02  --bmc1_non_equiv_states                 false
% 0.99/1.02  --bmc1_deadlock                         false
% 0.99/1.02  --bmc1_ucm                              false
% 0.99/1.02  --bmc1_add_unsat_core                   none
% 0.99/1.02  --bmc1_unsat_core_children              false
% 0.99/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/1.02  --bmc1_out_stat                         full
% 0.99/1.02  --bmc1_ground_init                      false
% 0.99/1.02  --bmc1_pre_inst_next_state              false
% 0.99/1.02  --bmc1_pre_inst_state                   false
% 0.99/1.02  --bmc1_pre_inst_reach_state             false
% 0.99/1.02  --bmc1_out_unsat_core                   false
% 0.99/1.02  --bmc1_aig_witness_out                  false
% 0.99/1.02  --bmc1_verbose                          false
% 0.99/1.02  --bmc1_dump_clauses_tptp                false
% 0.99/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.99/1.02  --bmc1_dump_file                        -
% 0.99/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.99/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.99/1.02  --bmc1_ucm_extend_mode                  1
% 0.99/1.02  --bmc1_ucm_init_mode                    2
% 0.99/1.02  --bmc1_ucm_cone_mode                    none
% 0.99/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.99/1.02  --bmc1_ucm_relax_model                  4
% 0.99/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.99/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/1.02  --bmc1_ucm_layered_model                none
% 0.99/1.02  --bmc1_ucm_max_lemma_size               10
% 0.99/1.02  
% 0.99/1.02  ------ AIG Options
% 0.99/1.02  
% 0.99/1.02  --aig_mode                              false
% 0.99/1.02  
% 0.99/1.02  ------ Instantiation Options
% 0.99/1.02  
% 0.99/1.02  --instantiation_flag                    true
% 0.99/1.02  --inst_sos_flag                         false
% 0.99/1.02  --inst_sos_phase                        true
% 0.99/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/1.02  --inst_lit_sel_side                     num_symb
% 0.99/1.02  --inst_solver_per_active                1400
% 0.99/1.02  --inst_solver_calls_frac                1.
% 0.99/1.02  --inst_passive_queue_type               priority_queues
% 0.99/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/1.02  --inst_passive_queues_freq              [25;2]
% 0.99/1.02  --inst_dismatching                      true
% 0.99/1.02  --inst_eager_unprocessed_to_passive     true
% 0.99/1.02  --inst_prop_sim_given                   true
% 0.99/1.02  --inst_prop_sim_new                     false
% 0.99/1.02  --inst_subs_new                         false
% 0.99/1.02  --inst_eq_res_simp                      false
% 0.99/1.02  --inst_subs_given                       false
% 0.99/1.02  --inst_orphan_elimination               true
% 0.99/1.02  --inst_learning_loop_flag               true
% 0.99/1.02  --inst_learning_start                   3000
% 0.99/1.02  --inst_learning_factor                  2
% 0.99/1.02  --inst_start_prop_sim_after_learn       3
% 0.99/1.02  --inst_sel_renew                        solver
% 0.99/1.02  --inst_lit_activity_flag                true
% 0.99/1.02  --inst_restr_to_given                   false
% 0.99/1.02  --inst_activity_threshold               500
% 0.99/1.02  --inst_out_proof                        true
% 0.99/1.02  
% 0.99/1.02  ------ Resolution Options
% 0.99/1.02  
% 0.99/1.02  --resolution_flag                       true
% 0.99/1.02  --res_lit_sel                           adaptive
% 0.99/1.02  --res_lit_sel_side                      none
% 0.99/1.02  --res_ordering                          kbo
% 0.99/1.02  --res_to_prop_solver                    active
% 0.99/1.02  --res_prop_simpl_new                    false
% 0.99/1.02  --res_prop_simpl_given                  true
% 0.99/1.02  --res_passive_queue_type                priority_queues
% 0.99/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/1.02  --res_passive_queues_freq               [15;5]
% 0.99/1.02  --res_forward_subs                      full
% 0.99/1.02  --res_backward_subs                     full
% 0.99/1.02  --res_forward_subs_resolution           true
% 0.99/1.02  --res_backward_subs_resolution          true
% 0.99/1.02  --res_orphan_elimination                true
% 0.99/1.02  --res_time_limit                        2.
% 0.99/1.02  --res_out_proof                         true
% 0.99/1.02  
% 0.99/1.02  ------ Superposition Options
% 0.99/1.02  
% 0.99/1.02  --superposition_flag                    true
% 0.99/1.02  --sup_passive_queue_type                priority_queues
% 0.99/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/1.02  --sup_passive_queues_freq               [8;1;4]
% 0.99/1.02  --demod_completeness_check              fast
% 0.99/1.02  --demod_use_ground                      true
% 0.99/1.02  --sup_to_prop_solver                    passive
% 0.99/1.02  --sup_prop_simpl_new                    true
% 0.99/1.02  --sup_prop_simpl_given                  true
% 0.99/1.02  --sup_fun_splitting                     false
% 0.99/1.02  --sup_smt_interval                      50000
% 0.99/1.02  
% 0.99/1.02  ------ Superposition Simplification Setup
% 0.99/1.02  
% 0.99/1.02  --sup_indices_passive                   []
% 0.99/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.02  --sup_full_bw                           [BwDemod]
% 0.99/1.02  --sup_immed_triv                        [TrivRules]
% 0.99/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.02  --sup_immed_bw_main                     []
% 0.99/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.02  
% 0.99/1.02  ------ Combination Options
% 0.99/1.02  
% 0.99/1.02  --comb_res_mult                         3
% 0.99/1.02  --comb_sup_mult                         2
% 0.99/1.02  --comb_inst_mult                        10
% 0.99/1.02  
% 0.99/1.02  ------ Debug Options
% 0.99/1.02  
% 0.99/1.02  --dbg_backtrace                         false
% 0.99/1.02  --dbg_dump_prop_clauses                 false
% 0.99/1.02  --dbg_dump_prop_clauses_file            -
% 0.99/1.02  --dbg_out_stat                          false
% 0.99/1.02  ------ Parsing...
% 0.99/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.99/1.02  
% 0.99/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.99/1.02  
% 0.99/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.99/1.02  
% 0.99/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.99/1.02  ------ Proving...
% 0.99/1.02  ------ Problem Properties 
% 0.99/1.02  
% 0.99/1.02  
% 0.99/1.02  clauses                                 22
% 0.99/1.02  conjectures                             3
% 0.99/1.02  EPR                                     3
% 0.99/1.02  Horn                                    20
% 0.99/1.02  unary                                   11
% 0.99/1.02  binary                                  6
% 0.99/1.02  lits                                    38
% 0.99/1.02  lits eq                                 14
% 0.99/1.02  fd_pure                                 0
% 0.99/1.02  fd_pseudo                               0
% 0.99/1.02  fd_cond                                 1
% 0.99/1.02  fd_pseudo_cond                          2
% 0.99/1.02  AC symbols                              0
% 0.99/1.02  
% 0.99/1.02  ------ Schedule dynamic 5 is on 
% 0.99/1.02  
% 0.99/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.99/1.02  
% 0.99/1.02  
% 0.99/1.02  ------ 
% 0.99/1.02  Current options:
% 0.99/1.02  ------ 
% 0.99/1.02  
% 0.99/1.02  ------ Input Options
% 0.99/1.02  
% 0.99/1.02  --out_options                           all
% 0.99/1.02  --tptp_safe_out                         true
% 0.99/1.02  --problem_path                          ""
% 0.99/1.02  --include_path                          ""
% 0.99/1.02  --clausifier                            res/vclausify_rel
% 0.99/1.02  --clausifier_options                    --mode clausify
% 0.99/1.02  --stdin                                 false
% 0.99/1.02  --stats_out                             all
% 0.99/1.02  
% 0.99/1.02  ------ General Options
% 0.99/1.02  
% 0.99/1.02  --fof                                   false
% 0.99/1.02  --time_out_real                         305.
% 0.99/1.02  --time_out_virtual                      -1.
% 0.99/1.02  --symbol_type_check                     false
% 0.99/1.02  --clausify_out                          false
% 0.99/1.02  --sig_cnt_out                           false
% 0.99/1.02  --trig_cnt_out                          false
% 0.99/1.02  --trig_cnt_out_tolerance                1.
% 0.99/1.02  --trig_cnt_out_sk_spl                   false
% 0.99/1.02  --abstr_cl_out                          false
% 0.99/1.02  
% 0.99/1.02  ------ Global Options
% 0.99/1.02  
% 0.99/1.02  --schedule                              default
% 0.99/1.02  --add_important_lit                     false
% 0.99/1.02  --prop_solver_per_cl                    1000
% 0.99/1.02  --min_unsat_core                        false
% 0.99/1.02  --soft_assumptions                      false
% 0.99/1.02  --soft_lemma_size                       3
% 0.99/1.02  --prop_impl_unit_size                   0
% 0.99/1.02  --prop_impl_unit                        []
% 0.99/1.02  --share_sel_clauses                     true
% 0.99/1.02  --reset_solvers                         false
% 0.99/1.02  --bc_imp_inh                            [conj_cone]
% 0.99/1.02  --conj_cone_tolerance                   3.
% 0.99/1.02  --extra_neg_conj                        none
% 0.99/1.02  --large_theory_mode                     true
% 0.99/1.02  --prolific_symb_bound                   200
% 0.99/1.02  --lt_threshold                          2000
% 0.99/1.02  --clause_weak_htbl                      true
% 0.99/1.02  --gc_record_bc_elim                     false
% 0.99/1.02  
% 0.99/1.02  ------ Preprocessing Options
% 0.99/1.02  
% 0.99/1.02  --preprocessing_flag                    true
% 0.99/1.02  --time_out_prep_mult                    0.1
% 0.99/1.02  --splitting_mode                        input
% 0.99/1.02  --splitting_grd                         true
% 0.99/1.02  --splitting_cvd                         false
% 0.99/1.02  --splitting_cvd_svl                     false
% 0.99/1.02  --splitting_nvd                         32
% 0.99/1.02  --sub_typing                            true
% 0.99/1.02  --prep_gs_sim                           true
% 0.99/1.02  --prep_unflatten                        true
% 0.99/1.02  --prep_res_sim                          true
% 0.99/1.02  --prep_upred                            true
% 0.99/1.02  --prep_sem_filter                       exhaustive
% 0.99/1.02  --prep_sem_filter_out                   false
% 0.99/1.02  --pred_elim                             true
% 0.99/1.02  --res_sim_input                         true
% 0.99/1.02  --eq_ax_congr_red                       true
% 0.99/1.02  --pure_diseq_elim                       true
% 0.99/1.02  --brand_transform                       false
% 0.99/1.02  --non_eq_to_eq                          false
% 0.99/1.02  --prep_def_merge                        true
% 0.99/1.02  --prep_def_merge_prop_impl              false
% 0.99/1.02  --prep_def_merge_mbd                    true
% 0.99/1.02  --prep_def_merge_tr_red                 false
% 0.99/1.02  --prep_def_merge_tr_cl                  false
% 0.99/1.02  --smt_preprocessing                     true
% 0.99/1.02  --smt_ac_axioms                         fast
% 0.99/1.02  --preprocessed_out                      false
% 0.99/1.02  --preprocessed_stats                    false
% 0.99/1.02  
% 0.99/1.02  ------ Abstraction refinement Options
% 0.99/1.02  
% 0.99/1.02  --abstr_ref                             []
% 0.99/1.02  --abstr_ref_prep                        false
% 0.99/1.02  --abstr_ref_until_sat                   false
% 0.99/1.02  --abstr_ref_sig_restrict                funpre
% 0.99/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 0.99/1.02  --abstr_ref_under                       []
% 0.99/1.02  
% 0.99/1.02  ------ SAT Options
% 0.99/1.02  
% 0.99/1.02  --sat_mode                              false
% 0.99/1.02  --sat_fm_restart_options                ""
% 0.99/1.02  --sat_gr_def                            false
% 0.99/1.02  --sat_epr_types                         true
% 0.99/1.02  --sat_non_cyclic_types                  false
% 0.99/1.02  --sat_finite_models                     false
% 0.99/1.02  --sat_fm_lemmas                         false
% 0.99/1.02  --sat_fm_prep                           false
% 0.99/1.02  --sat_fm_uc_incr                        true
% 0.99/1.02  --sat_out_model                         small
% 0.99/1.02  --sat_out_clauses                       false
% 0.99/1.02  
% 0.99/1.02  ------ QBF Options
% 0.99/1.02  
% 0.99/1.02  --qbf_mode                              false
% 0.99/1.02  --qbf_elim_univ                         false
% 0.99/1.02  --qbf_dom_inst                          none
% 0.99/1.02  --qbf_dom_pre_inst                      false
% 0.99/1.02  --qbf_sk_in                             false
% 0.99/1.02  --qbf_pred_elim                         true
% 0.99/1.02  --qbf_split                             512
% 0.99/1.02  
% 0.99/1.02  ------ BMC1 Options
% 0.99/1.02  
% 0.99/1.02  --bmc1_incremental                      false
% 0.99/1.02  --bmc1_axioms                           reachable_all
% 0.99/1.02  --bmc1_min_bound                        0
% 0.99/1.02  --bmc1_max_bound                        -1
% 0.99/1.02  --bmc1_max_bound_default                -1
% 0.99/1.02  --bmc1_symbol_reachability              true
% 0.99/1.02  --bmc1_property_lemmas                  false
% 0.99/1.02  --bmc1_k_induction                      false
% 0.99/1.02  --bmc1_non_equiv_states                 false
% 0.99/1.02  --bmc1_deadlock                         false
% 0.99/1.02  --bmc1_ucm                              false
% 0.99/1.02  --bmc1_add_unsat_core                   none
% 0.99/1.02  --bmc1_unsat_core_children              false
% 0.99/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 0.99/1.02  --bmc1_out_stat                         full
% 0.99/1.02  --bmc1_ground_init                      false
% 0.99/1.02  --bmc1_pre_inst_next_state              false
% 0.99/1.02  --bmc1_pre_inst_state                   false
% 0.99/1.02  --bmc1_pre_inst_reach_state             false
% 0.99/1.02  --bmc1_out_unsat_core                   false
% 0.99/1.02  --bmc1_aig_witness_out                  false
% 0.99/1.02  --bmc1_verbose                          false
% 0.99/1.02  --bmc1_dump_clauses_tptp                false
% 0.99/1.02  --bmc1_dump_unsat_core_tptp             false
% 0.99/1.02  --bmc1_dump_file                        -
% 0.99/1.02  --bmc1_ucm_expand_uc_limit              128
% 0.99/1.02  --bmc1_ucm_n_expand_iterations          6
% 0.99/1.02  --bmc1_ucm_extend_mode                  1
% 0.99/1.02  --bmc1_ucm_init_mode                    2
% 0.99/1.02  --bmc1_ucm_cone_mode                    none
% 0.99/1.02  --bmc1_ucm_reduced_relation_type        0
% 0.99/1.02  --bmc1_ucm_relax_model                  4
% 0.99/1.02  --bmc1_ucm_full_tr_after_sat            true
% 0.99/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 0.99/1.02  --bmc1_ucm_layered_model                none
% 0.99/1.02  --bmc1_ucm_max_lemma_size               10
% 0.99/1.02  
% 0.99/1.02  ------ AIG Options
% 0.99/1.02  
% 0.99/1.02  --aig_mode                              false
% 0.99/1.02  
% 0.99/1.02  ------ Instantiation Options
% 0.99/1.02  
% 0.99/1.02  --instantiation_flag                    true
% 0.99/1.02  --inst_sos_flag                         false
% 0.99/1.02  --inst_sos_phase                        true
% 0.99/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.99/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.99/1.02  --inst_lit_sel_side                     none
% 0.99/1.02  --inst_solver_per_active                1400
% 0.99/1.02  --inst_solver_calls_frac                1.
% 0.99/1.02  --inst_passive_queue_type               priority_queues
% 0.99/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.99/1.03  --inst_passive_queues_freq              [25;2]
% 0.99/1.03  --inst_dismatching                      true
% 0.99/1.03  --inst_eager_unprocessed_to_passive     true
% 0.99/1.03  --inst_prop_sim_given                   true
% 0.99/1.03  --inst_prop_sim_new                     false
% 0.99/1.03  --inst_subs_new                         false
% 0.99/1.03  --inst_eq_res_simp                      false
% 0.99/1.03  --inst_subs_given                       false
% 0.99/1.03  --inst_orphan_elimination               true
% 0.99/1.03  --inst_learning_loop_flag               true
% 0.99/1.03  --inst_learning_start                   3000
% 0.99/1.03  --inst_learning_factor                  2
% 0.99/1.03  --inst_start_prop_sim_after_learn       3
% 0.99/1.03  --inst_sel_renew                        solver
% 0.99/1.03  --inst_lit_activity_flag                true
% 0.99/1.03  --inst_restr_to_given                   false
% 0.99/1.03  --inst_activity_threshold               500
% 0.99/1.03  --inst_out_proof                        true
% 0.99/1.03  
% 0.99/1.03  ------ Resolution Options
% 0.99/1.03  
% 0.99/1.03  --resolution_flag                       false
% 0.99/1.03  --res_lit_sel                           adaptive
% 0.99/1.03  --res_lit_sel_side                      none
% 0.99/1.03  --res_ordering                          kbo
% 0.99/1.03  --res_to_prop_solver                    active
% 0.99/1.03  --res_prop_simpl_new                    false
% 0.99/1.03  --res_prop_simpl_given                  true
% 0.99/1.03  --res_passive_queue_type                priority_queues
% 0.99/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.99/1.03  --res_passive_queues_freq               [15;5]
% 0.99/1.03  --res_forward_subs                      full
% 0.99/1.03  --res_backward_subs                     full
% 0.99/1.03  --res_forward_subs_resolution           true
% 0.99/1.03  --res_backward_subs_resolution          true
% 0.99/1.03  --res_orphan_elimination                true
% 0.99/1.03  --res_time_limit                        2.
% 0.99/1.03  --res_out_proof                         true
% 0.99/1.03  
% 0.99/1.03  ------ Superposition Options
% 0.99/1.03  
% 0.99/1.03  --superposition_flag                    true
% 0.99/1.03  --sup_passive_queue_type                priority_queues
% 0.99/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.99/1.03  --sup_passive_queues_freq               [8;1;4]
% 0.99/1.03  --demod_completeness_check              fast
% 0.99/1.03  --demod_use_ground                      true
% 0.99/1.03  --sup_to_prop_solver                    passive
% 0.99/1.03  --sup_prop_simpl_new                    true
% 0.99/1.03  --sup_prop_simpl_given                  true
% 0.99/1.03  --sup_fun_splitting                     false
% 0.99/1.03  --sup_smt_interval                      50000
% 0.99/1.03  
% 0.99/1.03  ------ Superposition Simplification Setup
% 0.99/1.03  
% 0.99/1.03  --sup_indices_passive                   []
% 0.99/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.99/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 0.99/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.03  --sup_full_bw                           [BwDemod]
% 0.99/1.03  --sup_immed_triv                        [TrivRules]
% 0.99/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.99/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.03  --sup_immed_bw_main                     []
% 0.99/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 0.99/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.99/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.99/1.03  
% 0.99/1.03  ------ Combination Options
% 0.99/1.03  
% 0.99/1.03  --comb_res_mult                         3
% 0.99/1.03  --comb_sup_mult                         2
% 0.99/1.03  --comb_inst_mult                        10
% 0.99/1.03  
% 0.99/1.03  ------ Debug Options
% 0.99/1.03  
% 0.99/1.03  --dbg_backtrace                         false
% 0.99/1.03  --dbg_dump_prop_clauses                 false
% 0.99/1.03  --dbg_dump_prop_clauses_file            -
% 0.99/1.03  --dbg_out_stat                          false
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  ------ Proving...
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  % SZS status Theorem for theBenchmark.p
% 0.99/1.03  
% 0.99/1.03   Resolution empty clause
% 0.99/1.03  
% 0.99/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 0.99/1.03  
% 0.99/1.03  fof(f11,axiom,(
% 0.99/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f62,plain,(
% 0.99/1.03    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.99/1.03    inference(cnf_transformation,[],[f11])).
% 0.99/1.03  
% 0.99/1.03  fof(f10,axiom,(
% 0.99/1.03    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f24,plain,(
% 0.99/1.03    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.99/1.03    inference(ennf_transformation,[],[f10])).
% 0.99/1.03  
% 0.99/1.03  fof(f60,plain,(
% 0.99/1.03    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f24])).
% 0.99/1.03  
% 0.99/1.03  fof(f13,axiom,(
% 0.99/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f27,plain,(
% 0.99/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.99/1.03    inference(ennf_transformation,[],[f13])).
% 0.99/1.03  
% 0.99/1.03  fof(f64,plain,(
% 0.99/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.99/1.03    inference(cnf_transformation,[],[f27])).
% 0.99/1.03  
% 0.99/1.03  fof(f6,axiom,(
% 0.99/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f55,plain,(
% 0.99/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.99/1.03    inference(cnf_transformation,[],[f6])).
% 0.99/1.03  
% 0.99/1.03  fof(f14,axiom,(
% 0.99/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f21,plain,(
% 0.99/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.99/1.03    inference(pure_predicate_removal,[],[f14])).
% 0.99/1.03  
% 0.99/1.03  fof(f28,plain,(
% 0.99/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.99/1.03    inference(ennf_transformation,[],[f21])).
% 0.99/1.03  
% 0.99/1.03  fof(f65,plain,(
% 0.99/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.99/1.03    inference(cnf_transformation,[],[f28])).
% 0.99/1.03  
% 0.99/1.03  fof(f9,axiom,(
% 0.99/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f23,plain,(
% 0.99/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.99/1.03    inference(ennf_transformation,[],[f9])).
% 0.99/1.03  
% 0.99/1.03  fof(f41,plain,(
% 0.99/1.03    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.99/1.03    inference(nnf_transformation,[],[f23])).
% 0.99/1.03  
% 0.99/1.03  fof(f58,plain,(
% 0.99/1.03    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f41])).
% 0.99/1.03  
% 0.99/1.03  fof(f61,plain,(
% 0.99/1.03    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.99/1.03    inference(cnf_transformation,[],[f11])).
% 0.99/1.03  
% 0.99/1.03  fof(f1,axiom,(
% 0.99/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f34,plain,(
% 0.99/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.99/1.03    inference(nnf_transformation,[],[f1])).
% 0.99/1.03  
% 0.99/1.03  fof(f35,plain,(
% 0.99/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.99/1.03    inference(flattening,[],[f34])).
% 0.99/1.03  
% 0.99/1.03  fof(f46,plain,(
% 0.99/1.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f35])).
% 0.99/1.03  
% 0.99/1.03  fof(f44,plain,(
% 0.99/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.99/1.03    inference(cnf_transformation,[],[f35])).
% 0.99/1.03  
% 0.99/1.03  fof(f81,plain,(
% 0.99/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.99/1.03    inference(equality_resolution,[],[f44])).
% 0.99/1.03  
% 0.99/1.03  fof(f16,axiom,(
% 0.99/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f20,plain,(
% 0.99/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1))))),
% 0.99/1.03    inference(pure_predicate_removal,[],[f16])).
% 0.99/1.03  
% 0.99/1.03  fof(f30,plain,(
% 0.99/1.03    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.99/1.03    inference(ennf_transformation,[],[f20])).
% 0.99/1.03  
% 0.99/1.03  fof(f31,plain,(
% 0.99/1.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.99/1.03    inference(flattening,[],[f30])).
% 0.99/1.03  
% 0.99/1.03  fof(f68,plain,(
% 0.99/1.03    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f31])).
% 0.99/1.03  
% 0.99/1.03  fof(f17,conjecture,(
% 0.99/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f18,negated_conjecture,(
% 0.99/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.99/1.03    inference(negated_conjecture,[],[f17])).
% 0.99/1.03  
% 0.99/1.03  fof(f19,plain,(
% 0.99/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.99/1.03    inference(pure_predicate_removal,[],[f18])).
% 0.99/1.03  
% 0.99/1.03  fof(f32,plain,(
% 0.99/1.03    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 0.99/1.03    inference(ennf_transformation,[],[f19])).
% 0.99/1.03  
% 0.99/1.03  fof(f33,plain,(
% 0.99/1.03    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 0.99/1.03    inference(flattening,[],[f32])).
% 0.99/1.03  
% 0.99/1.03  fof(f42,plain,(
% 0.99/1.03    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 0.99/1.03    introduced(choice_axiom,[])).
% 0.99/1.03  
% 0.99/1.03  fof(f43,plain,(
% 0.99/1.03    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 0.99/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f42])).
% 0.99/1.03  
% 0.99/1.03  fof(f69,plain,(
% 0.99/1.03    v1_funct_1(sK3)),
% 0.99/1.03    inference(cnf_transformation,[],[f43])).
% 0.99/1.03  
% 0.99/1.03  fof(f70,plain,(
% 0.99/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.99/1.03    inference(cnf_transformation,[],[f43])).
% 0.99/1.03  
% 0.99/1.03  fof(f2,axiom,(
% 0.99/1.03    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f47,plain,(
% 0.99/1.03    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f2])).
% 0.99/1.03  
% 0.99/1.03  fof(f3,axiom,(
% 0.99/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f48,plain,(
% 0.99/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f3])).
% 0.99/1.03  
% 0.99/1.03  fof(f73,plain,(
% 0.99/1.03    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.99/1.03    inference(definition_unfolding,[],[f47,f48])).
% 0.99/1.03  
% 0.99/1.03  fof(f79,plain,(
% 0.99/1.03    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 0.99/1.03    inference(definition_unfolding,[],[f70,f73])).
% 0.99/1.03  
% 0.99/1.03  fof(f7,axiom,(
% 0.99/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f40,plain,(
% 0.99/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.99/1.03    inference(nnf_transformation,[],[f7])).
% 0.99/1.03  
% 0.99/1.03  fof(f56,plain,(
% 0.99/1.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.99/1.03    inference(cnf_transformation,[],[f40])).
% 0.99/1.03  
% 0.99/1.03  fof(f5,axiom,(
% 0.99/1.03    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f38,plain,(
% 0.99/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.99/1.03    inference(nnf_transformation,[],[f5])).
% 0.99/1.03  
% 0.99/1.03  fof(f39,plain,(
% 0.99/1.03    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.99/1.03    inference(flattening,[],[f38])).
% 0.99/1.03  
% 0.99/1.03  fof(f53,plain,(
% 0.99/1.03    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.99/1.03    inference(cnf_transformation,[],[f39])).
% 0.99/1.03  
% 0.99/1.03  fof(f85,plain,(
% 0.99/1.03    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.99/1.03    inference(equality_resolution,[],[f53])).
% 0.99/1.03  
% 0.99/1.03  fof(f4,axiom,(
% 0.99/1.03    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f36,plain,(
% 0.99/1.03    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.99/1.03    inference(nnf_transformation,[],[f4])).
% 0.99/1.03  
% 0.99/1.03  fof(f37,plain,(
% 0.99/1.03    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.99/1.03    inference(flattening,[],[f36])).
% 0.99/1.03  
% 0.99/1.03  fof(f49,plain,(
% 0.99/1.03    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.99/1.03    inference(cnf_transformation,[],[f37])).
% 0.99/1.03  
% 0.99/1.03  fof(f76,plain,(
% 0.99/1.03    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_enumset1(X1,X1,X1))) )),
% 0.99/1.03    inference(definition_unfolding,[],[f49,f73,f73])).
% 0.99/1.03  
% 0.99/1.03  fof(f72,plain,(
% 0.99/1.03    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.99/1.03    inference(cnf_transformation,[],[f43])).
% 0.99/1.03  
% 0.99/1.03  fof(f78,plain,(
% 0.99/1.03    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.99/1.03    inference(definition_unfolding,[],[f72,f73,f73])).
% 0.99/1.03  
% 0.99/1.03  fof(f15,axiom,(
% 0.99/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f29,plain,(
% 0.99/1.03    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.99/1.03    inference(ennf_transformation,[],[f15])).
% 0.99/1.03  
% 0.99/1.03  fof(f66,plain,(
% 0.99/1.03    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.99/1.03    inference(cnf_transformation,[],[f29])).
% 0.99/1.03  
% 0.99/1.03  fof(f12,axiom,(
% 0.99/1.03    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 0.99/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.99/1.03  
% 0.99/1.03  fof(f25,plain,(
% 0.99/1.03    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.99/1.03    inference(ennf_transformation,[],[f12])).
% 0.99/1.03  
% 0.99/1.03  fof(f26,plain,(
% 0.99/1.03    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.99/1.03    inference(flattening,[],[f25])).
% 0.99/1.03  
% 0.99/1.03  fof(f63,plain,(
% 0.99/1.03    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.99/1.03    inference(cnf_transformation,[],[f26])).
% 0.99/1.03  
% 0.99/1.03  fof(f77,plain,(
% 0.99/1.03    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_enumset1(X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.99/1.03    inference(definition_unfolding,[],[f63,f73,f73])).
% 0.99/1.03  
% 0.99/1.03  cnf(c_15,plain,
% 0.99/1.03      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.99/1.03      inference(cnf_transformation,[],[f62]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_14,plain,
% 0.99/1.03      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 0.99/1.03      inference(cnf_transformation,[],[f60]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1445,plain,
% 0.99/1.03      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 0.99/1.03      | v1_relat_1(X0) != iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_2850,plain,
% 0.99/1.03      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top
% 0.99/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_15,c_1445]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_18,plain,
% 0.99/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 0.99/1.03      inference(cnf_transformation,[],[f64]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1569,plain,
% 0.99/1.03      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 0.99/1.03      | v1_relat_1(k1_xboole_0) ),
% 0.99/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1571,plain,
% 0.99/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 0.99/1.03      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_1569]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_9,plain,
% 0.99/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 0.99/1.03      inference(cnf_transformation,[],[f55]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1570,plain,
% 0.99/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 0.99/1.03      inference(instantiation,[status(thm)],[c_9]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1573,plain,
% 0.99/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_1570]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_2855,plain,
% 0.99/1.03      ( r1_tarski(k9_relat_1(k1_xboole_0,X0),k1_xboole_0) = iProver_top ),
% 0.99/1.03      inference(global_propositional_subsumption,
% 0.99/1.03                [status(thm)],
% 0.99/1.03                [c_2850,c_1571,c_1573]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1448,plain,
% 0.99/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_19,plain,
% 0.99/1.03      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.99/1.03      inference(cnf_transformation,[],[f65]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_13,plain,
% 0.99/1.03      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 0.99/1.03      inference(cnf_transformation,[],[f58]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_320,plain,
% 0.99/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.99/1.03      | r1_tarski(k1_relat_1(X0),X1)
% 0.99/1.03      | ~ v1_relat_1(X0) ),
% 0.99/1.03      inference(resolution,[status(thm)],[c_19,c_13]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_324,plain,
% 0.99/1.03      ( r1_tarski(k1_relat_1(X0),X1)
% 0.99/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.99/1.03      inference(global_propositional_subsumption,[status(thm)],[c_320,c_18]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_325,plain,
% 0.99/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.99/1.03      | r1_tarski(k1_relat_1(X0),X1) ),
% 0.99/1.03      inference(renaming,[status(thm)],[c_324]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1438,plain,
% 0.99/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 0.99/1.03      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1945,plain,
% 0.99/1.03      ( r1_tarski(k1_relat_1(k1_xboole_0),X0) = iProver_top ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_1448,c_1438]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_16,plain,
% 0.99/1.03      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.99/1.03      inference(cnf_transformation,[],[f61]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1946,plain,
% 0.99/1.03      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 0.99/1.03      inference(light_normalisation,[status(thm)],[c_1945,c_16]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_0,plain,
% 0.99/1.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 0.99/1.03      inference(cnf_transformation,[],[f46]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1453,plain,
% 0.99/1.03      ( X0 = X1
% 0.99/1.03      | r1_tarski(X0,X1) != iProver_top
% 0.99/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_3186,plain,
% 0.99/1.03      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_1946,c_1453]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_5675,plain,
% 0.99/1.03      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_2855,c_3186]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f81]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1452,plain,
% 0.99/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_21,plain,
% 0.99/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 0.99/1.03      | ~ r1_tarski(k2_relat_1(X0),X1)
% 0.99/1.03      | ~ v1_funct_1(X0)
% 0.99/1.03      | ~ v1_relat_1(X0) ),
% 0.99/1.03      inference(cnf_transformation,[],[f68]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_26,negated_conjecture,
% 0.99/1.03      ( v1_funct_1(sK3) ),
% 0.99/1.03      inference(cnf_transformation,[],[f69]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_282,plain,
% 0.99/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 0.99/1.03      | ~ r1_tarski(k2_relat_1(X0),X1)
% 0.99/1.03      | ~ v1_relat_1(X0)
% 0.99/1.03      | sK3 != X0 ),
% 0.99/1.03      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_283,plain,
% 0.99/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
% 0.99/1.03      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 0.99/1.03      | ~ v1_relat_1(sK3) ),
% 0.99/1.03      inference(unflattening,[status(thm)],[c_282]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1440,plain,
% 0.99/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 0.99/1.03      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 0.99/1.03      | v1_relat_1(sK3) != iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_25,negated_conjecture,
% 0.99/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
% 0.99/1.03      inference(cnf_transformation,[],[f79]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_28,plain,
% 0.99/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_284,plain,
% 0.99/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 0.99/1.03      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 0.99/1.03      | v1_relat_1(sK3) != iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_283]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1580,plain,
% 0.99/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 0.99/1.03      | v1_relat_1(sK3) ),
% 0.99/1.03      inference(instantiation,[status(thm)],[c_18]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1581,plain,
% 0.99/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) != iProver_top
% 0.99/1.03      | v1_relat_1(sK3) = iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_1580]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1586,plain,
% 0.99/1.03      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 0.99/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top ),
% 0.99/1.03      inference(global_propositional_subsumption,
% 0.99/1.03                [status(thm)],
% 0.99/1.03                [c_1440,c_28,c_284,c_1581]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1587,plain,
% 0.99/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 0.99/1.03      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 0.99/1.03      inference(renaming,[status(thm)],[c_1586]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_11,plain,
% 0.99/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 0.99/1.03      inference(cnf_transformation,[],[f56]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1446,plain,
% 0.99/1.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 0.99/1.03      | r1_tarski(X0,X1) = iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_2153,plain,
% 0.99/1.03      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 0.99/1.03      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_1587,c_1446]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_3188,plain,
% 0.99/1.03      ( k2_zfmisc_1(k1_relat_1(sK3),X0) = sK3
% 0.99/1.03      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK3),X0),sK3) != iProver_top
% 0.99/1.03      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_2153,c_1453]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_7,plain,
% 0.99/1.03      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.99/1.03      inference(cnf_transformation,[],[f85]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1441,plain,
% 0.99/1.03      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1724,plain,
% 0.99/1.03      ( r1_tarski(k1_relat_1(sK3),k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_1441,c_1438]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_5,plain,
% 0.99/1.03      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
% 0.99/1.03      | k1_enumset1(X1,X1,X1) = X0
% 0.99/1.03      | k1_xboole_0 = X0 ),
% 0.99/1.03      inference(cnf_transformation,[],[f76]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1449,plain,
% 0.99/1.03      ( k1_enumset1(X0,X0,X0) = X1
% 0.99/1.03      | k1_xboole_0 = X1
% 0.99/1.03      | r1_tarski(X1,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_2976,plain,
% 0.99/1.03      ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
% 0.99/1.03      | k1_relat_1(sK3) = k1_xboole_0 ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_1724,c_1449]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_3670,plain,
% 0.99/1.03      ( k1_relat_1(sK3) = k1_xboole_0
% 0.99/1.03      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_2976,c_1441]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_23,negated_conjecture,
% 0.99/1.03      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 0.99/1.03      inference(cnf_transformation,[],[f78]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_20,plain,
% 0.99/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.99/1.03      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 0.99/1.03      inference(cnf_transformation,[],[f66]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1608,plain,
% 0.99/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 0.99/1.03      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 0.99/1.03      inference(instantiation,[status(thm)],[c_20]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1696,plain,
% 0.99/1.03      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 0.99/1.03      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 0.99/1.03      inference(instantiation,[status(thm)],[c_1608]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1020,plain,
% 0.99/1.03      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 0.99/1.03      theory(equality) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1613,plain,
% 0.99/1.03      ( ~ r1_tarski(X0,X1)
% 0.99/1.03      | r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 0.99/1.03      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 0.99/1.03      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 0.99/1.03      inference(instantiation,[status(thm)],[c_1020]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1695,plain,
% 0.99/1.03      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 0.99/1.03      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 0.99/1.03      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 0.99/1.03      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 0.99/1.03      inference(instantiation,[status(thm)],[c_1613]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1855,plain,
% 0.99/1.03      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 0.99/1.03      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 0.99/1.03      | k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 0.99/1.03      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 0.99/1.03      inference(instantiation,[status(thm)],[c_1695]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1856,plain,
% 0.99/1.03      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 0.99/1.03      inference(instantiation,[status(thm)],[c_14]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_17,plain,
% 0.99/1.03      ( ~ v1_funct_1(X0)
% 0.99/1.03      | ~ v1_relat_1(X0)
% 0.99/1.03      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 0.99/1.03      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 0.99/1.03      inference(cnf_transformation,[],[f77]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_297,plain,
% 0.99/1.03      ( ~ v1_relat_1(X0)
% 0.99/1.03      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 0.99/1.03      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 0.99/1.03      | sK3 != X0 ),
% 0.99/1.03      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_298,plain,
% 0.99/1.03      ( ~ v1_relat_1(sK3)
% 0.99/1.03      | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 0.99/1.03      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 0.99/1.03      inference(unflattening,[status(thm)],[c_297]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1439,plain,
% 0.99/1.03      ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 0.99/1.03      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 0.99/1.03      | v1_relat_1(sK3) != iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_298]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1628,plain,
% 0.99/1.03      ( k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 0.99/1.03      | k1_enumset1(X0,X0,X0) != k1_relat_1(sK3) ),
% 0.99/1.03      inference(global_propositional_subsumption,
% 0.99/1.03                [status(thm)],
% 0.99/1.03                [c_1439,c_25,c_298,c_1580]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1629,plain,
% 0.99/1.03      ( k1_enumset1(X0,X0,X0) != k1_relat_1(sK3)
% 0.99/1.03      | k1_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 0.99/1.03      inference(renaming,[status(thm)],[c_1628]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_3664,plain,
% 0.99/1.03      ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 0.99/1.03      | k1_relat_1(sK3) = k1_xboole_0 ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_2976,c_1629]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_3709,plain,
% 0.99/1.03      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 0.99/1.03      inference(global_propositional_subsumption,
% 0.99/1.03                [status(thm)],
% 0.99/1.03                [c_3670,c_25,c_23,c_1580,c_1696,c_1855,c_1856,c_3664]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_4607,plain,
% 0.99/1.03      ( sK3 = k1_xboole_0
% 0.99/1.03      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 0.99/1.03      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 0.99/1.03      inference(light_normalisation,[status(thm)],[c_3188,c_7,c_3709]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_4611,plain,
% 0.99/1.03      ( sK3 = k1_xboole_0 | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 0.99/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_4607,c_1946]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_4615,plain,
% 0.99/1.03      ( sK3 = k1_xboole_0 ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_1452,c_4611]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1443,plain,
% 0.99/1.03      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 0.99/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_3327,plain,
% 0.99/1.03      ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 0.99/1.03      inference(superposition,[status(thm)],[c_1441,c_1443]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_1442,plain,
% 0.99/1.03      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 0.99/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_3360,plain,
% 0.99/1.03      ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 0.99/1.03      inference(demodulation,[status(thm)],[c_3327,c_1442]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_4967,plain,
% 0.99/1.03      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.99/1.03      inference(demodulation,[status(thm)],[c_4615,c_3360]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_5769,plain,
% 0.99/1.03      ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.99/1.03      inference(demodulation,[status(thm)],[c_5675,c_4967]) ).
% 0.99/1.03  
% 0.99/1.03  cnf(c_5792,plain,
% 0.99/1.03      ( $false ),
% 0.99/1.03      inference(forward_subsumption_resolution,[status(thm)],[c_5769,c_1946]) ).
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 0.99/1.03  
% 0.99/1.03  ------                               Statistics
% 0.99/1.03  
% 0.99/1.03  ------ General
% 0.99/1.03  
% 0.99/1.03  abstr_ref_over_cycles:                  0
% 0.99/1.03  abstr_ref_under_cycles:                 0
% 0.99/1.03  gc_basic_clause_elim:                   0
% 0.99/1.03  forced_gc_time:                         0
% 0.99/1.03  parsing_time:                           0.007
% 0.99/1.03  unif_index_cands_time:                  0.
% 0.99/1.03  unif_index_add_time:                    0.
% 0.99/1.03  orderings_time:                         0.
% 0.99/1.03  out_proof_time:                         0.011
% 0.99/1.03  total_time:                             0.225
% 0.99/1.03  num_of_symbols:                         49
% 0.99/1.03  num_of_terms:                           4636
% 0.99/1.03  
% 0.99/1.03  ------ Preprocessing
% 0.99/1.03  
% 0.99/1.03  num_of_splits:                          0
% 0.99/1.03  num_of_split_atoms:                     0
% 0.99/1.03  num_of_reused_defs:                     0
% 0.99/1.03  num_eq_ax_congr_red:                    9
% 0.99/1.03  num_of_sem_filtered_clauses:            1
% 0.99/1.03  num_of_subtypes:                        0
% 0.99/1.03  monotx_restored_types:                  0
% 0.99/1.03  sat_num_of_epr_types:                   0
% 0.99/1.03  sat_num_of_non_cyclic_types:            0
% 0.99/1.03  sat_guarded_non_collapsed_types:        0
% 0.99/1.03  num_pure_diseq_elim:                    0
% 0.99/1.03  simp_replaced_by:                       0
% 0.99/1.03  res_preprocessed:                       116
% 0.99/1.03  prep_upred:                             0
% 0.99/1.03  prep_unflattend:                        36
% 0.99/1.03  smt_new_axioms:                         0
% 0.99/1.03  pred_elim_cands:                        3
% 0.99/1.03  pred_elim:                              2
% 0.99/1.03  pred_elim_cl:                           3
% 0.99/1.03  pred_elim_cycles:                       6
% 0.99/1.03  merged_defs:                            8
% 0.99/1.03  merged_defs_ncl:                        0
% 0.99/1.03  bin_hyper_res:                          8
% 0.99/1.03  prep_cycles:                            4
% 0.99/1.03  pred_elim_time:                         0.011
% 0.99/1.03  splitting_time:                         0.
% 0.99/1.03  sem_filter_time:                        0.
% 0.99/1.03  monotx_time:                            0.
% 0.99/1.03  subtype_inf_time:                       0.
% 0.99/1.03  
% 0.99/1.03  ------ Problem properties
% 0.99/1.03  
% 0.99/1.03  clauses:                                22
% 0.99/1.03  conjectures:                            3
% 0.99/1.03  epr:                                    3
% 0.99/1.03  horn:                                   20
% 0.99/1.03  ground:                                 5
% 0.99/1.03  unary:                                  11
% 0.99/1.03  binary:                                 6
% 0.99/1.03  lits:                                   38
% 0.99/1.03  lits_eq:                                14
% 0.99/1.03  fd_pure:                                0
% 0.99/1.03  fd_pseudo:                              0
% 0.99/1.03  fd_cond:                                1
% 0.99/1.03  fd_pseudo_cond:                         2
% 0.99/1.03  ac_symbols:                             0
% 0.99/1.03  
% 0.99/1.03  ------ Propositional Solver
% 0.99/1.03  
% 0.99/1.03  prop_solver_calls:                      28
% 0.99/1.03  prop_fast_solver_calls:                 715
% 0.99/1.03  smt_solver_calls:                       0
% 0.99/1.03  smt_fast_solver_calls:                  0
% 0.99/1.03  prop_num_of_clauses:                    2109
% 0.99/1.03  prop_preprocess_simplified:             7096
% 0.99/1.03  prop_fo_subsumed:                       12
% 0.99/1.03  prop_solver_time:                       0.
% 0.99/1.03  smt_solver_time:                        0.
% 0.99/1.03  smt_fast_solver_time:                   0.
% 0.99/1.03  prop_fast_solver_time:                  0.
% 0.99/1.03  prop_unsat_core_time:                   0.
% 0.99/1.03  
% 0.99/1.03  ------ QBF
% 0.99/1.03  
% 0.99/1.03  qbf_q_res:                              0
% 0.99/1.03  qbf_num_tautologies:                    0
% 0.99/1.03  qbf_prep_cycles:                        0
% 0.99/1.03  
% 0.99/1.03  ------ BMC1
% 0.99/1.03  
% 0.99/1.03  bmc1_current_bound:                     -1
% 0.99/1.03  bmc1_last_solved_bound:                 -1
% 0.99/1.03  bmc1_unsat_core_size:                   -1
% 0.99/1.03  bmc1_unsat_core_parents_size:           -1
% 0.99/1.03  bmc1_merge_next_fun:                    0
% 0.99/1.03  bmc1_unsat_core_clauses_time:           0.
% 0.99/1.03  
% 0.99/1.03  ------ Instantiation
% 0.99/1.03  
% 0.99/1.03  inst_num_of_clauses:                    701
% 0.99/1.03  inst_num_in_passive:                    355
% 0.99/1.03  inst_num_in_active:                     305
% 0.99/1.03  inst_num_in_unprocessed:                41
% 0.99/1.03  inst_num_of_loops:                      330
% 0.99/1.03  inst_num_of_learning_restarts:          0
% 0.99/1.03  inst_num_moves_active_passive:          23
% 0.99/1.03  inst_lit_activity:                      0
% 0.99/1.03  inst_lit_activity_moves:                0
% 0.99/1.03  inst_num_tautologies:                   0
% 0.99/1.03  inst_num_prop_implied:                  0
% 0.99/1.03  inst_num_existing_simplified:           0
% 0.99/1.03  inst_num_eq_res_simplified:             0
% 0.99/1.03  inst_num_child_elim:                    0
% 0.99/1.03  inst_num_of_dismatching_blockings:      187
% 0.99/1.03  inst_num_of_non_proper_insts:           629
% 0.99/1.03  inst_num_of_duplicates:                 0
% 0.99/1.03  inst_inst_num_from_inst_to_res:         0
% 0.99/1.03  inst_dismatching_checking_time:         0.
% 0.99/1.03  
% 0.99/1.03  ------ Resolution
% 0.99/1.03  
% 0.99/1.03  res_num_of_clauses:                     0
% 0.99/1.03  res_num_in_passive:                     0
% 0.99/1.03  res_num_in_active:                      0
% 0.99/1.03  res_num_of_loops:                       120
% 0.99/1.03  res_forward_subset_subsumed:            79
% 0.99/1.03  res_backward_subset_subsumed:           2
% 0.99/1.03  res_forward_subsumed:                   0
% 0.99/1.03  res_backward_subsumed:                  0
% 0.99/1.03  res_forward_subsumption_resolution:     0
% 0.99/1.03  res_backward_subsumption_resolution:    0
% 0.99/1.03  res_clause_to_clause_subsumption:       334
% 0.99/1.03  res_orphan_elimination:                 0
% 0.99/1.03  res_tautology_del:                      38
% 0.99/1.03  res_num_eq_res_simplified:              0
% 0.99/1.03  res_num_sel_changes:                    0
% 0.99/1.03  res_moves_from_active_to_pass:          0
% 0.99/1.03  
% 0.99/1.03  ------ Superposition
% 0.99/1.03  
% 0.99/1.03  sup_time_total:                         0.
% 0.99/1.03  sup_time_generating:                    0.
% 0.99/1.03  sup_time_sim_full:                      0.
% 0.99/1.03  sup_time_sim_immed:                     0.
% 0.99/1.03  
% 0.99/1.03  sup_num_of_clauses:                     59
% 0.99/1.03  sup_num_in_active:                      36
% 0.99/1.03  sup_num_in_passive:                     23
% 0.99/1.03  sup_num_of_loops:                       65
% 0.99/1.03  sup_fw_superposition:                   71
% 0.99/1.03  sup_bw_superposition:                   30
% 0.99/1.03  sup_immediate_simplified:               29
% 0.99/1.03  sup_given_eliminated:                   0
% 0.99/1.03  comparisons_done:                       0
% 0.99/1.03  comparisons_avoided:                    0
% 0.99/1.03  
% 0.99/1.03  ------ Simplifications
% 0.99/1.03  
% 0.99/1.03  
% 0.99/1.03  sim_fw_subset_subsumed:                 5
% 0.99/1.03  sim_bw_subset_subsumed:                 8
% 0.99/1.03  sim_fw_subsumed:                        17
% 0.99/1.03  sim_bw_subsumed:                        3
% 0.99/1.03  sim_fw_subsumption_res:                 2
% 0.99/1.03  sim_bw_subsumption_res:                 0
% 0.99/1.03  sim_tautology_del:                      3
% 0.99/1.03  sim_eq_tautology_del:                   10
% 0.99/1.03  sim_eq_res_simp:                        0
% 0.99/1.03  sim_fw_demodulated:                     0
% 0.99/1.03  sim_bw_demodulated:                     26
% 0.99/1.03  sim_light_normalised:                   17
% 0.99/1.03  sim_joinable_taut:                      0
% 0.99/1.03  sim_joinable_simp:                      0
% 0.99/1.03  sim_ac_normalised:                      0
% 0.99/1.03  sim_smt_subsumption:                    0
% 0.99/1.03  
%------------------------------------------------------------------------------
