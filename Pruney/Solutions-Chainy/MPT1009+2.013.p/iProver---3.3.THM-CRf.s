%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:31 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.13s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 523 expanded)
%              Number of clauses        :   84 ( 164 expanded)
%              Number of leaves         :   18 ( 109 expanded)
%              Depth                    :   23
%              Number of atoms          :  369 (1268 expanded)
%              Number of equality atoms :  196 ( 538 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f33])).

fof(f44,plain,
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

fof(f45,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f44])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f50,f51])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f73,f76])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f52,f76,f76])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_enumset1(X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f67,f76,f76])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f75,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f81,plain,(
    ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f75,f76,f76])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f46])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_969,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_21,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_973,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1986,plain,
    ( v4_relat_1(sK3,k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_969,c_973])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_980,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
    | k1_enumset1(X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_985,plain,
    ( k1_enumset1(X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k1_enumset1(X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3789,plain,
    ( k1_enumset1(X0,X0,X0) = k1_relat_1(X1)
    | k1_relat_1(X1) = k1_xboole_0
    | v4_relat_1(X1,k1_enumset1(X0,X0,X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_985])).

cnf(c_9951,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1986,c_3789])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1182,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1183,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1182])).

cnf(c_10493,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9951,c_29,c_1183])).

cnf(c_10494,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_10493])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
    | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_975,plain,
    ( k1_enumset1(X0,X0,X0) != k1_relat_1(X1)
    | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_10498,plain,
    ( k1_enumset1(k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0)) = k2_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10494,c_975])).

cnf(c_12029,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_10498])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_12030,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_12029])).

cnf(c_12255,plain,
    ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12029,c_27,c_26,c_1182,c_12030])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_971,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2921,plain,
    ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_969,c_971])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_970,plain,
    ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3201,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2921,c_970])).

cnf(c_12262,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_12255,c_3201])).

cnf(c_16,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_6629,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6634,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6629])).

cnf(c_12404,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12262,c_29,c_1183,c_6634])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_977,plain,
    ( k9_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12424,plain,
    ( k9_relat_1(sK3,X0) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12404,c_977])).

cnf(c_1171,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1173,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1171])).

cnf(c_10,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1172,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1175,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1172])).

cnf(c_984,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_972,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_982,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_972,c_982])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_988,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_990,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2627,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_988,c_990])).

cnf(c_4866,plain,
    ( k7_relset_1(X0,k1_xboole_0,X1,X2) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1576,c_2627])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4873,plain,
    ( k7_relset_1(X0,k1_xboole_0,X1,X2) = k1_xboole_0
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4866,c_7])).

cnf(c_5036,plain,
    ( k7_relset_1(X0,k1_xboole_0,k1_xboole_0,X1) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_984,c_4873])).

cnf(c_2918,plain,
    ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
    inference(superposition,[status(thm)],[c_984,c_971])).

cnf(c_5238,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5036,c_2918])).

cnf(c_18,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_976,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5447,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5238,c_976])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_989,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_983,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_1984,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_983,c_973])).

cnf(c_2510,plain,
    ( v4_relat_1(k2_zfmisc_1(X0,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_989,c_1984])).

cnf(c_4111,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | v4_relat_1(X0,k1_xboole_0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_980,c_2627])).

cnf(c_4749,plain,
    ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) = k1_xboole_0
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2510,c_4111])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_4764,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4749,c_8])).

cnf(c_37,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_39,plain,
    ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_1177,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1175])).

cnf(c_4119,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4111])).

cnf(c_4913,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4764,c_39,c_1173,c_1175,c_1177,c_4119])).

cnf(c_5453,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5447,c_4913])).

cnf(c_12632,plain,
    ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12424,c_29,c_1173,c_1175,c_1183,c_5453])).

cnf(c_12640,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12632,c_3201])).

cnf(c_1456,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1459,plain,
    ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1456])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12640,c_1459])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:55:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 4.13/1.05  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.05  
% 4.13/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.13/1.05  
% 4.13/1.05  ------  iProver source info
% 4.13/1.05  
% 4.13/1.05  git: date: 2020-06-30 10:37:57 +0100
% 4.13/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.13/1.05  git: non_committed_changes: false
% 4.13/1.05  git: last_make_outside_of_git: false
% 4.13/1.05  
% 4.13/1.05  ------ 
% 4.13/1.05  ------ Parsing...
% 4.13/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.13/1.05  
% 4.13/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 4.13/1.05  
% 4.13/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.13/1.05  
% 4.13/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.13/1.05  ------ Proving...
% 4.13/1.05  ------ Problem Properties 
% 4.13/1.05  
% 4.13/1.05  
% 4.13/1.05  clauses                                 27
% 4.13/1.05  conjectures                             4
% 4.13/1.05  EPR                                     5
% 4.13/1.05  Horn                                    25
% 4.13/1.05  unary                                   12
% 4.13/1.05  binary                                  7
% 4.13/1.05  lits                                    51
% 4.13/1.05  lits eq                                 14
% 4.13/1.05  fd_pure                                 0
% 4.13/1.05  fd_pseudo                               0
% 4.13/1.05  fd_cond                                 1
% 4.13/1.05  fd_pseudo_cond                          2
% 4.13/1.05  AC symbols                              0
% 4.13/1.05  
% 4.13/1.05  ------ Input Options Time Limit: Unbounded
% 4.13/1.05  
% 4.13/1.05  
% 4.13/1.05  ------ 
% 4.13/1.05  Current options:
% 4.13/1.05  ------ 
% 4.13/1.05  
% 4.13/1.05  
% 4.13/1.05  
% 4.13/1.05  
% 4.13/1.05  ------ Proving...
% 4.13/1.05  
% 4.13/1.05  
% 4.13/1.05  % SZS status Theorem for theBenchmark.p
% 4.13/1.05  
% 4.13/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 4.13/1.05  
% 4.13/1.05  fof(f19,conjecture,(
% 4.13/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f20,negated_conjecture,(
% 4.13/1.05    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 4.13/1.05    inference(negated_conjecture,[],[f19])).
% 4.13/1.05  
% 4.13/1.05  fof(f21,plain,(
% 4.13/1.05    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 4.13/1.05    inference(pure_predicate_removal,[],[f20])).
% 4.13/1.05  
% 4.13/1.05  fof(f33,plain,(
% 4.13/1.05    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 4.13/1.05    inference(ennf_transformation,[],[f21])).
% 4.13/1.05  
% 4.13/1.05  fof(f34,plain,(
% 4.13/1.05    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 4.13/1.05    inference(flattening,[],[f33])).
% 4.13/1.05  
% 4.13/1.05  fof(f44,plain,(
% 4.13/1.05    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 4.13/1.05    introduced(choice_axiom,[])).
% 4.13/1.05  
% 4.13/1.05  fof(f45,plain,(
% 4.13/1.05    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 4.13/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f34,f44])).
% 4.13/1.05  
% 4.13/1.05  fof(f73,plain,(
% 4.13/1.05    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 4.13/1.05    inference(cnf_transformation,[],[f45])).
% 4.13/1.05  
% 4.13/1.05  fof(f3,axiom,(
% 4.13/1.05    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f50,plain,(
% 4.13/1.05    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.13/1.05    inference(cnf_transformation,[],[f3])).
% 4.13/1.05  
% 4.13/1.05  fof(f4,axiom,(
% 4.13/1.05    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f51,plain,(
% 4.13/1.05    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.13/1.05    inference(cnf_transformation,[],[f4])).
% 4.13/1.05  
% 4.13/1.05  fof(f76,plain,(
% 4.13/1.05    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 4.13/1.05    inference(definition_unfolding,[],[f50,f51])).
% 4.13/1.05  
% 4.13/1.05  fof(f82,plain,(
% 4.13/1.05    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))),
% 4.13/1.05    inference(definition_unfolding,[],[f73,f76])).
% 4.13/1.05  
% 4.13/1.05  fof(f16,axiom,(
% 4.13/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f22,plain,(
% 4.13/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 4.13/1.05    inference(pure_predicate_removal,[],[f16])).
% 4.13/1.05  
% 4.13/1.05  fof(f30,plain,(
% 4.13/1.05    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.13/1.05    inference(ennf_transformation,[],[f22])).
% 4.13/1.05  
% 4.13/1.05  fof(f69,plain,(
% 4.13/1.05    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.13/1.05    inference(cnf_transformation,[],[f30])).
% 4.13/1.05  
% 4.13/1.05  fof(f10,axiom,(
% 4.13/1.05    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f24,plain,(
% 4.13/1.05    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.13/1.05    inference(ennf_transformation,[],[f10])).
% 4.13/1.05  
% 4.13/1.05  fof(f42,plain,(
% 4.13/1.05    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.13/1.05    inference(nnf_transformation,[],[f24])).
% 4.13/1.05  
% 4.13/1.05  fof(f61,plain,(
% 4.13/1.05    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.13/1.05    inference(cnf_transformation,[],[f42])).
% 4.13/1.05  
% 4.13/1.05  fof(f5,axiom,(
% 4.13/1.05    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f37,plain,(
% 4.13/1.05    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 4.13/1.05    inference(nnf_transformation,[],[f5])).
% 4.13/1.05  
% 4.13/1.05  fof(f38,plain,(
% 4.13/1.05    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 4.13/1.05    inference(flattening,[],[f37])).
% 4.13/1.05  
% 4.13/1.05  fof(f52,plain,(
% 4.13/1.05    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 4.13/1.05    inference(cnf_transformation,[],[f38])).
% 4.13/1.05  
% 4.13/1.05  fof(f79,plain,(
% 4.13/1.05    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_enumset1(X1,X1,X1))) )),
% 4.13/1.05    inference(definition_unfolding,[],[f52,f76,f76])).
% 4.13/1.05  
% 4.13/1.05  fof(f15,axiom,(
% 4.13/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f29,plain,(
% 4.13/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.13/1.05    inference(ennf_transformation,[],[f15])).
% 4.13/1.05  
% 4.13/1.05  fof(f68,plain,(
% 4.13/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.13/1.05    inference(cnf_transformation,[],[f29])).
% 4.13/1.05  
% 4.13/1.05  fof(f14,axiom,(
% 4.13/1.05    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f27,plain,(
% 4.13/1.05    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 4.13/1.05    inference(ennf_transformation,[],[f14])).
% 4.13/1.05  
% 4.13/1.05  fof(f28,plain,(
% 4.13/1.05    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 4.13/1.05    inference(flattening,[],[f27])).
% 4.13/1.05  
% 4.13/1.05  fof(f67,plain,(
% 4.13/1.05    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.13/1.05    inference(cnf_transformation,[],[f28])).
% 4.13/1.05  
% 4.13/1.05  fof(f80,plain,(
% 4.13/1.05    ( ! [X0,X1] : (k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_enumset1(X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 4.13/1.05    inference(definition_unfolding,[],[f67,f76,f76])).
% 4.13/1.05  
% 4.13/1.05  fof(f72,plain,(
% 4.13/1.05    v1_funct_1(sK3)),
% 4.13/1.05    inference(cnf_transformation,[],[f45])).
% 4.13/1.05  
% 4.13/1.05  fof(f18,axiom,(
% 4.13/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f32,plain,(
% 4.13/1.05    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.13/1.05    inference(ennf_transformation,[],[f18])).
% 4.13/1.05  
% 4.13/1.05  fof(f71,plain,(
% 4.13/1.05    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.13/1.05    inference(cnf_transformation,[],[f32])).
% 4.13/1.05  
% 4.13/1.05  fof(f75,plain,(
% 4.13/1.05    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 4.13/1.05    inference(cnf_transformation,[],[f45])).
% 4.13/1.05  
% 4.13/1.05  fof(f81,plain,(
% 4.13/1.05    ~r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 4.13/1.05    inference(definition_unfolding,[],[f75,f76,f76])).
% 4.13/1.05  
% 4.13/1.05  fof(f12,axiom,(
% 4.13/1.05    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f25,plain,(
% 4.13/1.05    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 4.13/1.05    inference(ennf_transformation,[],[f12])).
% 4.13/1.05  
% 4.13/1.05  fof(f64,plain,(
% 4.13/1.05    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 4.13/1.05    inference(cnf_transformation,[],[f25])).
% 4.13/1.05  
% 4.13/1.05  fof(f13,axiom,(
% 4.13/1.05    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f26,plain,(
% 4.13/1.05    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 4.13/1.05    inference(ennf_transformation,[],[f13])).
% 4.13/1.05  
% 4.13/1.05  fof(f43,plain,(
% 4.13/1.05    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 4.13/1.05    inference(nnf_transformation,[],[f26])).
% 4.13/1.05  
% 4.13/1.05  fof(f66,plain,(
% 4.13/1.05    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 4.13/1.05    inference(cnf_transformation,[],[f43])).
% 4.13/1.05  
% 4.13/1.05  fof(f7,axiom,(
% 4.13/1.05    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f58,plain,(
% 4.13/1.05    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 4.13/1.05    inference(cnf_transformation,[],[f7])).
% 4.13/1.05  
% 4.13/1.05  fof(f17,axiom,(
% 4.13/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f31,plain,(
% 4.13/1.05    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.13/1.05    inference(ennf_transformation,[],[f17])).
% 4.13/1.05  
% 4.13/1.05  fof(f70,plain,(
% 4.13/1.05    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.13/1.05    inference(cnf_transformation,[],[f31])).
% 4.13/1.05  
% 4.13/1.05  fof(f8,axiom,(
% 4.13/1.05    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f41,plain,(
% 4.13/1.05    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 4.13/1.05    inference(nnf_transformation,[],[f8])).
% 4.13/1.05  
% 4.13/1.05  fof(f59,plain,(
% 4.13/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 4.13/1.05    inference(cnf_transformation,[],[f41])).
% 4.13/1.05  
% 4.13/1.05  fof(f2,axiom,(
% 4.13/1.05    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f49,plain,(
% 4.13/1.05    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.13/1.05    inference(cnf_transformation,[],[f2])).
% 4.13/1.05  
% 4.13/1.05  fof(f1,axiom,(
% 4.13/1.05    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f35,plain,(
% 4.13/1.05    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.13/1.05    inference(nnf_transformation,[],[f1])).
% 4.13/1.05  
% 4.13/1.05  fof(f36,plain,(
% 4.13/1.05    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.13/1.05    inference(flattening,[],[f35])).
% 4.13/1.05  
% 4.13/1.05  fof(f48,plain,(
% 4.13/1.05    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 4.13/1.05    inference(cnf_transformation,[],[f36])).
% 4.13/1.05  
% 4.13/1.05  fof(f6,axiom,(
% 4.13/1.05    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.13/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 4.13/1.05  
% 4.13/1.05  fof(f39,plain,(
% 4.13/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.13/1.05    inference(nnf_transformation,[],[f6])).
% 4.13/1.05  
% 4.13/1.05  fof(f40,plain,(
% 4.13/1.05    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.13/1.05    inference(flattening,[],[f39])).
% 4.13/1.05  
% 4.13/1.05  fof(f57,plain,(
% 4.13/1.05    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 4.13/1.05    inference(cnf_transformation,[],[f40])).
% 4.13/1.05  
% 4.13/1.05  fof(f87,plain,(
% 4.13/1.05    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 4.13/1.05    inference(equality_resolution,[],[f57])).
% 4.13/1.05  
% 4.13/1.05  fof(f65,plain,(
% 4.13/1.05    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.13/1.05    inference(cnf_transformation,[],[f43])).
% 4.13/1.05  
% 4.13/1.05  fof(f46,plain,(
% 4.13/1.05    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 4.13/1.05    inference(cnf_transformation,[],[f36])).
% 4.13/1.05  
% 4.13/1.05  fof(f84,plain,(
% 4.13/1.05    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.13/1.05    inference(equality_resolution,[],[f46])).
% 4.13/1.05  
% 4.13/1.05  fof(f60,plain,(
% 4.13/1.05    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 4.13/1.05    inference(cnf_transformation,[],[f41])).
% 4.13/1.05  
% 4.13/1.05  fof(f56,plain,(
% 4.13/1.05    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.13/1.05    inference(cnf_transformation,[],[f40])).
% 4.13/1.05  
% 4.13/1.05  fof(f88,plain,(
% 4.13/1.05    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.13/1.05    inference(equality_resolution,[],[f56])).
% 4.13/1.05  
% 4.13/1.05  cnf(c_26,negated_conjecture,
% 4.13/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) ),
% 4.13/1.05      inference(cnf_transformation,[],[f82]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_969,plain,
% 4.13/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_21,plain,
% 4.13/1.05      ( v4_relat_1(X0,X1)
% 4.13/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 4.13/1.05      inference(cnf_transformation,[],[f69]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_973,plain,
% 4.13/1.05      ( v4_relat_1(X0,X1) = iProver_top
% 4.13/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1986,plain,
% 4.13/1.05      ( v4_relat_1(sK3,k1_enumset1(sK0,sK0,sK0)) = iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_969,c_973]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_14,plain,
% 4.13/1.05      ( ~ v4_relat_1(X0,X1)
% 4.13/1.05      | r1_tarski(k1_relat_1(X0),X1)
% 4.13/1.05      | ~ v1_relat_1(X0) ),
% 4.13/1.05      inference(cnf_transformation,[],[f61]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_980,plain,
% 4.13/1.05      ( v4_relat_1(X0,X1) != iProver_top
% 4.13/1.05      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 4.13/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_6,plain,
% 4.13/1.05      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
% 4.13/1.05      | k1_enumset1(X1,X1,X1) = X0
% 4.13/1.05      | k1_xboole_0 = X0 ),
% 4.13/1.05      inference(cnf_transformation,[],[f79]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_985,plain,
% 4.13/1.05      ( k1_enumset1(X0,X0,X0) = X1
% 4.13/1.05      | k1_xboole_0 = X1
% 4.13/1.05      | r1_tarski(X1,k1_enumset1(X0,X0,X0)) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_3789,plain,
% 4.13/1.05      ( k1_enumset1(X0,X0,X0) = k1_relat_1(X1)
% 4.13/1.05      | k1_relat_1(X1) = k1_xboole_0
% 4.13/1.05      | v4_relat_1(X1,k1_enumset1(X0,X0,X0)) != iProver_top
% 4.13/1.05      | v1_relat_1(X1) != iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_980,c_985]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_9951,plain,
% 4.13/1.05      ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
% 4.13/1.05      | k1_relat_1(sK3) = k1_xboole_0
% 4.13/1.05      | v1_relat_1(sK3) != iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_1986,c_3789]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_29,plain,
% 4.13/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) = iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_20,plain,
% 4.13/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.13/1.05      | v1_relat_1(X0) ),
% 4.13/1.05      inference(cnf_transformation,[],[f68]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1182,plain,
% 4.13/1.05      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1)))
% 4.13/1.05      | v1_relat_1(sK3) ),
% 4.13/1.05      inference(instantiation,[status(thm)],[c_20]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1183,plain,
% 4.13/1.05      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),sK1))) != iProver_top
% 4.13/1.05      | v1_relat_1(sK3) = iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_1182]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_10493,plain,
% 4.13/1.05      ( k1_relat_1(sK3) = k1_xboole_0
% 4.13/1.05      | k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3) ),
% 4.13/1.05      inference(global_propositional_subsumption,
% 4.13/1.05                [status(thm)],
% 4.13/1.05                [c_9951,c_29,c_1183]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_10494,plain,
% 4.13/1.05      ( k1_enumset1(sK0,sK0,sK0) = k1_relat_1(sK3)
% 4.13/1.05      | k1_relat_1(sK3) = k1_xboole_0 ),
% 4.13/1.05      inference(renaming,[status(thm)],[c_10493]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_19,plain,
% 4.13/1.05      ( ~ v1_funct_1(X0)
% 4.13/1.05      | ~ v1_relat_1(X0)
% 4.13/1.05      | k1_enumset1(X1,X1,X1) != k1_relat_1(X0)
% 4.13/1.05      | k1_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 4.13/1.05      inference(cnf_transformation,[],[f80]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_975,plain,
% 4.13/1.05      ( k1_enumset1(X0,X0,X0) != k1_relat_1(X1)
% 4.13/1.05      | k1_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
% 4.13/1.05      | v1_funct_1(X1) != iProver_top
% 4.13/1.05      | v1_relat_1(X1) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_10498,plain,
% 4.13/1.05      ( k1_enumset1(k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0)) = k2_relat_1(X0)
% 4.13/1.05      | k1_relat_1(X0) != k1_relat_1(sK3)
% 4.13/1.05      | k1_relat_1(sK3) = k1_xboole_0
% 4.13/1.05      | v1_funct_1(X0) != iProver_top
% 4.13/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_10494,c_975]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_12029,plain,
% 4.13/1.05      ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 4.13/1.05      | k1_relat_1(sK3) = k1_xboole_0
% 4.13/1.05      | v1_funct_1(sK3) != iProver_top
% 4.13/1.05      | v1_relat_1(sK3) != iProver_top ),
% 4.13/1.05      inference(equality_resolution,[status(thm)],[c_10498]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_27,negated_conjecture,
% 4.13/1.05      ( v1_funct_1(sK3) ),
% 4.13/1.05      inference(cnf_transformation,[],[f72]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_12030,plain,
% 4.13/1.05      ( ~ v1_funct_1(sK3)
% 4.13/1.05      | ~ v1_relat_1(sK3)
% 4.13/1.05      | k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 4.13/1.05      | k1_relat_1(sK3) = k1_xboole_0 ),
% 4.13/1.05      inference(predicate_to_equality_rev,[status(thm)],[c_12029]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_12255,plain,
% 4.13/1.05      ( k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 4.13/1.05      | k1_relat_1(sK3) = k1_xboole_0 ),
% 4.13/1.05      inference(global_propositional_subsumption,
% 4.13/1.05                [status(thm)],
% 4.13/1.05                [c_12029,c_27,c_26,c_1182,c_12030]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_23,plain,
% 4.13/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.13/1.05      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 4.13/1.05      inference(cnf_transformation,[],[f71]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_971,plain,
% 4.13/1.05      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 4.13/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_2921,plain,
% 4.13/1.05      ( k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_969,c_971]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_24,negated_conjecture,
% 4.13/1.05      ( ~ r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 4.13/1.05      inference(cnf_transformation,[],[f81]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_970,plain,
% 4.13/1.05      ( r1_tarski(k7_relset_1(k1_enumset1(sK0,sK0,sK0),sK1,sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_3201,plain,
% 4.13/1.05      ( r1_tarski(k9_relat_1(sK3,sK2),k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 4.13/1.05      inference(demodulation,[status(thm)],[c_2921,c_970]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_12262,plain,
% 4.13/1.05      ( k1_relat_1(sK3) = k1_xboole_0
% 4.13/1.05      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_12255,c_3201]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_16,plain,
% 4.13/1.05      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 4.13/1.05      inference(cnf_transformation,[],[f64]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_6629,plain,
% 4.13/1.05      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 4.13/1.05      | ~ v1_relat_1(sK3) ),
% 4.13/1.05      inference(instantiation,[status(thm)],[c_16]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_6634,plain,
% 4.13/1.05      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) = iProver_top
% 4.13/1.05      | v1_relat_1(sK3) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_6629]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_12404,plain,
% 4.13/1.05      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 4.13/1.05      inference(global_propositional_subsumption,
% 4.13/1.05                [status(thm)],
% 4.13/1.05                [c_12262,c_29,c_1183,c_6634]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_17,plain,
% 4.13/1.05      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 4.13/1.05      | ~ v1_relat_1(X0)
% 4.13/1.05      | k9_relat_1(X0,X1) = k1_xboole_0 ),
% 4.13/1.05      inference(cnf_transformation,[],[f66]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_977,plain,
% 4.13/1.05      ( k9_relat_1(X0,X1) = k1_xboole_0
% 4.13/1.05      | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
% 4.13/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_12424,plain,
% 4.13/1.05      ( k9_relat_1(sK3,X0) = k1_xboole_0
% 4.13/1.05      | r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 4.13/1.05      | v1_relat_1(sK3) != iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_12404,c_977]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1171,plain,
% 4.13/1.05      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 4.13/1.05      | v1_relat_1(k1_xboole_0) ),
% 4.13/1.05      inference(instantiation,[status(thm)],[c_20]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1173,plain,
% 4.13/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 4.13/1.05      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_1171]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_10,plain,
% 4.13/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 4.13/1.05      inference(cnf_transformation,[],[f58]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1172,plain,
% 4.13/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 4.13/1.05      inference(instantiation,[status(thm)],[c_10]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1175,plain,
% 4.13/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_1172]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_984,plain,
% 4.13/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_22,plain,
% 4.13/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.13/1.05      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 4.13/1.05      inference(cnf_transformation,[],[f70]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_972,plain,
% 4.13/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.13/1.05      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_12,plain,
% 4.13/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 4.13/1.05      inference(cnf_transformation,[],[f59]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_982,plain,
% 4.13/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 4.13/1.05      | r1_tarski(X0,X1) = iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1576,plain,
% 4.13/1.05      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 4.13/1.05      | r1_tarski(k7_relset_1(X1,X2,X0,X3),X2) = iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_972,c_982]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_3,plain,
% 4.13/1.05      ( r1_tarski(k1_xboole_0,X0) ),
% 4.13/1.05      inference(cnf_transformation,[],[f49]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_988,plain,
% 4.13/1.05      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_0,plain,
% 4.13/1.05      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 4.13/1.05      inference(cnf_transformation,[],[f48]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_990,plain,
% 4.13/1.05      ( X0 = X1
% 4.13/1.05      | r1_tarski(X0,X1) != iProver_top
% 4.13/1.05      | r1_tarski(X1,X0) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_2627,plain,
% 4.13/1.05      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_988,c_990]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_4866,plain,
% 4.13/1.05      ( k7_relset_1(X0,k1_xboole_0,X1,X2) = k1_xboole_0
% 4.13/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) != iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_1576,c_2627]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_7,plain,
% 4.13/1.05      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 4.13/1.05      inference(cnf_transformation,[],[f87]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_4873,plain,
% 4.13/1.05      ( k7_relset_1(X0,k1_xboole_0,X1,X2) = k1_xboole_0
% 4.13/1.05      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 4.13/1.05      inference(light_normalisation,[status(thm)],[c_4866,c_7]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_5036,plain,
% 4.13/1.05      ( k7_relset_1(X0,k1_xboole_0,k1_xboole_0,X1) = k1_xboole_0 ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_984,c_4873]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_2918,plain,
% 4.13/1.05      ( k7_relset_1(X0,X1,k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,X2) ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_984,c_971]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_5238,plain,
% 4.13/1.05      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_5036,c_2918]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_18,plain,
% 4.13/1.05      ( r1_xboole_0(k1_relat_1(X0),X1)
% 4.13/1.05      | ~ v1_relat_1(X0)
% 4.13/1.05      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 4.13/1.05      inference(cnf_transformation,[],[f65]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_976,plain,
% 4.13/1.05      ( k9_relat_1(X0,X1) != k1_xboole_0
% 4.13/1.05      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 4.13/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_5447,plain,
% 4.13/1.05      ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 4.13/1.05      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_5238,c_976]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_2,plain,
% 4.13/1.05      ( r1_tarski(X0,X0) ),
% 4.13/1.05      inference(cnf_transformation,[],[f84]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_989,plain,
% 4.13/1.05      ( r1_tarski(X0,X0) = iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_11,plain,
% 4.13/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 4.13/1.05      inference(cnf_transformation,[],[f60]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_983,plain,
% 4.13/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 4.13/1.05      | r1_tarski(X0,X1) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1984,plain,
% 4.13/1.05      ( v4_relat_1(X0,X1) = iProver_top
% 4.13/1.05      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_983,c_973]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_2510,plain,
% 4.13/1.05      ( v4_relat_1(k2_zfmisc_1(X0,X1),X0) = iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_989,c_1984]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_4111,plain,
% 4.13/1.05      ( k1_relat_1(X0) = k1_xboole_0
% 4.13/1.05      | v4_relat_1(X0,k1_xboole_0) != iProver_top
% 4.13/1.05      | v1_relat_1(X0) != iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_980,c_2627]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_4749,plain,
% 4.13/1.05      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) = k1_xboole_0
% 4.13/1.05      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,X0)) != iProver_top ),
% 4.13/1.05      inference(superposition,[status(thm)],[c_2510,c_4111]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_8,plain,
% 4.13/1.05      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 4.13/1.05      inference(cnf_transformation,[],[f88]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_4764,plain,
% 4.13/1.05      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 4.13/1.05      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.13/1.05      inference(light_normalisation,[status(thm)],[c_4749,c_8]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_37,plain,
% 4.13/1.05      ( v4_relat_1(X0,X1) = iProver_top
% 4.13/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_39,plain,
% 4.13/1.05      ( v4_relat_1(k1_xboole_0,k1_xboole_0) = iProver_top
% 4.13/1.05      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 4.13/1.05      inference(instantiation,[status(thm)],[c_37]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1177,plain,
% 4.13/1.05      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 4.13/1.05      inference(instantiation,[status(thm)],[c_1175]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_4119,plain,
% 4.13/1.05      ( k1_relat_1(k1_xboole_0) = k1_xboole_0
% 4.13/1.05      | v4_relat_1(k1_xboole_0,k1_xboole_0) != iProver_top
% 4.13/1.05      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.13/1.05      inference(instantiation,[status(thm)],[c_4111]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_4913,plain,
% 4.13/1.05      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 4.13/1.05      inference(global_propositional_subsumption,
% 4.13/1.05                [status(thm)],
% 4.13/1.05                [c_4764,c_39,c_1173,c_1175,c_1177,c_4119]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_5453,plain,
% 4.13/1.05      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top
% 4.13/1.05      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 4.13/1.05      inference(light_normalisation,[status(thm)],[c_5447,c_4913]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_12632,plain,
% 4.13/1.05      ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
% 4.13/1.05      inference(global_propositional_subsumption,
% 4.13/1.05                [status(thm)],
% 4.13/1.05                [c_12424,c_29,c_1173,c_1175,c_1183,c_5453]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_12640,plain,
% 4.13/1.05      ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 4.13/1.05      inference(demodulation,[status(thm)],[c_12632,c_3201]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1456,plain,
% 4.13/1.05      ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 4.13/1.05      inference(instantiation,[status(thm)],[c_3]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(c_1459,plain,
% 4.13/1.05      ( r1_tarski(k1_xboole_0,k1_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
% 4.13/1.05      inference(predicate_to_equality,[status(thm)],[c_1456]) ).
% 4.13/1.05  
% 4.13/1.05  cnf(contradiction,plain,
% 4.13/1.05      ( $false ),
% 4.13/1.05      inference(minisat,[status(thm)],[c_12640,c_1459]) ).
% 4.13/1.05  
% 4.13/1.05  
% 4.13/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 4.13/1.05  
% 4.13/1.05  ------                               Statistics
% 4.13/1.05  
% 4.13/1.05  ------ Selected
% 4.13/1.05  
% 4.13/1.05  total_time:                             0.414
% 4.13/1.05  
%------------------------------------------------------------------------------
