%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:36 EST 2020

% Result     : Theorem 3.11s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 620 expanded)
%              Number of clauses        :   67 ( 129 expanded)
%              Number of leaves         :   19 ( 164 expanded)
%              Depth                    :   19
%              Number of atoms          :  378 (1520 expanded)
%              Number of equality atoms :  208 ( 820 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f18,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f39,plain,
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

fof(f40,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f39])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f40])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f72])).

fof(f85,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f66,plain,(
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

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

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

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ~ ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
    <=> ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
        | ( k1_enumset1(X0,X1,X2) != X3
          & k2_tarski(X0,X2) != X3
          & k2_tarski(X1,X2) != X3
          & k2_tarski(X0,X1) != X3
          & k1_tarski(X2) != X3
          & k1_tarski(X1) != X3
          & k1_tarski(X0) != X3
          & k1_xboole_0 != X3 ) )
      & ( k1_enumset1(X0,X1,X2) = X3
        | k2_tarski(X0,X2) = X3
        | k2_tarski(X1,X2) = X3
        | k2_tarski(X0,X1) = X3
        | k1_tarski(X2) = X3
        | k1_tarski(X1) = X3
        | k1_tarski(X0) = X3
        | k1_xboole_0 = X3
        | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ) ),
    inference(flattening,[],[f34])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_enumset1(X0,X1,X2) = X3
      | k2_tarski(X0,X2) = X3
      | k2_tarski(X1,X2) = X3
      | k2_tarski(X0,X1) = X3
      | k1_tarski(X2) = X3
      | k1_tarski(X1) = X3
      | k1_tarski(X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k1_enumset1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_enumset1(X0,X0,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X2) = X3
      | k2_enumset1(X1,X1,X1,X2) = X3
      | k2_enumset1(X0,X0,X0,X1) = X3
      | k2_enumset1(X2,X2,X2,X2) = X3
      | k2_enumset1(X1,X1,X1,X1) = X3
      | k2_enumset1(X0,X0,X0,X0) = X3
      | k1_xboole_0 = X3
      | ~ r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) ) ),
    inference(definition_unfolding,[],[f47,f46,f72,f72,f72,f73,f73,f73,f46])).

fof(f71,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f84,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f71,f73,f73])).

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

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f64,f73,f73])).

fof(f68,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f40])).

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

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k1_enumset1(X0,X1,X2))
      | k1_xboole_0 != X3 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))
      | k1_xboole_0 != X3 ) ),
    inference(definition_unfolding,[],[f48,f46])).

fof(f95,plain,(
    ! [X2,X0,X1] : r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f81])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1547,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_16])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_365,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_21])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_365])).

cnf(c_1545,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_1925,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1547,c_1545])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1557,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3628,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1925,c_1557])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_342,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_343,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_342])).

cnf(c_344,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_346,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_344])).

cnf(c_1727,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1728,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1727])).

cnf(c_1733,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_1834,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1772,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1887,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1772])).

cnf(c_1013,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1749,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_1013])).

cnf(c_1886,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1749])).

cnf(c_2013,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_17,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1819,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2014,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1819])).

cnf(c_1012,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1910,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_2324,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1910])).

cnf(c_1011,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3471,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_3895,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3628,c_26,c_29,c_24,c_346,c_1727,c_1728,c_1733,c_1834,c_1887,c_2013,c_2014,c_2324,c_3471])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1551,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3910,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3895,c_1551])).

cnf(c_1820,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4088,plain,
    ( k2_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3910,c_26,c_29,c_24,c_346,c_1727,c_1728,c_1733,c_1820,c_1834,c_1887,c_2013,c_2014,c_2324,c_3471])).

cnf(c_1553,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4094,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4088,c_1553])).

cnf(c_4184,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4094,c_29,c_1728])).

cnf(c_12,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1556,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1554,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1842,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1556,c_1554])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1567,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2622,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1842,c_1567])).

cnf(c_4192,plain,
    ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4184,c_2622])).

cnf(c_1549,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2701,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1547,c_1549])).

cnf(c_1548,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2816,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2701,c_1548])).

cnf(c_4202,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4192,c_2816])).

cnf(c_10,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2482,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2485,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2482])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4202,c_2485])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:29:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.11/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.11/0.99  
% 3.11/0.99  ------  iProver source info
% 3.11/0.99  
% 3.11/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.11/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.11/0.99  git: non_committed_changes: false
% 3.11/0.99  git: last_make_outside_of_git: false
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    --mode clausify
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         false
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     num_symb
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       true
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     false
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   []
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_full_bw                           [BwDemod]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  ------ Parsing...
% 3.11/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.11/0.99  ------ Proving...
% 3.11/0.99  ------ Problem Properties 
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  clauses                                 24
% 3.11/0.99  conjectures                             3
% 3.11/0.99  EPR                                     3
% 3.11/0.99  Horn                                    23
% 3.11/0.99  unary                                   13
% 3.11/0.99  binary                                  6
% 3.11/0.99  lits                                    46
% 3.11/0.99  lits eq                                 17
% 3.11/0.99  fd_pure                                 0
% 3.11/0.99  fd_pseudo                               0
% 3.11/0.99  fd_cond                                 0
% 3.11/0.99  fd_pseudo_cond                          2
% 3.11/0.99  AC symbols                              0
% 3.11/0.99  
% 3.11/0.99  ------ Schedule dynamic 5 is on 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ 
% 3.11/0.99  Current options:
% 3.11/0.99  ------ 
% 3.11/0.99  
% 3.11/0.99  ------ Input Options
% 3.11/0.99  
% 3.11/0.99  --out_options                           all
% 3.11/0.99  --tptp_safe_out                         true
% 3.11/0.99  --problem_path                          ""
% 3.11/0.99  --include_path                          ""
% 3.11/0.99  --clausifier                            res/vclausify_rel
% 3.11/0.99  --clausifier_options                    --mode clausify
% 3.11/0.99  --stdin                                 false
% 3.11/0.99  --stats_out                             all
% 3.11/0.99  
% 3.11/0.99  ------ General Options
% 3.11/0.99  
% 3.11/0.99  --fof                                   false
% 3.11/0.99  --time_out_real                         305.
% 3.11/0.99  --time_out_virtual                      -1.
% 3.11/0.99  --symbol_type_check                     false
% 3.11/0.99  --clausify_out                          false
% 3.11/0.99  --sig_cnt_out                           false
% 3.11/0.99  --trig_cnt_out                          false
% 3.11/0.99  --trig_cnt_out_tolerance                1.
% 3.11/0.99  --trig_cnt_out_sk_spl                   false
% 3.11/0.99  --abstr_cl_out                          false
% 3.11/0.99  
% 3.11/0.99  ------ Global Options
% 3.11/0.99  
% 3.11/0.99  --schedule                              default
% 3.11/0.99  --add_important_lit                     false
% 3.11/0.99  --prop_solver_per_cl                    1000
% 3.11/0.99  --min_unsat_core                        false
% 3.11/0.99  --soft_assumptions                      false
% 3.11/0.99  --soft_lemma_size                       3
% 3.11/0.99  --prop_impl_unit_size                   0
% 3.11/0.99  --prop_impl_unit                        []
% 3.11/0.99  --share_sel_clauses                     true
% 3.11/0.99  --reset_solvers                         false
% 3.11/0.99  --bc_imp_inh                            [conj_cone]
% 3.11/0.99  --conj_cone_tolerance                   3.
% 3.11/0.99  --extra_neg_conj                        none
% 3.11/0.99  --large_theory_mode                     true
% 3.11/0.99  --prolific_symb_bound                   200
% 3.11/0.99  --lt_threshold                          2000
% 3.11/0.99  --clause_weak_htbl                      true
% 3.11/0.99  --gc_record_bc_elim                     false
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing Options
% 3.11/0.99  
% 3.11/0.99  --preprocessing_flag                    true
% 3.11/0.99  --time_out_prep_mult                    0.1
% 3.11/0.99  --splitting_mode                        input
% 3.11/0.99  --splitting_grd                         true
% 3.11/0.99  --splitting_cvd                         false
% 3.11/0.99  --splitting_cvd_svl                     false
% 3.11/0.99  --splitting_nvd                         32
% 3.11/0.99  --sub_typing                            true
% 3.11/0.99  --prep_gs_sim                           true
% 3.11/0.99  --prep_unflatten                        true
% 3.11/0.99  --prep_res_sim                          true
% 3.11/0.99  --prep_upred                            true
% 3.11/0.99  --prep_sem_filter                       exhaustive
% 3.11/0.99  --prep_sem_filter_out                   false
% 3.11/0.99  --pred_elim                             true
% 3.11/0.99  --res_sim_input                         true
% 3.11/0.99  --eq_ax_congr_red                       true
% 3.11/0.99  --pure_diseq_elim                       true
% 3.11/0.99  --brand_transform                       false
% 3.11/0.99  --non_eq_to_eq                          false
% 3.11/0.99  --prep_def_merge                        true
% 3.11/0.99  --prep_def_merge_prop_impl              false
% 3.11/0.99  --prep_def_merge_mbd                    true
% 3.11/0.99  --prep_def_merge_tr_red                 false
% 3.11/0.99  --prep_def_merge_tr_cl                  false
% 3.11/0.99  --smt_preprocessing                     true
% 3.11/0.99  --smt_ac_axioms                         fast
% 3.11/0.99  --preprocessed_out                      false
% 3.11/0.99  --preprocessed_stats                    false
% 3.11/0.99  
% 3.11/0.99  ------ Abstraction refinement Options
% 3.11/0.99  
% 3.11/0.99  --abstr_ref                             []
% 3.11/0.99  --abstr_ref_prep                        false
% 3.11/0.99  --abstr_ref_until_sat                   false
% 3.11/0.99  --abstr_ref_sig_restrict                funpre
% 3.11/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.11/0.99  --abstr_ref_under                       []
% 3.11/0.99  
% 3.11/0.99  ------ SAT Options
% 3.11/0.99  
% 3.11/0.99  --sat_mode                              false
% 3.11/0.99  --sat_fm_restart_options                ""
% 3.11/0.99  --sat_gr_def                            false
% 3.11/0.99  --sat_epr_types                         true
% 3.11/0.99  --sat_non_cyclic_types                  false
% 3.11/0.99  --sat_finite_models                     false
% 3.11/0.99  --sat_fm_lemmas                         false
% 3.11/0.99  --sat_fm_prep                           false
% 3.11/0.99  --sat_fm_uc_incr                        true
% 3.11/0.99  --sat_out_model                         small
% 3.11/0.99  --sat_out_clauses                       false
% 3.11/0.99  
% 3.11/0.99  ------ QBF Options
% 3.11/0.99  
% 3.11/0.99  --qbf_mode                              false
% 3.11/0.99  --qbf_elim_univ                         false
% 3.11/0.99  --qbf_dom_inst                          none
% 3.11/0.99  --qbf_dom_pre_inst                      false
% 3.11/0.99  --qbf_sk_in                             false
% 3.11/0.99  --qbf_pred_elim                         true
% 3.11/0.99  --qbf_split                             512
% 3.11/0.99  
% 3.11/0.99  ------ BMC1 Options
% 3.11/0.99  
% 3.11/0.99  --bmc1_incremental                      false
% 3.11/0.99  --bmc1_axioms                           reachable_all
% 3.11/0.99  --bmc1_min_bound                        0
% 3.11/0.99  --bmc1_max_bound                        -1
% 3.11/0.99  --bmc1_max_bound_default                -1
% 3.11/0.99  --bmc1_symbol_reachability              true
% 3.11/0.99  --bmc1_property_lemmas                  false
% 3.11/0.99  --bmc1_k_induction                      false
% 3.11/0.99  --bmc1_non_equiv_states                 false
% 3.11/0.99  --bmc1_deadlock                         false
% 3.11/0.99  --bmc1_ucm                              false
% 3.11/0.99  --bmc1_add_unsat_core                   none
% 3.11/0.99  --bmc1_unsat_core_children              false
% 3.11/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.11/0.99  --bmc1_out_stat                         full
% 3.11/0.99  --bmc1_ground_init                      false
% 3.11/0.99  --bmc1_pre_inst_next_state              false
% 3.11/0.99  --bmc1_pre_inst_state                   false
% 3.11/0.99  --bmc1_pre_inst_reach_state             false
% 3.11/0.99  --bmc1_out_unsat_core                   false
% 3.11/0.99  --bmc1_aig_witness_out                  false
% 3.11/0.99  --bmc1_verbose                          false
% 3.11/0.99  --bmc1_dump_clauses_tptp                false
% 3.11/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.11/0.99  --bmc1_dump_file                        -
% 3.11/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.11/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.11/0.99  --bmc1_ucm_extend_mode                  1
% 3.11/0.99  --bmc1_ucm_init_mode                    2
% 3.11/0.99  --bmc1_ucm_cone_mode                    none
% 3.11/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.11/0.99  --bmc1_ucm_relax_model                  4
% 3.11/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.11/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.11/0.99  --bmc1_ucm_layered_model                none
% 3.11/0.99  --bmc1_ucm_max_lemma_size               10
% 3.11/0.99  
% 3.11/0.99  ------ AIG Options
% 3.11/0.99  
% 3.11/0.99  --aig_mode                              false
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation Options
% 3.11/0.99  
% 3.11/0.99  --instantiation_flag                    true
% 3.11/0.99  --inst_sos_flag                         false
% 3.11/0.99  --inst_sos_phase                        true
% 3.11/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.11/0.99  --inst_lit_sel_side                     none
% 3.11/0.99  --inst_solver_per_active                1400
% 3.11/0.99  --inst_solver_calls_frac                1.
% 3.11/0.99  --inst_passive_queue_type               priority_queues
% 3.11/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.11/0.99  --inst_passive_queues_freq              [25;2]
% 3.11/0.99  --inst_dismatching                      true
% 3.11/0.99  --inst_eager_unprocessed_to_passive     true
% 3.11/0.99  --inst_prop_sim_given                   true
% 3.11/0.99  --inst_prop_sim_new                     false
% 3.11/0.99  --inst_subs_new                         false
% 3.11/0.99  --inst_eq_res_simp                      false
% 3.11/0.99  --inst_subs_given                       false
% 3.11/0.99  --inst_orphan_elimination               true
% 3.11/0.99  --inst_learning_loop_flag               true
% 3.11/0.99  --inst_learning_start                   3000
% 3.11/0.99  --inst_learning_factor                  2
% 3.11/0.99  --inst_start_prop_sim_after_learn       3
% 3.11/0.99  --inst_sel_renew                        solver
% 3.11/0.99  --inst_lit_activity_flag                true
% 3.11/0.99  --inst_restr_to_given                   false
% 3.11/0.99  --inst_activity_threshold               500
% 3.11/0.99  --inst_out_proof                        true
% 3.11/0.99  
% 3.11/0.99  ------ Resolution Options
% 3.11/0.99  
% 3.11/0.99  --resolution_flag                       false
% 3.11/0.99  --res_lit_sel                           adaptive
% 3.11/0.99  --res_lit_sel_side                      none
% 3.11/0.99  --res_ordering                          kbo
% 3.11/0.99  --res_to_prop_solver                    active
% 3.11/0.99  --res_prop_simpl_new                    false
% 3.11/0.99  --res_prop_simpl_given                  true
% 3.11/0.99  --res_passive_queue_type                priority_queues
% 3.11/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.11/0.99  --res_passive_queues_freq               [15;5]
% 3.11/0.99  --res_forward_subs                      full
% 3.11/0.99  --res_backward_subs                     full
% 3.11/0.99  --res_forward_subs_resolution           true
% 3.11/0.99  --res_backward_subs_resolution          true
% 3.11/0.99  --res_orphan_elimination                true
% 3.11/0.99  --res_time_limit                        2.
% 3.11/0.99  --res_out_proof                         true
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Options
% 3.11/0.99  
% 3.11/0.99  --superposition_flag                    true
% 3.11/0.99  --sup_passive_queue_type                priority_queues
% 3.11/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.11/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.11/0.99  --demod_completeness_check              fast
% 3.11/0.99  --demod_use_ground                      true
% 3.11/0.99  --sup_to_prop_solver                    passive
% 3.11/0.99  --sup_prop_simpl_new                    true
% 3.11/0.99  --sup_prop_simpl_given                  true
% 3.11/0.99  --sup_fun_splitting                     false
% 3.11/0.99  --sup_smt_interval                      50000
% 3.11/0.99  
% 3.11/0.99  ------ Superposition Simplification Setup
% 3.11/0.99  
% 3.11/0.99  --sup_indices_passive                   []
% 3.11/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.11/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.11/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_full_bw                           [BwDemod]
% 3.11/0.99  --sup_immed_triv                        [TrivRules]
% 3.11/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.11/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_immed_bw_main                     []
% 3.11/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.11/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.11/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.11/0.99  
% 3.11/0.99  ------ Combination Options
% 3.11/0.99  
% 3.11/0.99  --comb_res_mult                         3
% 3.11/0.99  --comb_sup_mult                         2
% 3.11/0.99  --comb_inst_mult                        10
% 3.11/0.99  
% 3.11/0.99  ------ Debug Options
% 3.11/0.99  
% 3.11/0.99  --dbg_backtrace                         false
% 3.11/0.99  --dbg_dump_prop_clauses                 false
% 3.11/0.99  --dbg_dump_prop_clauses_file            -
% 3.11/0.99  --dbg_out_stat                          false
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  ------ Proving...
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  % SZS status Theorem for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  fof(f16,conjecture,(
% 3.11/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f17,negated_conjecture,(
% 3.11/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.11/0.99    inference(negated_conjecture,[],[f16])).
% 3.11/0.99  
% 3.11/0.99  fof(f18,plain,(
% 3.11/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.11/0.99    inference(pure_predicate_removal,[],[f17])).
% 3.11/0.99  
% 3.11/0.99  fof(f30,plain,(
% 3.11/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 3.11/0.99    inference(ennf_transformation,[],[f18])).
% 3.11/0.99  
% 3.11/0.99  fof(f31,plain,(
% 3.11/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 3.11/0.99    inference(flattening,[],[f30])).
% 3.11/0.99  
% 3.11/0.99  fof(f39,plain,(
% 3.11/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 3.11/0.99    introduced(choice_axiom,[])).
% 3.11/0.99  
% 3.11/0.99  fof(f40,plain,(
% 3.11/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 3.11/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f39])).
% 3.11/0.99  
% 3.11/0.99  fof(f69,plain,(
% 3.11/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.11/0.99    inference(cnf_transformation,[],[f40])).
% 3.11/0.99  
% 3.11/0.99  fof(f2,axiom,(
% 3.11/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f44,plain,(
% 3.11/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f2])).
% 3.11/0.99  
% 3.11/0.99  fof(f3,axiom,(
% 3.11/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f45,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f3])).
% 3.11/0.99  
% 3.11/0.99  fof(f4,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f46,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f4])).
% 3.11/0.99  
% 3.11/0.99  fof(f72,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f45,f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f73,plain,(
% 3.11/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f44,f72])).
% 3.11/0.99  
% 3.11/0.99  fof(f85,plain,(
% 3.11/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 3.11/0.99    inference(definition_unfolding,[],[f69,f73])).
% 3.11/0.99  
% 3.11/0.99  fof(f14,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f19,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.11/0.99    inference(pure_predicate_removal,[],[f14])).
% 3.11/0.99  
% 3.11/0.99  fof(f28,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f19])).
% 3.11/0.99  
% 3.11/0.99  fof(f66,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f28])).
% 3.11/0.99  
% 3.11/0.99  fof(f9,axiom,(
% 3.11/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f22,plain,(
% 3.11/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.11/0.99    inference(ennf_transformation,[],[f9])).
% 3.11/0.99  
% 3.11/0.99  fof(f37,plain,(
% 3.11/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.11/0.99    inference(nnf_transformation,[],[f22])).
% 3.11/0.99  
% 3.11/0.99  fof(f59,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f37])).
% 3.11/0.99  
% 3.11/0.99  fof(f13,axiom,(
% 3.11/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f27,plain,(
% 3.11/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f13])).
% 3.11/0.99  
% 3.11/0.99  fof(f65,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f27])).
% 3.11/0.99  
% 3.11/0.99  fof(f5,axiom,(
% 3.11/0.99    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f21,plain,(
% 3.11/0.99    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 3.11/0.99    inference(ennf_transformation,[],[f5])).
% 3.11/0.99  
% 3.11/0.99  fof(f34,plain,(
% 3.11/0.99    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 3.11/0.99    inference(nnf_transformation,[],[f21])).
% 3.11/0.99  
% 3.11/0.99  fof(f35,plain,(
% 3.11/0.99    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 3.11/0.99    inference(flattening,[],[f34])).
% 3.11/0.99  
% 3.11/0.99  fof(f47,plain,(
% 3.11/0.99    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f35])).
% 3.11/0.99  
% 3.11/0.99  fof(f82,plain,(
% 3.11/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 3.11/0.99    inference(definition_unfolding,[],[f47,f46,f72,f72,f72,f73,f73,f73,f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f71,plain,(
% 3.11/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 3.11/0.99    inference(cnf_transformation,[],[f40])).
% 3.11/0.99  
% 3.11/0.99  fof(f84,plain,(
% 3.11/0.99    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 3.11/0.99    inference(definition_unfolding,[],[f71,f73,f73])).
% 3.11/0.99  
% 3.11/0.99  fof(f12,axiom,(
% 3.11/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f25,plain,(
% 3.11/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.11/0.99    inference(ennf_transformation,[],[f12])).
% 3.11/0.99  
% 3.11/0.99  fof(f26,plain,(
% 3.11/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.11/0.99    inference(flattening,[],[f25])).
% 3.11/0.99  
% 3.11/0.99  fof(f64,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f26])).
% 3.11/0.99  
% 3.11/0.99  fof(f83,plain,(
% 3.11/0.99    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.11/0.99    inference(definition_unfolding,[],[f64,f73,f73])).
% 3.11/0.99  
% 3.11/0.99  fof(f68,plain,(
% 3.11/0.99    v1_funct_1(sK3)),
% 3.11/0.99    inference(cnf_transformation,[],[f40])).
% 3.11/0.99  
% 3.11/0.99  fof(f15,axiom,(
% 3.11/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f29,plain,(
% 3.11/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.11/0.99    inference(ennf_transformation,[],[f15])).
% 3.11/0.99  
% 3.11/0.99  fof(f67,plain,(
% 3.11/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f29])).
% 3.11/0.99  
% 3.11/0.99  fof(f10,axiom,(
% 3.11/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f23,plain,(
% 3.11/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.11/0.99    inference(ennf_transformation,[],[f10])).
% 3.11/0.99  
% 3.11/0.99  fof(f61,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f23])).
% 3.11/0.99  
% 3.11/0.99  fof(f11,axiom,(
% 3.11/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f24,plain,(
% 3.11/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(ennf_transformation,[],[f11])).
% 3.11/0.99  
% 3.11/0.99  fof(f38,plain,(
% 3.11/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.11/0.99    inference(nnf_transformation,[],[f24])).
% 3.11/0.99  
% 3.11/0.99  fof(f62,plain,(
% 3.11/0.99    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f38])).
% 3.11/0.99  
% 3.11/0.99  fof(f6,axiom,(
% 3.11/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f56,plain,(
% 3.11/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f6])).
% 3.11/0.99  
% 3.11/0.99  fof(f7,axiom,(
% 3.11/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f36,plain,(
% 3.11/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.11/0.99    inference(nnf_transformation,[],[f7])).
% 3.11/0.99  
% 3.11/0.99  fof(f57,plain,(
% 3.11/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.11/0.99    inference(cnf_transformation,[],[f36])).
% 3.11/0.99  
% 3.11/0.99  fof(f1,axiom,(
% 3.11/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.11/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.11/0.99  
% 3.11/0.99  fof(f32,plain,(
% 3.11/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/0.99    inference(nnf_transformation,[],[f1])).
% 3.11/0.99  
% 3.11/0.99  fof(f33,plain,(
% 3.11/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.11/0.99    inference(flattening,[],[f32])).
% 3.11/0.99  
% 3.11/0.99  fof(f43,plain,(
% 3.11/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.11/0.99    inference(cnf_transformation,[],[f33])).
% 3.11/0.99  
% 3.11/0.99  fof(f48,plain,(
% 3.11/0.99    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) | k1_xboole_0 != X3) )),
% 3.11/0.99    inference(cnf_transformation,[],[f35])).
% 3.11/0.99  
% 3.11/0.99  fof(f81,plain,(
% 3.11/0.99    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) | k1_xboole_0 != X3) )),
% 3.11/0.99    inference(definition_unfolding,[],[f48,f46])).
% 3.11/0.99  
% 3.11/0.99  fof(f95,plain,(
% 3.11/0.99    ( ! [X2,X0,X1] : (r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2))) )),
% 3.11/0.99    inference(equality_resolution,[],[f81])).
% 3.11/0.99  
% 3.11/0.99  cnf(c_26,negated_conjecture,
% 3.11/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 3.11/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1547,plain,
% 3.11/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_22,plain,
% 3.11/0.99      ( v4_relat_1(X0,X1)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.11/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_16,plain,
% 3.11/0.99      ( ~ v4_relat_1(X0,X1)
% 3.11/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.11/0.99      | ~ v1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_361,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.11/0.99      | ~ v1_relat_1(X0) ),
% 3.11/0.99      inference(resolution,[status(thm)],[c_22,c_16]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_21,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | v1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_365,plain,
% 3.11/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.11/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_361,c_21]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_366,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.11/0.99      inference(renaming,[status(thm)],[c_365]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1545,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.11/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1925,plain,
% 3.11/0.99      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1547,c_1545]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_11,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 3.11/0.99      | k2_enumset1(X1,X1,X2,X3) = X0
% 3.11/0.99      | k2_enumset1(X1,X1,X1,X3) = X0
% 3.11/0.99      | k2_enumset1(X2,X2,X2,X3) = X0
% 3.11/0.99      | k2_enumset1(X1,X1,X1,X2) = X0
% 3.11/0.99      | k2_enumset1(X3,X3,X3,X3) = X0
% 3.11/0.99      | k2_enumset1(X2,X2,X2,X2) = X0
% 3.11/0.99      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.11/0.99      | k1_xboole_0 = X0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1557,plain,
% 3.11/0.99      ( k2_enumset1(X0,X0,X1,X2) = X3
% 3.11/0.99      | k2_enumset1(X0,X0,X0,X2) = X3
% 3.11/0.99      | k2_enumset1(X1,X1,X1,X2) = X3
% 3.11/0.99      | k2_enumset1(X0,X0,X0,X1) = X3
% 3.11/0.99      | k2_enumset1(X2,X2,X2,X2) = X3
% 3.11/0.99      | k2_enumset1(X1,X1,X1,X1) = X3
% 3.11/0.99      | k2_enumset1(X0,X0,X0,X0) = X3
% 3.11/0.99      | k1_xboole_0 = X3
% 3.11/0.99      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3628,plain,
% 3.11/0.99      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.11/0.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1925,c_1557]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_29,plain,
% 3.11/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_24,negated_conjecture,
% 3.11/0.99      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.11/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_20,plain,
% 3.11/0.99      ( ~ v1_funct_1(X0)
% 3.11/0.99      | ~ v1_relat_1(X0)
% 3.11/0.99      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.11/0.99      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_27,negated_conjecture,
% 3.11/0.99      ( v1_funct_1(sK3) ),
% 3.11/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_342,plain,
% 3.11/0.99      ( ~ v1_relat_1(X0)
% 3.11/0.99      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.11/0.99      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.11/0.99      | sK3 != X0 ),
% 3.11/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_343,plain,
% 3.11/0.99      ( ~ v1_relat_1(sK3)
% 3.11/0.99      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.11/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.11/0.99      inference(unflattening,[status(thm)],[c_342]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_344,plain,
% 3.11/0.99      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.11/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.11/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_346,plain,
% 3.11/0.99      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.11/0.99      | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
% 3.11/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_344]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1727,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.11/0.99      | v1_relat_1(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1728,plain,
% 3.11/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 3.11/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_1727]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1733,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.11/0.99      | r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_366]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1834,plain,
% 3.11/0.99      ( ~ r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0))
% 3.11/0.99      | k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.11/0.99      | k1_xboole_0 = k1_relat_1(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_23,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.11/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.11/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1772,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.11/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_23]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1887,plain,
% 3.11/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.11/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1772]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1013,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.11/0.99      theory(equality) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1749,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,X1)
% 3.11/0.99      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.11/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 3.11/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1013]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1886,plain,
% 3.11/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.11/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 3.11/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.11/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1749]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2013,plain,
% 3.11/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.11/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 3.11/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.11/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1886]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_17,plain,
% 3.11/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.11/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1819,plain,
% 3.11/0.99      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
% 3.11/0.99      | ~ v1_relat_1(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2014,plain,
% 3.11/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 3.11/0.99      | ~ v1_relat_1(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1819]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1012,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1910,plain,
% 3.11/0.99      ( k1_relat_1(sK3) != X0
% 3.11/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.11/0.99      | k1_xboole_0 != X0 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1012]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2324,plain,
% 3.11/0.99      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 3.11/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.11/0.99      | k1_xboole_0 != k1_relat_1(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1910]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1011,plain,( X0 = X0 ),theory(equality) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3471,plain,
% 3.11/0.99      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_1011]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3895,plain,
% 3.11/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_3628,c_26,c_29,c_24,c_346,c_1727,c_1728,c_1733,c_1834,
% 3.11/0.99                 c_1887,c_2013,c_2014,c_2324,c_3471]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_19,plain,
% 3.11/0.99      ( ~ v1_relat_1(X0)
% 3.11/0.99      | k2_relat_1(X0) = k1_xboole_0
% 3.11/0.99      | k1_relat_1(X0) != k1_xboole_0 ),
% 3.11/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1551,plain,
% 3.11/0.99      ( k2_relat_1(X0) = k1_xboole_0
% 3.11/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.11/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_3910,plain,
% 3.11/0.99      ( k2_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_3895,c_1551]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1820,plain,
% 3.11/0.99      ( ~ v1_relat_1(sK3)
% 3.11/0.99      | k2_relat_1(sK3) = k1_xboole_0
% 3.11/0.99      | k1_relat_1(sK3) != k1_xboole_0 ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4088,plain,
% 3.11/0.99      ( k2_relat_1(sK3) = k1_xboole_0 ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_3910,c_26,c_29,c_24,c_346,c_1727,c_1728,c_1733,c_1820,
% 3.11/0.99                 c_1834,c_1887,c_2013,c_2014,c_2324,c_3471]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1553,plain,
% 3.11/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 3.11/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4094,plain,
% 3.11/0.99      ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top
% 3.11/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_4088,c_1553]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4184,plain,
% 3.11/0.99      ( r1_tarski(k9_relat_1(sK3,X0),k1_xboole_0) = iProver_top ),
% 3.11/0.99      inference(global_propositional_subsumption,
% 3.11/0.99                [status(thm)],
% 3.11/0.99                [c_4094,c_29,c_1728]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_12,plain,
% 3.11/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1556,plain,
% 3.11/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_14,plain,
% 3.11/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.11/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1554,plain,
% 3.11/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.11/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1842,plain,
% 3.11/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1556,c_1554]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_0,plain,
% 3.11/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.11/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1567,plain,
% 3.11/0.99      ( X0 = X1
% 3.11/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.11/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2622,plain,
% 3.11/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1842,c_1567]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4192,plain,
% 3.11/0.99      ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_4184,c_2622]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1549,plain,
% 3.11/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.11/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2701,plain,
% 3.11/0.99      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.11/0.99      inference(superposition,[status(thm)],[c_1547,c_1549]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_1548,plain,
% 3.11/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2816,plain,
% 3.11/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_2701,c_1548]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_4202,plain,
% 3.11/0.99      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.11/0.99      inference(demodulation,[status(thm)],[c_4192,c_2816]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_10,plain,
% 3.11/0.99      ( r1_tarski(k1_xboole_0,k2_enumset1(X0,X0,X1,X2)) ),
% 3.11/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2482,plain,
% 3.11/0.99      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.11/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(c_2485,plain,
% 3.11/0.99      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
% 3.11/0.99      inference(predicate_to_equality,[status(thm)],[c_2482]) ).
% 3.11/0.99  
% 3.11/0.99  cnf(contradiction,plain,
% 3.11/0.99      ( $false ),
% 3.11/0.99      inference(minisat,[status(thm)],[c_4202,c_2485]) ).
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.11/0.99  
% 3.11/0.99  ------                               Statistics
% 3.11/0.99  
% 3.11/0.99  ------ General
% 3.11/0.99  
% 3.11/0.99  abstr_ref_over_cycles:                  0
% 3.11/0.99  abstr_ref_under_cycles:                 0
% 3.11/0.99  gc_basic_clause_elim:                   0
% 3.11/0.99  forced_gc_time:                         0
% 3.11/0.99  parsing_time:                           0.011
% 3.11/0.99  unif_index_cands_time:                  0.
% 3.11/0.99  unif_index_add_time:                    0.
% 3.11/0.99  orderings_time:                         0.
% 3.11/0.99  out_proof_time:                         0.011
% 3.11/0.99  total_time:                             0.145
% 3.11/0.99  num_of_symbols:                         49
% 3.11/0.99  num_of_terms:                           3438
% 3.11/0.99  
% 3.11/0.99  ------ Preprocessing
% 3.11/0.99  
% 3.11/0.99  num_of_splits:                          0
% 3.11/0.99  num_of_split_atoms:                     0
% 3.11/0.99  num_of_reused_defs:                     0
% 3.11/0.99  num_eq_ax_congr_red:                    11
% 3.11/0.99  num_of_sem_filtered_clauses:            1
% 3.11/0.99  num_of_subtypes:                        0
% 3.11/0.99  monotx_restored_types:                  0
% 3.11/0.99  sat_num_of_epr_types:                   0
% 3.11/0.99  sat_num_of_non_cyclic_types:            0
% 3.11/0.99  sat_guarded_non_collapsed_types:        0
% 3.11/0.99  num_pure_diseq_elim:                    0
% 3.11/0.99  simp_replaced_by:                       0
% 3.11/0.99  res_preprocessed:                       124
% 3.11/0.99  prep_upred:                             0
% 3.11/0.99  prep_unflattend:                        25
% 3.11/0.99  smt_new_axioms:                         0
% 3.11/0.99  pred_elim_cands:                        3
% 3.11/0.99  pred_elim:                              2
% 3.11/0.99  pred_elim_cl:                           3
% 3.11/0.99  pred_elim_cycles:                       6
% 3.11/0.99  merged_defs:                            8
% 3.11/0.99  merged_defs_ncl:                        0
% 3.11/0.99  bin_hyper_res:                          8
% 3.11/0.99  prep_cycles:                            4
% 3.11/0.99  pred_elim_time:                         0.008
% 3.11/0.99  splitting_time:                         0.
% 3.11/0.99  sem_filter_time:                        0.
% 3.11/0.99  monotx_time:                            0.
% 3.11/0.99  subtype_inf_time:                       0.
% 3.11/0.99  
% 3.11/0.99  ------ Problem properties
% 3.11/0.99  
% 3.11/0.99  clauses:                                24
% 3.11/0.99  conjectures:                            3
% 3.11/0.99  epr:                                    3
% 3.11/0.99  horn:                                   23
% 3.11/0.99  ground:                                 3
% 3.11/0.99  unary:                                  13
% 3.11/0.99  binary:                                 6
% 3.11/0.99  lits:                                   46
% 3.11/0.99  lits_eq:                                17
% 3.11/0.99  fd_pure:                                0
% 3.11/0.99  fd_pseudo:                              0
% 3.11/0.99  fd_cond:                                0
% 3.11/0.99  fd_pseudo_cond:                         2
% 3.11/0.99  ac_symbols:                             0
% 3.11/0.99  
% 3.11/0.99  ------ Propositional Solver
% 3.11/0.99  
% 3.11/0.99  prop_solver_calls:                      27
% 3.11/0.99  prop_fast_solver_calls:                 700
% 3.11/0.99  smt_solver_calls:                       0
% 3.11/0.99  smt_fast_solver_calls:                  0
% 3.11/0.99  prop_num_of_clauses:                    1412
% 3.11/0.99  prop_preprocess_simplified:             5670
% 3.11/0.99  prop_fo_subsumed:                       6
% 3.11/0.99  prop_solver_time:                       0.
% 3.11/0.99  smt_solver_time:                        0.
% 3.11/0.99  smt_fast_solver_time:                   0.
% 3.11/0.99  prop_fast_solver_time:                  0.
% 3.11/0.99  prop_unsat_core_time:                   0.
% 3.11/0.99  
% 3.11/0.99  ------ QBF
% 3.11/0.99  
% 3.11/0.99  qbf_q_res:                              0
% 3.11/0.99  qbf_num_tautologies:                    0
% 3.11/0.99  qbf_prep_cycles:                        0
% 3.11/0.99  
% 3.11/0.99  ------ BMC1
% 3.11/0.99  
% 3.11/0.99  bmc1_current_bound:                     -1
% 3.11/0.99  bmc1_last_solved_bound:                 -1
% 3.11/0.99  bmc1_unsat_core_size:                   -1
% 3.11/0.99  bmc1_unsat_core_parents_size:           -1
% 3.11/0.99  bmc1_merge_next_fun:                    0
% 3.11/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.11/0.99  
% 3.11/0.99  ------ Instantiation
% 3.11/0.99  
% 3.11/0.99  inst_num_of_clauses:                    425
% 3.11/0.99  inst_num_in_passive:                    95
% 3.11/0.99  inst_num_in_active:                     223
% 3.11/0.99  inst_num_in_unprocessed:                108
% 3.11/0.99  inst_num_of_loops:                      230
% 3.11/0.99  inst_num_of_learning_restarts:          0
% 3.11/0.99  inst_num_moves_active_passive:          5
% 3.11/0.99  inst_lit_activity:                      0
% 3.11/0.99  inst_lit_activity_moves:                0
% 3.11/0.99  inst_num_tautologies:                   0
% 3.11/0.99  inst_num_prop_implied:                  0
% 3.11/0.99  inst_num_existing_simplified:           0
% 3.11/0.99  inst_num_eq_res_simplified:             0
% 3.11/0.99  inst_num_child_elim:                    0
% 3.11/0.99  inst_num_of_dismatching_blockings:      111
% 3.11/0.99  inst_num_of_non_proper_insts:           494
% 3.11/0.99  inst_num_of_duplicates:                 0
% 3.11/0.99  inst_inst_num_from_inst_to_res:         0
% 3.11/0.99  inst_dismatching_checking_time:         0.
% 3.11/0.99  
% 3.11/0.99  ------ Resolution
% 3.11/0.99  
% 3.11/0.99  res_num_of_clauses:                     0
% 3.11/0.99  res_num_in_passive:                     0
% 3.11/0.99  res_num_in_active:                      0
% 3.11/0.99  res_num_of_loops:                       128
% 3.11/0.99  res_forward_subset_subsumed:            70
% 3.11/0.99  res_backward_subset_subsumed:           2
% 3.11/0.99  res_forward_subsumed:                   0
% 3.11/0.99  res_backward_subsumed:                  0
% 3.11/0.99  res_forward_subsumption_resolution:     0
% 3.11/0.99  res_backward_subsumption_resolution:    0
% 3.11/0.99  res_clause_to_clause_subsumption:       267
% 3.11/0.99  res_orphan_elimination:                 0
% 3.11/0.99  res_tautology_del:                      42
% 3.11/0.99  res_num_eq_res_simplified:              0
% 3.11/0.99  res_num_sel_changes:                    0
% 3.11/0.99  res_moves_from_active_to_pass:          0
% 3.11/0.99  
% 3.11/0.99  ------ Superposition
% 3.11/0.99  
% 3.11/0.99  sup_time_total:                         0.
% 3.11/0.99  sup_time_generating:                    0.
% 3.11/0.99  sup_time_sim_full:                      0.
% 3.11/0.99  sup_time_sim_immed:                     0.
% 3.11/0.99  
% 3.11/0.99  sup_num_of_clauses:                     59
% 3.11/0.99  sup_num_in_active:                      37
% 3.11/0.99  sup_num_in_passive:                     22
% 3.11/0.99  sup_num_of_loops:                       45
% 3.11/0.99  sup_fw_superposition:                   50
% 3.11/0.99  sup_bw_superposition:                   11
% 3.11/0.99  sup_immediate_simplified:               5
% 3.11/0.99  sup_given_eliminated:                   1
% 3.11/0.99  comparisons_done:                       0
% 3.11/0.99  comparisons_avoided:                    0
% 3.11/0.99  
% 3.11/0.99  ------ Simplifications
% 3.11/0.99  
% 3.11/0.99  
% 3.11/0.99  sim_fw_subset_subsumed:                 3
% 3.11/0.99  sim_bw_subset_subsumed:                 0
% 3.11/0.99  sim_fw_subsumed:                        3
% 3.11/0.99  sim_bw_subsumed:                        0
% 3.11/0.99  sim_fw_subsumption_res:                 0
% 3.11/0.99  sim_bw_subsumption_res:                 0
% 3.11/0.99  sim_tautology_del:                      1
% 3.11/0.99  sim_eq_tautology_del:                   12
% 3.11/0.99  sim_eq_res_simp:                        0
% 3.11/0.99  sim_fw_demodulated:                     0
% 3.11/0.99  sim_bw_demodulated:                     8
% 3.11/0.99  sim_light_normalised:                   0
% 3.11/0.99  sim_joinable_taut:                      0
% 3.11/0.99  sim_joinable_simp:                      0
% 3.11/0.99  sim_ac_normalised:                      0
% 3.11/0.99  sim_smt_subsumption:                    0
% 3.11/0.99  
%------------------------------------------------------------------------------
