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
% DateTime   : Thu Dec  3 12:05:09 EST 2020

% Result     : Theorem 7.41s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 473 expanded)
%              Number of clauses        :   76 ( 113 expanded)
%              Number of leaves         :   24 ( 116 expanded)
%              Depth                    :   21
%              Number of atoms          :  536 (1260 expanded)
%              Number of equality atoms :  310 ( 652 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f91,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X2,k1_tarski(X0),X1)
          & v1_funct_1(X2) )
       => ( k1_xboole_0 != X1
         => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
      & k1_xboole_0 != X1
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_2(X2,k1_tarski(X0),X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f63,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2)
        & k1_xboole_0 != X1
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X2,k1_tarski(X0),X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
      & k1_xboole_0 != sK3
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
      & v1_funct_2(sK4,k1_tarski(sK2),sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)
    & k1_xboole_0 != sK3
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))
    & v1_funct_2(sK4,k1_tarski(sK2),sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f63])).

fof(f113,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) ),
    inference(cnf_transformation,[],[f64])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f116,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f77,f78])).

fof(f117,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f76,f116])).

fof(f136,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(definition_unfolding,[],[f113,f117])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f59,plain,(
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
    inference(flattening,[],[f58])).

fof(f82,plain,(
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
    inference(cnf_transformation,[],[f59])).

fof(f132,plain,(
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
    inference(definition_unfolding,[],[f82,f78,f116,f116,f116,f117,f117,f117,f78])).

fof(f111,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f115,plain,(
    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f64])).

fof(f135,plain,(
    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(definition_unfolding,[],[f115,f117,f117])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f99,f117,f117])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f56])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f146,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f49])).

fof(f68,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f51])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f52])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK0(X0,X1,X2) != X1
            & sK0(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( sK0(X0,X1,X2) = X1
          | sK0(X0,X1,X2) = X0
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK0(X0,X1,X2) != X1
              & sK0(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK0(X0,X1,X2),X2) )
          & ( sK0(X0,X1,X2) = X1
            | sK0(X0,X1,X2) = X0
            | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f121,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f72,f116])).

fof(f140,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_enumset1(X0,X0,X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f121])).

fof(f141,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_enumset1(X0,X0,X0,X4)) ),
    inference(equality_resolution,[],[f140])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r2_hidden(X2,X0)
       => ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f45])).

fof(f110,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3))
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f112,plain,(
    v1_funct_2(sK4,k1_tarski(sK2),sK3) ),
    inference(cnf_transformation,[],[f64])).

fof(f137,plain,(
    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(definition_unfolding,[],[f112,f117])).

fof(f114,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f64])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f14,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f97,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

cnf(c_23,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1969,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1967,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3655,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1969,c_1967])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1955,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_36,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1960,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_6552,plain,
    ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1955,c_1960])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1961,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6601,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6552,c_1961])).

cnf(c_50,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_7559,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6601,c_50])).

cnf(c_7563,plain,
    ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_7559,c_1967])).

cnf(c_34,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_27,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_530,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_34,c_27])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_34,c_33,c_27])).

cnf(c_1953,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_2637,plain,
    ( k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4 ),
    inference(superposition,[status(thm)],[c_1955,c_1953])).

cnf(c_30,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1965,plain,
    ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6260,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2637,c_1965])).

cnf(c_2981,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_5065,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2981])).

cnf(c_5066,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5065])).

cnf(c_7013,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6260,c_50,c_5066])).

cnf(c_22,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_1970,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_7073,plain,
    ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7013,c_1970])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_43,negated_conjecture,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1142,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2046,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != X0
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1142])).

cnf(c_2137,plain,
    ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4)
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_2245,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_31,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2671,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(sK4)
    | k2_enumset1(sK2,sK2,sK2,sK2) != k1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_10525,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7073,c_47,c_45,c_43,c_2137,c_2245,c_2671,c_5065])).

cnf(c_12,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f146])).

cnf(c_37,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1959,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4254,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1959,c_1967])).

cnf(c_12567,plain,
    ( r1_tarski(X0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12,c_4254])).

cnf(c_12744,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_10525,c_12567])).

cnf(c_94,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_96,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_94])).

cnf(c_100,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_102,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_100])).

cnf(c_14165,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12744,c_50,c_96,c_102,c_5066])).

cnf(c_14171,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_7563,c_14165])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1987,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_14174,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_14171,c_1987])).

cnf(c_16366,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3655,c_14174])).

cnf(c_8,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_1981,plain,
    ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_42,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_550,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
    | ~ v1_funct_1(X0)
    | k2_enumset1(sK2,sK2,sK2,sK2) != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_46])).

cnf(c_551,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
    | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
    | ~ v1_funct_1(sK4)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_550])).

cnf(c_44,negated_conjecture,
    ( k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_555,plain,
    ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_551,c_47,c_45,c_44])).

cnf(c_1952,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_555])).

cnf(c_32,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1963,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3515,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4),k1_funct_1(sK4,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1952,c_1963])).

cnf(c_6579,plain,
    ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
    | r1_tarski(k2_relat_1(sK4),k1_funct_1(sK4,X0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6552,c_3515])).

cnf(c_7457,plain,
    ( r1_tarski(k2_relat_1(sK4),k1_funct_1(sK4,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1981,c_6579])).

cnf(c_21782,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_16366,c_7457])).

cnf(c_28,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_21811,plain,
    ( r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_21782,c_28])).

cnf(c_22404,plain,
    ( $false ),
    inference(superposition,[status(thm)],[c_3655,c_21811])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n019.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:49:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.41/1.41  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.41/1.41  
% 7.41/1.41  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.41/1.41  
% 7.41/1.41  ------  iProver source info
% 7.41/1.41  
% 7.41/1.41  git: date: 2020-06-30 10:37:57 +0100
% 7.41/1.41  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.41/1.41  git: non_committed_changes: false
% 7.41/1.41  git: last_make_outside_of_git: false
% 7.41/1.41  
% 7.41/1.41  ------ 
% 7.41/1.41  
% 7.41/1.41  ------ Input Options
% 7.41/1.41  
% 7.41/1.41  --out_options                           all
% 7.41/1.41  --tptp_safe_out                         true
% 7.41/1.41  --problem_path                          ""
% 7.41/1.41  --include_path                          ""
% 7.41/1.41  --clausifier                            res/vclausify_rel
% 7.41/1.41  --clausifier_options                    ""
% 7.41/1.41  --stdin                                 false
% 7.41/1.41  --stats_out                             all
% 7.41/1.41  
% 7.41/1.41  ------ General Options
% 7.41/1.41  
% 7.41/1.41  --fof                                   false
% 7.41/1.41  --time_out_real                         305.
% 7.41/1.41  --time_out_virtual                      -1.
% 7.41/1.41  --symbol_type_check                     false
% 7.41/1.41  --clausify_out                          false
% 7.41/1.41  --sig_cnt_out                           false
% 7.41/1.41  --trig_cnt_out                          false
% 7.41/1.41  --trig_cnt_out_tolerance                1.
% 7.41/1.41  --trig_cnt_out_sk_spl                   false
% 7.41/1.41  --abstr_cl_out                          false
% 7.41/1.41  
% 7.41/1.41  ------ Global Options
% 7.41/1.41  
% 7.41/1.41  --schedule                              default
% 7.41/1.41  --add_important_lit                     false
% 7.41/1.41  --prop_solver_per_cl                    1000
% 7.41/1.41  --min_unsat_core                        false
% 7.41/1.41  --soft_assumptions                      false
% 7.41/1.41  --soft_lemma_size                       3
% 7.41/1.41  --prop_impl_unit_size                   0
% 7.41/1.41  --prop_impl_unit                        []
% 7.41/1.41  --share_sel_clauses                     true
% 7.41/1.41  --reset_solvers                         false
% 7.41/1.41  --bc_imp_inh                            [conj_cone]
% 7.41/1.41  --conj_cone_tolerance                   3.
% 7.41/1.41  --extra_neg_conj                        none
% 7.41/1.41  --large_theory_mode                     true
% 7.41/1.41  --prolific_symb_bound                   200
% 7.41/1.41  --lt_threshold                          2000
% 7.41/1.41  --clause_weak_htbl                      true
% 7.41/1.41  --gc_record_bc_elim                     false
% 7.41/1.41  
% 7.41/1.41  ------ Preprocessing Options
% 7.41/1.41  
% 7.41/1.41  --preprocessing_flag                    true
% 7.41/1.41  --time_out_prep_mult                    0.1
% 7.41/1.41  --splitting_mode                        input
% 7.41/1.41  --splitting_grd                         true
% 7.41/1.41  --splitting_cvd                         false
% 7.41/1.41  --splitting_cvd_svl                     false
% 7.41/1.41  --splitting_nvd                         32
% 7.41/1.41  --sub_typing                            true
% 7.41/1.41  --prep_gs_sim                           true
% 7.41/1.41  --prep_unflatten                        true
% 7.41/1.41  --prep_res_sim                          true
% 7.41/1.41  --prep_upred                            true
% 7.41/1.41  --prep_sem_filter                       exhaustive
% 7.41/1.41  --prep_sem_filter_out                   false
% 7.41/1.41  --pred_elim                             true
% 7.41/1.41  --res_sim_input                         true
% 7.41/1.41  --eq_ax_congr_red                       true
% 7.41/1.41  --pure_diseq_elim                       true
% 7.41/1.41  --brand_transform                       false
% 7.41/1.41  --non_eq_to_eq                          false
% 7.41/1.41  --prep_def_merge                        true
% 7.41/1.41  --prep_def_merge_prop_impl              false
% 7.41/1.41  --prep_def_merge_mbd                    true
% 7.41/1.41  --prep_def_merge_tr_red                 false
% 7.41/1.41  --prep_def_merge_tr_cl                  false
% 7.41/1.41  --smt_preprocessing                     true
% 7.41/1.41  --smt_ac_axioms                         fast
% 7.41/1.41  --preprocessed_out                      false
% 7.41/1.41  --preprocessed_stats                    false
% 7.41/1.41  
% 7.41/1.41  ------ Abstraction refinement Options
% 7.41/1.41  
% 7.41/1.41  --abstr_ref                             []
% 7.41/1.41  --abstr_ref_prep                        false
% 7.41/1.41  --abstr_ref_until_sat                   false
% 7.41/1.41  --abstr_ref_sig_restrict                funpre
% 7.41/1.41  --abstr_ref_af_restrict_to_split_sk     false
% 7.41/1.41  --abstr_ref_under                       []
% 7.41/1.41  
% 7.41/1.41  ------ SAT Options
% 7.41/1.41  
% 7.41/1.41  --sat_mode                              false
% 7.41/1.41  --sat_fm_restart_options                ""
% 7.41/1.41  --sat_gr_def                            false
% 7.41/1.41  --sat_epr_types                         true
% 7.41/1.41  --sat_non_cyclic_types                  false
% 7.41/1.41  --sat_finite_models                     false
% 7.41/1.41  --sat_fm_lemmas                         false
% 7.41/1.41  --sat_fm_prep                           false
% 7.41/1.41  --sat_fm_uc_incr                        true
% 7.41/1.41  --sat_out_model                         small
% 7.41/1.41  --sat_out_clauses                       false
% 7.41/1.41  
% 7.41/1.41  ------ QBF Options
% 7.41/1.41  
% 7.41/1.41  --qbf_mode                              false
% 7.41/1.41  --qbf_elim_univ                         false
% 7.41/1.41  --qbf_dom_inst                          none
% 7.41/1.41  --qbf_dom_pre_inst                      false
% 7.41/1.41  --qbf_sk_in                             false
% 7.41/1.41  --qbf_pred_elim                         true
% 7.41/1.41  --qbf_split                             512
% 7.41/1.41  
% 7.41/1.41  ------ BMC1 Options
% 7.41/1.41  
% 7.41/1.41  --bmc1_incremental                      false
% 7.41/1.41  --bmc1_axioms                           reachable_all
% 7.41/1.41  --bmc1_min_bound                        0
% 7.41/1.41  --bmc1_max_bound                        -1
% 7.41/1.41  --bmc1_max_bound_default                -1
% 7.41/1.41  --bmc1_symbol_reachability              true
% 7.41/1.41  --bmc1_property_lemmas                  false
% 7.41/1.41  --bmc1_k_induction                      false
% 7.41/1.41  --bmc1_non_equiv_states                 false
% 7.41/1.41  --bmc1_deadlock                         false
% 7.41/1.41  --bmc1_ucm                              false
% 7.41/1.41  --bmc1_add_unsat_core                   none
% 7.41/1.41  --bmc1_unsat_core_children              false
% 7.41/1.41  --bmc1_unsat_core_extrapolate_axioms    false
% 7.41/1.41  --bmc1_out_stat                         full
% 7.41/1.41  --bmc1_ground_init                      false
% 7.41/1.41  --bmc1_pre_inst_next_state              false
% 7.41/1.41  --bmc1_pre_inst_state                   false
% 7.41/1.41  --bmc1_pre_inst_reach_state             false
% 7.41/1.41  --bmc1_out_unsat_core                   false
% 7.41/1.41  --bmc1_aig_witness_out                  false
% 7.41/1.41  --bmc1_verbose                          false
% 7.41/1.41  --bmc1_dump_clauses_tptp                false
% 7.41/1.41  --bmc1_dump_unsat_core_tptp             false
% 7.41/1.41  --bmc1_dump_file                        -
% 7.41/1.41  --bmc1_ucm_expand_uc_limit              128
% 7.41/1.41  --bmc1_ucm_n_expand_iterations          6
% 7.41/1.41  --bmc1_ucm_extend_mode                  1
% 7.41/1.41  --bmc1_ucm_init_mode                    2
% 7.41/1.41  --bmc1_ucm_cone_mode                    none
% 7.41/1.41  --bmc1_ucm_reduced_relation_type        0
% 7.41/1.41  --bmc1_ucm_relax_model                  4
% 7.41/1.41  --bmc1_ucm_full_tr_after_sat            true
% 7.41/1.41  --bmc1_ucm_expand_neg_assumptions       false
% 7.41/1.41  --bmc1_ucm_layered_model                none
% 7.41/1.41  --bmc1_ucm_max_lemma_size               10
% 7.41/1.41  
% 7.41/1.41  ------ AIG Options
% 7.41/1.41  
% 7.41/1.41  --aig_mode                              false
% 7.41/1.41  
% 7.41/1.41  ------ Instantiation Options
% 7.41/1.41  
% 7.41/1.41  --instantiation_flag                    true
% 7.41/1.41  --inst_sos_flag                         true
% 7.41/1.41  --inst_sos_phase                        true
% 7.41/1.41  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.41/1.41  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.41/1.41  --inst_lit_sel_side                     num_symb
% 7.41/1.41  --inst_solver_per_active                1400
% 7.41/1.41  --inst_solver_calls_frac                1.
% 7.41/1.41  --inst_passive_queue_type               priority_queues
% 7.41/1.41  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.41/1.41  --inst_passive_queues_freq              [25;2]
% 7.41/1.41  --inst_dismatching                      true
% 7.41/1.41  --inst_eager_unprocessed_to_passive     true
% 7.41/1.41  --inst_prop_sim_given                   true
% 7.41/1.41  --inst_prop_sim_new                     false
% 7.41/1.41  --inst_subs_new                         false
% 7.41/1.41  --inst_eq_res_simp                      false
% 7.41/1.41  --inst_subs_given                       false
% 7.41/1.41  --inst_orphan_elimination               true
% 7.41/1.41  --inst_learning_loop_flag               true
% 7.41/1.41  --inst_learning_start                   3000
% 7.41/1.41  --inst_learning_factor                  2
% 7.41/1.41  --inst_start_prop_sim_after_learn       3
% 7.41/1.41  --inst_sel_renew                        solver
% 7.41/1.41  --inst_lit_activity_flag                true
% 7.41/1.41  --inst_restr_to_given                   false
% 7.41/1.41  --inst_activity_threshold               500
% 7.41/1.41  --inst_out_proof                        true
% 7.41/1.41  
% 7.41/1.41  ------ Resolution Options
% 7.41/1.41  
% 7.41/1.41  --resolution_flag                       true
% 7.41/1.41  --res_lit_sel                           adaptive
% 7.41/1.41  --res_lit_sel_side                      none
% 7.41/1.41  --res_ordering                          kbo
% 7.41/1.41  --res_to_prop_solver                    active
% 7.41/1.41  --res_prop_simpl_new                    false
% 7.41/1.41  --res_prop_simpl_given                  true
% 7.41/1.41  --res_passive_queue_type                priority_queues
% 7.41/1.41  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.41/1.41  --res_passive_queues_freq               [15;5]
% 7.41/1.41  --res_forward_subs                      full
% 7.41/1.41  --res_backward_subs                     full
% 7.41/1.41  --res_forward_subs_resolution           true
% 7.41/1.41  --res_backward_subs_resolution          true
% 7.41/1.41  --res_orphan_elimination                true
% 7.41/1.41  --res_time_limit                        2.
% 7.41/1.41  --res_out_proof                         true
% 7.41/1.41  
% 7.41/1.41  ------ Superposition Options
% 7.41/1.41  
% 7.41/1.41  --superposition_flag                    true
% 7.41/1.41  --sup_passive_queue_type                priority_queues
% 7.41/1.41  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.41/1.41  --sup_passive_queues_freq               [8;1;4]
% 7.41/1.41  --demod_completeness_check              fast
% 7.41/1.41  --demod_use_ground                      true
% 7.41/1.41  --sup_to_prop_solver                    passive
% 7.41/1.41  --sup_prop_simpl_new                    true
% 7.41/1.41  --sup_prop_simpl_given                  true
% 7.41/1.41  --sup_fun_splitting                     true
% 7.41/1.41  --sup_smt_interval                      50000
% 7.41/1.41  
% 7.41/1.41  ------ Superposition Simplification Setup
% 7.41/1.41  
% 7.41/1.41  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.41/1.41  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.41/1.41  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.41  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.41/1.41  --sup_full_triv                         [TrivRules;PropSubs]
% 7.41/1.41  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.41/1.41  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.41/1.41  --sup_immed_triv                        [TrivRules]
% 7.41/1.41  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.41  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.41  --sup_immed_bw_main                     []
% 7.41/1.41  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.41/1.41  --sup_input_triv                        [Unflattening;TrivRules]
% 7.41/1.41  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.41  --sup_input_bw                          []
% 7.41/1.41  
% 7.41/1.41  ------ Combination Options
% 7.41/1.41  
% 7.41/1.41  --comb_res_mult                         3
% 7.41/1.41  --comb_sup_mult                         2
% 7.41/1.41  --comb_inst_mult                        10
% 7.41/1.41  
% 7.41/1.41  ------ Debug Options
% 7.41/1.41  
% 7.41/1.41  --dbg_backtrace                         false
% 7.41/1.41  --dbg_dump_prop_clauses                 false
% 7.41/1.41  --dbg_dump_prop_clauses_file            -
% 7.41/1.41  --dbg_out_stat                          false
% 7.41/1.41  ------ Parsing...
% 7.41/1.41  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.41/1.41  
% 7.41/1.41  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.41/1.41  
% 7.41/1.41  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.41/1.41  
% 7.41/1.41  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.41/1.41  ------ Proving...
% 7.41/1.41  ------ Problem Properties 
% 7.41/1.41  
% 7.41/1.41  
% 7.41/1.41  clauses                                 45
% 7.41/1.41  conjectures                             4
% 7.41/1.41  EPR                                     7
% 7.41/1.41  Horn                                    41
% 7.41/1.41  unary                                   24
% 7.41/1.41  binary                                  10
% 7.41/1.41  lits                                    86
% 7.41/1.41  lits eq                                 34
% 7.41/1.41  fd_pure                                 0
% 7.41/1.41  fd_pseudo                               0
% 7.41/1.41  fd_cond                                 1
% 7.41/1.41  fd_pseudo_cond                          6
% 7.41/1.41  AC symbols                              0
% 7.41/1.41  
% 7.41/1.41  ------ Schedule dynamic 5 is on 
% 7.41/1.41  
% 7.41/1.41  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.41/1.41  
% 7.41/1.41  
% 7.41/1.41  ------ 
% 7.41/1.41  Current options:
% 7.41/1.41  ------ 
% 7.41/1.41  
% 7.41/1.41  ------ Input Options
% 7.41/1.41  
% 7.41/1.41  --out_options                           all
% 7.41/1.41  --tptp_safe_out                         true
% 7.41/1.41  --problem_path                          ""
% 7.41/1.41  --include_path                          ""
% 7.41/1.41  --clausifier                            res/vclausify_rel
% 7.41/1.41  --clausifier_options                    ""
% 7.41/1.41  --stdin                                 false
% 7.41/1.41  --stats_out                             all
% 7.41/1.41  
% 7.41/1.41  ------ General Options
% 7.41/1.41  
% 7.41/1.41  --fof                                   false
% 7.41/1.41  --time_out_real                         305.
% 7.41/1.41  --time_out_virtual                      -1.
% 7.41/1.41  --symbol_type_check                     false
% 7.41/1.41  --clausify_out                          false
% 7.41/1.41  --sig_cnt_out                           false
% 7.41/1.41  --trig_cnt_out                          false
% 7.41/1.41  --trig_cnt_out_tolerance                1.
% 7.41/1.41  --trig_cnt_out_sk_spl                   false
% 7.41/1.41  --abstr_cl_out                          false
% 7.41/1.41  
% 7.41/1.41  ------ Global Options
% 7.41/1.41  
% 7.41/1.41  --schedule                              default
% 7.41/1.41  --add_important_lit                     false
% 7.41/1.41  --prop_solver_per_cl                    1000
% 7.41/1.41  --min_unsat_core                        false
% 7.41/1.41  --soft_assumptions                      false
% 7.41/1.41  --soft_lemma_size                       3
% 7.41/1.41  --prop_impl_unit_size                   0
% 7.41/1.41  --prop_impl_unit                        []
% 7.41/1.41  --share_sel_clauses                     true
% 7.41/1.41  --reset_solvers                         false
% 7.41/1.41  --bc_imp_inh                            [conj_cone]
% 7.41/1.41  --conj_cone_tolerance                   3.
% 7.41/1.41  --extra_neg_conj                        none
% 7.41/1.41  --large_theory_mode                     true
% 7.41/1.41  --prolific_symb_bound                   200
% 7.41/1.41  --lt_threshold                          2000
% 7.41/1.41  --clause_weak_htbl                      true
% 7.41/1.41  --gc_record_bc_elim                     false
% 7.41/1.41  
% 7.41/1.41  ------ Preprocessing Options
% 7.41/1.41  
% 7.41/1.41  --preprocessing_flag                    true
% 7.41/1.41  --time_out_prep_mult                    0.1
% 7.41/1.41  --splitting_mode                        input
% 7.41/1.41  --splitting_grd                         true
% 7.41/1.41  --splitting_cvd                         false
% 7.41/1.41  --splitting_cvd_svl                     false
% 7.41/1.41  --splitting_nvd                         32
% 7.41/1.41  --sub_typing                            true
% 7.41/1.41  --prep_gs_sim                           true
% 7.41/1.41  --prep_unflatten                        true
% 7.41/1.41  --prep_res_sim                          true
% 7.41/1.41  --prep_upred                            true
% 7.41/1.41  --prep_sem_filter                       exhaustive
% 7.41/1.41  --prep_sem_filter_out                   false
% 7.41/1.41  --pred_elim                             true
% 7.41/1.41  --res_sim_input                         true
% 7.41/1.41  --eq_ax_congr_red                       true
% 7.41/1.41  --pure_diseq_elim                       true
% 7.41/1.41  --brand_transform                       false
% 7.41/1.41  --non_eq_to_eq                          false
% 7.41/1.41  --prep_def_merge                        true
% 7.41/1.41  --prep_def_merge_prop_impl              false
% 7.41/1.41  --prep_def_merge_mbd                    true
% 7.41/1.41  --prep_def_merge_tr_red                 false
% 7.41/1.41  --prep_def_merge_tr_cl                  false
% 7.41/1.41  --smt_preprocessing                     true
% 7.41/1.41  --smt_ac_axioms                         fast
% 7.41/1.41  --preprocessed_out                      false
% 7.41/1.41  --preprocessed_stats                    false
% 7.41/1.41  
% 7.41/1.41  ------ Abstraction refinement Options
% 7.41/1.41  
% 7.41/1.41  --abstr_ref                             []
% 7.41/1.41  --abstr_ref_prep                        false
% 7.41/1.41  --abstr_ref_until_sat                   false
% 7.41/1.41  --abstr_ref_sig_restrict                funpre
% 7.41/1.41  --abstr_ref_af_restrict_to_split_sk     false
% 7.41/1.41  --abstr_ref_under                       []
% 7.41/1.41  
% 7.41/1.41  ------ SAT Options
% 7.41/1.41  
% 7.41/1.41  --sat_mode                              false
% 7.41/1.41  --sat_fm_restart_options                ""
% 7.41/1.41  --sat_gr_def                            false
% 7.41/1.41  --sat_epr_types                         true
% 7.41/1.41  --sat_non_cyclic_types                  false
% 7.41/1.41  --sat_finite_models                     false
% 7.41/1.41  --sat_fm_lemmas                         false
% 7.41/1.41  --sat_fm_prep                           false
% 7.41/1.41  --sat_fm_uc_incr                        true
% 7.41/1.41  --sat_out_model                         small
% 7.41/1.41  --sat_out_clauses                       false
% 7.41/1.41  
% 7.41/1.41  ------ QBF Options
% 7.41/1.41  
% 7.41/1.41  --qbf_mode                              false
% 7.41/1.41  --qbf_elim_univ                         false
% 7.41/1.41  --qbf_dom_inst                          none
% 7.41/1.41  --qbf_dom_pre_inst                      false
% 7.41/1.41  --qbf_sk_in                             false
% 7.41/1.41  --qbf_pred_elim                         true
% 7.41/1.41  --qbf_split                             512
% 7.41/1.41  
% 7.41/1.41  ------ BMC1 Options
% 7.41/1.41  
% 7.41/1.41  --bmc1_incremental                      false
% 7.41/1.41  --bmc1_axioms                           reachable_all
% 7.41/1.41  --bmc1_min_bound                        0
% 7.41/1.41  --bmc1_max_bound                        -1
% 7.41/1.41  --bmc1_max_bound_default                -1
% 7.41/1.41  --bmc1_symbol_reachability              true
% 7.41/1.41  --bmc1_property_lemmas                  false
% 7.41/1.41  --bmc1_k_induction                      false
% 7.41/1.41  --bmc1_non_equiv_states                 false
% 7.41/1.41  --bmc1_deadlock                         false
% 7.41/1.41  --bmc1_ucm                              false
% 7.41/1.41  --bmc1_add_unsat_core                   none
% 7.41/1.41  --bmc1_unsat_core_children              false
% 7.41/1.41  --bmc1_unsat_core_extrapolate_axioms    false
% 7.41/1.41  --bmc1_out_stat                         full
% 7.41/1.41  --bmc1_ground_init                      false
% 7.41/1.41  --bmc1_pre_inst_next_state              false
% 7.41/1.41  --bmc1_pre_inst_state                   false
% 7.41/1.41  --bmc1_pre_inst_reach_state             false
% 7.41/1.41  --bmc1_out_unsat_core                   false
% 7.41/1.41  --bmc1_aig_witness_out                  false
% 7.41/1.41  --bmc1_verbose                          false
% 7.41/1.41  --bmc1_dump_clauses_tptp                false
% 7.41/1.41  --bmc1_dump_unsat_core_tptp             false
% 7.41/1.41  --bmc1_dump_file                        -
% 7.41/1.41  --bmc1_ucm_expand_uc_limit              128
% 7.41/1.41  --bmc1_ucm_n_expand_iterations          6
% 7.41/1.41  --bmc1_ucm_extend_mode                  1
% 7.41/1.41  --bmc1_ucm_init_mode                    2
% 7.41/1.41  --bmc1_ucm_cone_mode                    none
% 7.41/1.41  --bmc1_ucm_reduced_relation_type        0
% 7.41/1.41  --bmc1_ucm_relax_model                  4
% 7.41/1.41  --bmc1_ucm_full_tr_after_sat            true
% 7.41/1.41  --bmc1_ucm_expand_neg_assumptions       false
% 7.41/1.41  --bmc1_ucm_layered_model                none
% 7.41/1.41  --bmc1_ucm_max_lemma_size               10
% 7.41/1.41  
% 7.41/1.41  ------ AIG Options
% 7.41/1.41  
% 7.41/1.41  --aig_mode                              false
% 7.41/1.41  
% 7.41/1.41  ------ Instantiation Options
% 7.41/1.41  
% 7.41/1.41  --instantiation_flag                    true
% 7.41/1.41  --inst_sos_flag                         true
% 7.41/1.41  --inst_sos_phase                        true
% 7.41/1.41  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.41/1.41  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.41/1.41  --inst_lit_sel_side                     none
% 7.41/1.41  --inst_solver_per_active                1400
% 7.41/1.41  --inst_solver_calls_frac                1.
% 7.41/1.41  --inst_passive_queue_type               priority_queues
% 7.41/1.41  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.41/1.41  --inst_passive_queues_freq              [25;2]
% 7.41/1.41  --inst_dismatching                      true
% 7.41/1.41  --inst_eager_unprocessed_to_passive     true
% 7.41/1.41  --inst_prop_sim_given                   true
% 7.41/1.41  --inst_prop_sim_new                     false
% 7.41/1.41  --inst_subs_new                         false
% 7.41/1.41  --inst_eq_res_simp                      false
% 7.41/1.41  --inst_subs_given                       false
% 7.41/1.41  --inst_orphan_elimination               true
% 7.41/1.41  --inst_learning_loop_flag               true
% 7.41/1.41  --inst_learning_start                   3000
% 7.41/1.41  --inst_learning_factor                  2
% 7.41/1.41  --inst_start_prop_sim_after_learn       3
% 7.41/1.41  --inst_sel_renew                        solver
% 7.41/1.41  --inst_lit_activity_flag                true
% 7.41/1.41  --inst_restr_to_given                   false
% 7.41/1.41  --inst_activity_threshold               500
% 7.41/1.41  --inst_out_proof                        true
% 7.41/1.41  
% 7.41/1.41  ------ Resolution Options
% 7.41/1.41  
% 7.41/1.41  --resolution_flag                       false
% 7.41/1.41  --res_lit_sel                           adaptive
% 7.41/1.41  --res_lit_sel_side                      none
% 7.41/1.41  --res_ordering                          kbo
% 7.41/1.41  --res_to_prop_solver                    active
% 7.41/1.41  --res_prop_simpl_new                    false
% 7.41/1.41  --res_prop_simpl_given                  true
% 7.41/1.41  --res_passive_queue_type                priority_queues
% 7.41/1.41  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.41/1.41  --res_passive_queues_freq               [15;5]
% 7.41/1.41  --res_forward_subs                      full
% 7.41/1.41  --res_backward_subs                     full
% 7.41/1.41  --res_forward_subs_resolution           true
% 7.41/1.41  --res_backward_subs_resolution          true
% 7.41/1.41  --res_orphan_elimination                true
% 7.41/1.41  --res_time_limit                        2.
% 7.41/1.41  --res_out_proof                         true
% 7.41/1.41  
% 7.41/1.41  ------ Superposition Options
% 7.41/1.41  
% 7.41/1.41  --superposition_flag                    true
% 7.41/1.41  --sup_passive_queue_type                priority_queues
% 7.41/1.41  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.41/1.41  --sup_passive_queues_freq               [8;1;4]
% 7.41/1.41  --demod_completeness_check              fast
% 7.41/1.41  --demod_use_ground                      true
% 7.41/1.41  --sup_to_prop_solver                    passive
% 7.41/1.41  --sup_prop_simpl_new                    true
% 7.41/1.41  --sup_prop_simpl_given                  true
% 7.41/1.41  --sup_fun_splitting                     true
% 7.41/1.41  --sup_smt_interval                      50000
% 7.41/1.41  
% 7.41/1.41  ------ Superposition Simplification Setup
% 7.41/1.41  
% 7.41/1.41  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.41/1.41  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.41/1.41  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.41/1.41  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.41/1.41  --sup_full_triv                         [TrivRules;PropSubs]
% 7.41/1.41  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.41/1.41  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.41/1.41  --sup_immed_triv                        [TrivRules]
% 7.41/1.41  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.41  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.41  --sup_immed_bw_main                     []
% 7.41/1.41  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.41/1.41  --sup_input_triv                        [Unflattening;TrivRules]
% 7.41/1.41  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.41/1.41  --sup_input_bw                          []
% 7.41/1.41  
% 7.41/1.41  ------ Combination Options
% 7.41/1.41  
% 7.41/1.41  --comb_res_mult                         3
% 7.41/1.41  --comb_sup_mult                         2
% 7.41/1.41  --comb_inst_mult                        10
% 7.41/1.41  
% 7.41/1.41  ------ Debug Options
% 7.41/1.41  
% 7.41/1.41  --dbg_backtrace                         false
% 7.41/1.41  --dbg_dump_prop_clauses                 false
% 7.41/1.41  --dbg_dump_prop_clauses_file            -
% 7.41/1.41  --dbg_out_stat                          false
% 7.41/1.41  
% 7.41/1.41  
% 7.41/1.41  
% 7.41/1.41  
% 7.41/1.41  ------ Proving...
% 7.41/1.41  
% 7.41/1.41  
% 7.41/1.41  % SZS status Theorem for theBenchmark.p
% 7.41/1.41  
% 7.41/1.41   Resolution empty clause
% 7.41/1.41  
% 7.41/1.41  % SZS output start CNFRefutation for theBenchmark.p
% 7.41/1.41  
% 7.41/1.41  fof(f10,axiom,(
% 7.41/1.41    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f91,plain,(
% 7.41/1.41    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 7.41/1.41    inference(cnf_transformation,[],[f10])).
% 7.41/1.41  
% 7.41/1.41  fof(f11,axiom,(
% 7.41/1.41    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f60,plain,(
% 7.41/1.41    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.41/1.41    inference(nnf_transformation,[],[f11])).
% 7.41/1.41  
% 7.41/1.41  fof(f92,plain,(
% 7.41/1.41    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.41/1.41    inference(cnf_transformation,[],[f60])).
% 7.41/1.41  
% 7.41/1.41  fof(f25,conjecture,(
% 7.41/1.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f26,negated_conjecture,(
% 7.41/1.41    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => k1_tarski(k1_funct_1(X2,X0)) = k2_relset_1(k1_tarski(X0),X1,X2)))),
% 7.41/1.41    inference(negated_conjecture,[],[f25])).
% 7.41/1.41  
% 7.41/1.41  fof(f47,plain,(
% 7.41/1.41    ? [X0,X1,X2] : ((k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)))),
% 7.41/1.41    inference(ennf_transformation,[],[f26])).
% 7.41/1.41  
% 7.41/1.41  fof(f48,plain,(
% 7.41/1.41    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2))),
% 7.41/1.41    inference(flattening,[],[f47])).
% 7.41/1.41  
% 7.41/1.41  fof(f63,plain,(
% 7.41/1.41    ? [X0,X1,X2] : (k1_tarski(k1_funct_1(X2,X0)) != k2_relset_1(k1_tarski(X0),X1,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X2,k1_tarski(X0),X1) & v1_funct_1(X2)) => (k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4))),
% 7.41/1.41    introduced(choice_axiom,[])).
% 7.41/1.41  
% 7.41/1.41  fof(f64,plain,(
% 7.41/1.41    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4) & k1_xboole_0 != sK3 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3))) & v1_funct_2(sK4,k1_tarski(sK2),sK3) & v1_funct_1(sK4)),
% 7.41/1.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f48,f63])).
% 7.41/1.41  
% 7.41/1.41  fof(f113,plain,(
% 7.41/1.41    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK2),sK3)))),
% 7.41/1.41    inference(cnf_transformation,[],[f64])).
% 7.41/1.41  
% 7.41/1.41  fof(f5,axiom,(
% 7.41/1.41    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f76,plain,(
% 7.41/1.41    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.41/1.41    inference(cnf_transformation,[],[f5])).
% 7.41/1.41  
% 7.41/1.41  fof(f6,axiom,(
% 7.41/1.41    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f77,plain,(
% 7.41/1.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.41/1.41    inference(cnf_transformation,[],[f6])).
% 7.41/1.41  
% 7.41/1.41  fof(f7,axiom,(
% 7.41/1.41    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f78,plain,(
% 7.41/1.41    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.41/1.41    inference(cnf_transformation,[],[f7])).
% 7.41/1.41  
% 7.41/1.41  fof(f116,plain,(
% 7.41/1.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.41/1.41    inference(definition_unfolding,[],[f77,f78])).
% 7.41/1.41  
% 7.41/1.41  fof(f117,plain,(
% 7.41/1.41    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.41/1.41    inference(definition_unfolding,[],[f76,f116])).
% 7.41/1.41  
% 7.41/1.41  fof(f136,plain,(
% 7.41/1.41    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))),
% 7.41/1.41    inference(definition_unfolding,[],[f113,f117])).
% 7.41/1.41  
% 7.41/1.41  fof(f21,axiom,(
% 7.41/1.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f41,plain,(
% 7.41/1.41    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.41/1.41    inference(ennf_transformation,[],[f21])).
% 7.41/1.41  
% 7.41/1.41  fof(f104,plain,(
% 7.41/1.41    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.41/1.41    inference(cnf_transformation,[],[f41])).
% 7.41/1.41  
% 7.41/1.41  fof(f20,axiom,(
% 7.41/1.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f40,plain,(
% 7.41/1.41    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.41/1.41    inference(ennf_transformation,[],[f20])).
% 7.41/1.41  
% 7.41/1.41  fof(f103,plain,(
% 7.41/1.41    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.41/1.41    inference(cnf_transformation,[],[f40])).
% 7.41/1.41  
% 7.41/1.41  fof(f19,axiom,(
% 7.41/1.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f27,plain,(
% 7.41/1.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.41/1.41    inference(pure_predicate_removal,[],[f19])).
% 7.41/1.41  
% 7.41/1.41  fof(f39,plain,(
% 7.41/1.41    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.41/1.41    inference(ennf_transformation,[],[f27])).
% 7.41/1.41  
% 7.41/1.41  fof(f102,plain,(
% 7.41/1.41    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.41/1.41    inference(cnf_transformation,[],[f39])).
% 7.41/1.41  
% 7.41/1.41  fof(f13,axiom,(
% 7.41/1.41    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f32,plain,(
% 7.41/1.41    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 7.41/1.41    inference(ennf_transformation,[],[f13])).
% 7.41/1.41  
% 7.41/1.41  fof(f33,plain,(
% 7.41/1.41    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.41/1.41    inference(flattening,[],[f32])).
% 7.41/1.41  
% 7.41/1.41  fof(f95,plain,(
% 7.41/1.41    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.41/1.41    inference(cnf_transformation,[],[f33])).
% 7.41/1.41  
% 7.41/1.41  fof(f18,axiom,(
% 7.41/1.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f38,plain,(
% 7.41/1.41    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.41/1.41    inference(ennf_transformation,[],[f18])).
% 7.41/1.41  
% 7.41/1.41  fof(f101,plain,(
% 7.41/1.41    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.41/1.41    inference(cnf_transformation,[],[f38])).
% 7.41/1.41  
% 7.41/1.41  fof(f15,axiom,(
% 7.41/1.41    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f34,plain,(
% 7.41/1.41    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 7.41/1.41    inference(ennf_transformation,[],[f15])).
% 7.41/1.41  
% 7.41/1.41  fof(f98,plain,(
% 7.41/1.41    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 7.41/1.41    inference(cnf_transformation,[],[f34])).
% 7.41/1.41  
% 7.41/1.41  fof(f9,axiom,(
% 7.41/1.41    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f29,plain,(
% 7.41/1.41    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 7.41/1.41    inference(ennf_transformation,[],[f9])).
% 7.41/1.41  
% 7.41/1.41  fof(f58,plain,(
% 7.41/1.41    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 7.41/1.41    inference(nnf_transformation,[],[f29])).
% 7.41/1.41  
% 7.41/1.41  fof(f59,plain,(
% 7.41/1.41    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 7.41/1.41    inference(flattening,[],[f58])).
% 7.41/1.41  
% 7.41/1.41  fof(f82,plain,(
% 7.41/1.41    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 7.41/1.41    inference(cnf_transformation,[],[f59])).
% 7.41/1.41  
% 7.41/1.41  fof(f132,plain,(
% 7.41/1.41    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 7.41/1.41    inference(definition_unfolding,[],[f82,f78,f116,f116,f116,f117,f117,f117,f78])).
% 7.41/1.41  
% 7.41/1.41  fof(f111,plain,(
% 7.41/1.41    v1_funct_1(sK4)),
% 7.41/1.41    inference(cnf_transformation,[],[f64])).
% 7.41/1.41  
% 7.41/1.41  fof(f115,plain,(
% 7.41/1.41    k1_tarski(k1_funct_1(sK4,sK2)) != k2_relset_1(k1_tarski(sK2),sK3,sK4)),
% 7.41/1.41    inference(cnf_transformation,[],[f64])).
% 7.41/1.41  
% 7.41/1.41  fof(f135,plain,(
% 7.41/1.41    k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)),
% 7.41/1.41    inference(definition_unfolding,[],[f115,f117,f117])).
% 7.41/1.41  
% 7.41/1.41  fof(f16,axiom,(
% 7.41/1.41    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f35,plain,(
% 7.41/1.41    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.41/1.41    inference(ennf_transformation,[],[f16])).
% 7.41/1.41  
% 7.41/1.41  fof(f36,plain,(
% 7.41/1.41    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.41/1.41    inference(flattening,[],[f35])).
% 7.41/1.41  
% 7.41/1.41  fof(f99,plain,(
% 7.41/1.41    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.41/1.41    inference(cnf_transformation,[],[f36])).
% 7.41/1.41  
% 7.41/1.41  fof(f133,plain,(
% 7.41/1.41    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.41/1.41    inference(definition_unfolding,[],[f99,f117,f117])).
% 7.41/1.41  
% 7.41/1.41  fof(f8,axiom,(
% 7.41/1.41    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f56,plain,(
% 7.41/1.41    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.41/1.41    inference(nnf_transformation,[],[f8])).
% 7.41/1.41  
% 7.41/1.41  fof(f57,plain,(
% 7.41/1.41    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.41/1.41    inference(flattening,[],[f56])).
% 7.41/1.41  
% 7.41/1.41  fof(f80,plain,(
% 7.41/1.41    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.41/1.41    inference(cnf_transformation,[],[f57])).
% 7.41/1.41  
% 7.41/1.41  fof(f146,plain,(
% 7.41/1.41    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.41/1.41    inference(equality_resolution,[],[f80])).
% 7.41/1.41  
% 7.41/1.41  fof(f22,axiom,(
% 7.41/1.41    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f42,plain,(
% 7.41/1.41    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 7.41/1.41    inference(ennf_transformation,[],[f22])).
% 7.41/1.41  
% 7.41/1.41  fof(f43,plain,(
% 7.41/1.41    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 7.41/1.41    inference(flattening,[],[f42])).
% 7.41/1.41  
% 7.41/1.41  fof(f105,plain,(
% 7.41/1.41    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 7.41/1.41    inference(cnf_transformation,[],[f43])).
% 7.41/1.41  
% 7.41/1.41  fof(f2,axiom,(
% 7.41/1.41    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f49,plain,(
% 7.41/1.41    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.41/1.41    inference(nnf_transformation,[],[f2])).
% 7.41/1.41  
% 7.41/1.41  fof(f50,plain,(
% 7.41/1.41    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.41/1.41    inference(flattening,[],[f49])).
% 7.41/1.41  
% 7.41/1.41  fof(f68,plain,(
% 7.41/1.41    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.41/1.41    inference(cnf_transformation,[],[f50])).
% 7.41/1.41  
% 7.41/1.41  fof(f4,axiom,(
% 7.41/1.41    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f51,plain,(
% 7.41/1.41    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.41/1.41    inference(nnf_transformation,[],[f4])).
% 7.41/1.41  
% 7.41/1.41  fof(f52,plain,(
% 7.41/1.41    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 7.41/1.41    inference(flattening,[],[f51])).
% 7.41/1.41  
% 7.41/1.41  fof(f53,plain,(
% 7.41/1.41    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.41/1.41    inference(rectify,[],[f52])).
% 7.41/1.41  
% 7.41/1.41  fof(f54,plain,(
% 7.41/1.41    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2))))),
% 7.41/1.41    introduced(choice_axiom,[])).
% 7.41/1.41  
% 7.41/1.41  fof(f55,plain,(
% 7.41/1.41    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK0(X0,X1,X2) != X1 & sK0(X0,X1,X2) != X0) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (sK0(X0,X1,X2) = X1 | sK0(X0,X1,X2) = X0 | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 7.41/1.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f53,f54])).
% 7.41/1.41  
% 7.41/1.41  fof(f72,plain,(
% 7.41/1.41    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 7.41/1.41    inference(cnf_transformation,[],[f55])).
% 7.41/1.41  
% 7.41/1.41  fof(f121,plain,(
% 7.41/1.41    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 7.41/1.41    inference(definition_unfolding,[],[f72,f116])).
% 7.41/1.41  
% 7.41/1.41  fof(f140,plain,(
% 7.41/1.41    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_enumset1(X0,X0,X0,X4) != X2) )),
% 7.41/1.41    inference(equality_resolution,[],[f121])).
% 7.41/1.41  
% 7.41/1.41  fof(f141,plain,(
% 7.41/1.41    ( ! [X4,X0] : (r2_hidden(X4,k2_enumset1(X0,X0,X0,X4))) )),
% 7.41/1.41    inference(equality_resolution,[],[f140])).
% 7.41/1.41  
% 7.41/1.41  fof(f24,axiom,(
% 7.41/1.41    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r2_hidden(X2,X0) => (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1)))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f45,plain,(
% 7.41/1.41    ! [X0,X1,X2,X3] : (((r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1) | ~r2_hidden(X2,X0)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.41/1.41    inference(ennf_transformation,[],[f24])).
% 7.41/1.41  
% 7.41/1.41  fof(f46,plain,(
% 7.41/1.41    ! [X0,X1,X2,X3] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.41/1.41    inference(flattening,[],[f45])).
% 7.41/1.41  
% 7.41/1.41  fof(f110,plain,(
% 7.41/1.41    ( ! [X2,X0,X3,X1] : (r2_hidden(k1_funct_1(X3,X2),k2_relset_1(X0,X1,X3)) | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.41/1.41    inference(cnf_transformation,[],[f46])).
% 7.41/1.41  
% 7.41/1.41  fof(f112,plain,(
% 7.41/1.41    v1_funct_2(sK4,k1_tarski(sK2),sK3)),
% 7.41/1.41    inference(cnf_transformation,[],[f64])).
% 7.41/1.41  
% 7.41/1.41  fof(f137,plain,(
% 7.41/1.41    v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3)),
% 7.41/1.41    inference(definition_unfolding,[],[f112,f117])).
% 7.41/1.41  
% 7.41/1.41  fof(f114,plain,(
% 7.41/1.41    k1_xboole_0 != sK3),
% 7.41/1.41    inference(cnf_transformation,[],[f64])).
% 7.41/1.41  
% 7.41/1.41  fof(f17,axiom,(
% 7.41/1.41    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f37,plain,(
% 7.41/1.41    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.41/1.41    inference(ennf_transformation,[],[f17])).
% 7.41/1.41  
% 7.41/1.41  fof(f100,plain,(
% 7.41/1.41    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.41/1.41    inference(cnf_transformation,[],[f37])).
% 7.41/1.41  
% 7.41/1.41  fof(f14,axiom,(
% 7.41/1.41    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 7.41/1.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.41/1.41  
% 7.41/1.41  fof(f97,plain,(
% 7.41/1.41    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 7.41/1.41    inference(cnf_transformation,[],[f14])).
% 7.41/1.41  
% 7.41/1.41  cnf(c_23,plain,
% 7.41/1.41      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 7.41/1.41      inference(cnf_transformation,[],[f91]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1969,plain,
% 7.41/1.41      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_25,plain,
% 7.41/1.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.41/1.41      inference(cnf_transformation,[],[f92]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1967,plain,
% 7.41/1.41      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.41/1.41      | r1_tarski(X0,X1) = iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_3655,plain,
% 7.41/1.41      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_1969,c_1967]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_45,negated_conjecture,
% 7.41/1.41      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) ),
% 7.41/1.41      inference(cnf_transformation,[],[f136]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1955,plain,
% 7.41/1.41      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_36,plain,
% 7.41/1.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.41/1.41      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.41/1.41      inference(cnf_transformation,[],[f104]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1960,plain,
% 7.41/1.41      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.41/1.41      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_6552,plain,
% 7.41/1.41      ( k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_1955,c_1960]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_35,plain,
% 7.41/1.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.41/1.41      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 7.41/1.41      inference(cnf_transformation,[],[f103]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1961,plain,
% 7.41/1.41      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.41/1.41      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_6601,plain,
% 7.41/1.41      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top
% 7.41/1.41      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_6552,c_1961]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_50,plain,
% 7.41/1.41      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) = iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_7559,plain,
% 7.41/1.41      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK3)) = iProver_top ),
% 7.41/1.41      inference(global_propositional_subsumption,[status(thm)],[c_6601,c_50]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_7563,plain,
% 7.41/1.41      ( r1_tarski(k2_relat_1(sK4),sK3) = iProver_top ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_7559,c_1967]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_34,plain,
% 7.41/1.41      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.41/1.41      inference(cnf_transformation,[],[f102]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_27,plain,
% 7.41/1.41      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 7.41/1.41      inference(cnf_transformation,[],[f95]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_530,plain,
% 7.41/1.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.41/1.41      | ~ v1_relat_1(X0)
% 7.41/1.41      | k7_relat_1(X0,X1) = X0 ),
% 7.41/1.41      inference(resolution,[status(thm)],[c_34,c_27]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_33,plain,
% 7.41/1.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.41/1.41      inference(cnf_transformation,[],[f101]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_534,plain,
% 7.41/1.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.41/1.41      | k7_relat_1(X0,X1) = X0 ),
% 7.41/1.41      inference(global_propositional_subsumption,
% 7.41/1.41                [status(thm)],
% 7.41/1.41                [c_530,c_34,c_33,c_27]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1953,plain,
% 7.41/1.41      ( k7_relat_1(X0,X1) = X0
% 7.41/1.41      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_2637,plain,
% 7.41/1.41      ( k7_relat_1(sK4,k2_enumset1(sK2,sK2,sK2,sK2)) = sK4 ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_1955,c_1953]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_30,plain,
% 7.41/1.41      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) | ~ v1_relat_1(X0) ),
% 7.41/1.41      inference(cnf_transformation,[],[f98]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1965,plain,
% 7.41/1.41      ( r1_tarski(k1_relat_1(k7_relat_1(X0,X1)),X1) = iProver_top
% 7.41/1.41      | v1_relat_1(X0) != iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_6260,plain,
% 7.41/1.41      ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top
% 7.41/1.41      | v1_relat_1(sK4) != iProver_top ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_2637,c_1965]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_2981,plain,
% 7.41/1.41      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK4) ),
% 7.41/1.41      inference(instantiation,[status(thm)],[c_33]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_5065,plain,
% 7.41/1.41      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 7.41/1.41      | v1_relat_1(sK4) ),
% 7.41/1.41      inference(instantiation,[status(thm)],[c_2981]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_5066,plain,
% 7.41/1.41      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3))) != iProver_top
% 7.41/1.41      | v1_relat_1(sK4) = iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_5065]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_7013,plain,
% 7.41/1.41      ( r1_tarski(k1_relat_1(sK4),k2_enumset1(sK2,sK2,sK2,sK2)) = iProver_top ),
% 7.41/1.41      inference(global_propositional_subsumption,
% 7.41/1.41                [status(thm)],
% 7.41/1.41                [c_6260,c_50,c_5066]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_22,plain,
% 7.41/1.41      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 7.41/1.41      | k2_enumset1(X1,X1,X2,X3) = X0
% 7.41/1.41      | k2_enumset1(X1,X1,X1,X3) = X0
% 7.41/1.41      | k2_enumset1(X2,X2,X2,X3) = X0
% 7.41/1.41      | k2_enumset1(X1,X1,X1,X2) = X0
% 7.41/1.41      | k2_enumset1(X3,X3,X3,X3) = X0
% 7.41/1.41      | k2_enumset1(X2,X2,X2,X2) = X0
% 7.41/1.41      | k2_enumset1(X1,X1,X1,X1) = X0
% 7.41/1.41      | k1_xboole_0 = X0 ),
% 7.41/1.41      inference(cnf_transformation,[],[f132]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1970,plain,
% 7.41/1.41      ( k2_enumset1(X0,X0,X1,X2) = X3
% 7.41/1.41      | k2_enumset1(X0,X0,X0,X2) = X3
% 7.41/1.41      | k2_enumset1(X1,X1,X1,X2) = X3
% 7.41/1.41      | k2_enumset1(X0,X0,X0,X1) = X3
% 7.41/1.41      | k2_enumset1(X2,X2,X2,X2) = X3
% 7.41/1.41      | k2_enumset1(X1,X1,X1,X1) = X3
% 7.41/1.41      | k2_enumset1(X0,X0,X0,X0) = X3
% 7.41/1.41      | k1_xboole_0 = X3
% 7.41/1.41      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_7073,plain,
% 7.41/1.41      ( k2_enumset1(sK2,sK2,sK2,sK2) = k1_relat_1(sK4)
% 7.41/1.41      | k1_relat_1(sK4) = k1_xboole_0 ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_7013,c_1970]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_47,negated_conjecture,
% 7.41/1.41      ( v1_funct_1(sK4) ),
% 7.41/1.41      inference(cnf_transformation,[],[f111]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_43,negated_conjecture,
% 7.41/1.41      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) ),
% 7.41/1.41      inference(cnf_transformation,[],[f135]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1142,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_2046,plain,
% 7.41/1.41      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != X0
% 7.41/1.41      | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 7.41/1.41      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != X0 ),
% 7.41/1.41      inference(instantiation,[status(thm)],[c_1142]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_2137,plain,
% 7.41/1.41      ( k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)
% 7.41/1.41      | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) != k2_relat_1(sK4)
% 7.41/1.41      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) != k2_relat_1(sK4) ),
% 7.41/1.41      inference(instantiation,[status(thm)],[c_2046]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_2245,plain,
% 7.41/1.41      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 7.41/1.41      | k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4) = k2_relat_1(sK4) ),
% 7.41/1.41      inference(instantiation,[status(thm)],[c_36]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_31,plain,
% 7.41/1.41      ( ~ v1_funct_1(X0)
% 7.41/1.41      | ~ v1_relat_1(X0)
% 7.41/1.41      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 7.41/1.41      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 7.41/1.41      inference(cnf_transformation,[],[f133]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_2671,plain,
% 7.41/1.41      ( ~ v1_funct_1(sK4)
% 7.41/1.41      | ~ v1_relat_1(sK4)
% 7.41/1.41      | k2_enumset1(k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2),k1_funct_1(sK4,sK2)) = k2_relat_1(sK4)
% 7.41/1.41      | k2_enumset1(sK2,sK2,sK2,sK2) != k1_relat_1(sK4) ),
% 7.41/1.41      inference(instantiation,[status(thm)],[c_31]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_10525,plain,
% 7.41/1.41      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 7.41/1.41      inference(global_propositional_subsumption,
% 7.41/1.41                [status(thm)],
% 7.41/1.41                [c_7073,c_47,c_45,c_43,c_2137,c_2245,c_2671,c_5065]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_12,plain,
% 7.41/1.41      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.41/1.41      inference(cnf_transformation,[],[f146]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_37,plain,
% 7.41/1.41      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.41/1.41      | ~ r1_tarski(k1_relat_1(X0),X1)
% 7.41/1.41      | ~ r1_tarski(k2_relat_1(X0),X2)
% 7.41/1.41      | ~ v1_relat_1(X0) ),
% 7.41/1.41      inference(cnf_transformation,[],[f105]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1959,plain,
% 7.41/1.41      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 7.41/1.41      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.41/1.41      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.41/1.41      | v1_relat_1(X0) != iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_4254,plain,
% 7.41/1.41      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) = iProver_top
% 7.41/1.41      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 7.41/1.41      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 7.41/1.41      | v1_relat_1(X0) != iProver_top ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_1959,c_1967]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_12567,plain,
% 7.41/1.41      ( r1_tarski(X0,k1_xboole_0) = iProver_top
% 7.41/1.41      | r1_tarski(k1_relat_1(X0),k1_xboole_0) != iProver_top
% 7.41/1.41      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 7.41/1.41      | v1_relat_1(X0) != iProver_top ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_12,c_4254]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_12744,plain,
% 7.41/1.41      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 7.41/1.41      | r1_tarski(sK4,k1_xboole_0) = iProver_top
% 7.41/1.41      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top
% 7.41/1.41      | v1_relat_1(sK4) != iProver_top ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_10525,c_12567]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_94,plain,
% 7.41/1.41      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.41/1.41      | r1_tarski(X0,X1) = iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_96,plain,
% 7.41/1.41      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 7.41/1.41      | r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.41/1.41      inference(instantiation,[status(thm)],[c_94]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_100,plain,
% 7.41/1.41      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_102,plain,
% 7.41/1.41      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 7.41/1.41      inference(instantiation,[status(thm)],[c_100]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_14165,plain,
% 7.41/1.41      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 7.41/1.41      | r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 7.41/1.41      inference(global_propositional_subsumption,
% 7.41/1.41                [status(thm)],
% 7.41/1.41                [c_12744,c_50,c_96,c_102,c_5066]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_14171,plain,
% 7.41/1.41      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_7563,c_14165]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1,plain,
% 7.41/1.41      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.41/1.41      inference(cnf_transformation,[],[f68]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1987,plain,
% 7.41/1.41      ( X0 = X1
% 7.41/1.41      | r1_tarski(X1,X0) != iProver_top
% 7.41/1.41      | r1_tarski(X0,X1) != iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_14174,plain,
% 7.41/1.41      ( sK4 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_14171,c_1987]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_16366,plain,
% 7.41/1.41      ( sK4 = k1_xboole_0 ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_3655,c_14174]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_8,plain,
% 7.41/1.41      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) ),
% 7.41/1.41      inference(cnf_transformation,[],[f141]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1981,plain,
% 7.41/1.41      ( r2_hidden(X0,k2_enumset1(X1,X1,X1,X0)) = iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_42,plain,
% 7.41/1.41      ( ~ v1_funct_2(X0,X1,X2)
% 7.41/1.41      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.41/1.41      | ~ r2_hidden(X3,X1)
% 7.41/1.41      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 7.41/1.41      | ~ v1_funct_1(X0)
% 7.41/1.41      | k1_xboole_0 = X2 ),
% 7.41/1.41      inference(cnf_transformation,[],[f110]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_46,negated_conjecture,
% 7.41/1.41      ( v1_funct_2(sK4,k2_enumset1(sK2,sK2,sK2,sK2),sK3) ),
% 7.41/1.41      inference(cnf_transformation,[],[f137]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_550,plain,
% 7.41/1.41      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.41/1.41      | ~ r2_hidden(X3,X1)
% 7.41/1.41      | r2_hidden(k1_funct_1(X0,X3),k2_relset_1(X1,X2,X0))
% 7.41/1.41      | ~ v1_funct_1(X0)
% 7.41/1.41      | k2_enumset1(sK2,sK2,sK2,sK2) != X1
% 7.41/1.41      | sK3 != X2
% 7.41/1.41      | sK4 != X0
% 7.41/1.41      | k1_xboole_0 = X2 ),
% 7.41/1.41      inference(resolution_lifted,[status(thm)],[c_42,c_46]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_551,plain,
% 7.41/1.41      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3)))
% 7.41/1.41      | ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 7.41/1.41      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4))
% 7.41/1.41      | ~ v1_funct_1(sK4)
% 7.41/1.41      | k1_xboole_0 = sK3 ),
% 7.41/1.41      inference(unflattening,[status(thm)],[c_550]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_44,negated_conjecture,
% 7.41/1.41      ( k1_xboole_0 != sK3 ),
% 7.41/1.41      inference(cnf_transformation,[],[f114]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_555,plain,
% 7.41/1.41      ( ~ r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2))
% 7.41/1.41      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) ),
% 7.41/1.41      inference(global_propositional_subsumption,
% 7.41/1.41                [status(thm)],
% 7.41/1.41                [c_551,c_47,c_45,c_44]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1952,plain,
% 7.41/1.41      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 7.41/1.41      | r2_hidden(k1_funct_1(sK4,X0),k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4)) = iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_555]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_32,plain,
% 7.41/1.41      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.41/1.41      inference(cnf_transformation,[],[f100]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_1963,plain,
% 7.41/1.41      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 7.41/1.41      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_3515,plain,
% 7.41/1.41      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 7.41/1.41      | r1_tarski(k2_relset_1(k2_enumset1(sK2,sK2,sK2,sK2),sK3,sK4),k1_funct_1(sK4,X0)) != iProver_top ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_1952,c_1963]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_6579,plain,
% 7.41/1.41      ( r2_hidden(X0,k2_enumset1(sK2,sK2,sK2,sK2)) != iProver_top
% 7.41/1.41      | r1_tarski(k2_relat_1(sK4),k1_funct_1(sK4,X0)) != iProver_top ),
% 7.41/1.41      inference(demodulation,[status(thm)],[c_6552,c_3515]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_7457,plain,
% 7.41/1.41      ( r1_tarski(k2_relat_1(sK4),k1_funct_1(sK4,sK2)) != iProver_top ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_1981,c_6579]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_21782,plain,
% 7.41/1.41      ( r1_tarski(k2_relat_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK2)) != iProver_top ),
% 7.41/1.41      inference(demodulation,[status(thm)],[c_16366,c_7457]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_28,plain,
% 7.41/1.41      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 7.41/1.41      inference(cnf_transformation,[],[f97]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_21811,plain,
% 7.41/1.41      ( r1_tarski(k1_xboole_0,k1_funct_1(k1_xboole_0,sK2)) != iProver_top ),
% 7.41/1.41      inference(light_normalisation,[status(thm)],[c_21782,c_28]) ).
% 7.41/1.41  
% 7.41/1.41  cnf(c_22404,plain,
% 7.41/1.41      ( $false ),
% 7.41/1.41      inference(superposition,[status(thm)],[c_3655,c_21811]) ).
% 7.41/1.41  
% 7.41/1.41  
% 7.41/1.41  % SZS output end CNFRefutation for theBenchmark.p
% 7.41/1.41  
% 7.41/1.41  ------                               Statistics
% 7.41/1.41  
% 7.41/1.41  ------ General
% 7.41/1.41  
% 7.41/1.41  abstr_ref_over_cycles:                  0
% 7.41/1.41  abstr_ref_under_cycles:                 0
% 7.41/1.41  gc_basic_clause_elim:                   0
% 7.41/1.41  forced_gc_time:                         0
% 7.41/1.41  parsing_time:                           0.009
% 7.41/1.41  unif_index_cands_time:                  0.
% 7.41/1.41  unif_index_add_time:                    0.
% 7.41/1.41  orderings_time:                         0.
% 7.41/1.41  out_proof_time:                         0.012
% 7.41/1.41  total_time:                             0.633
% 7.41/1.41  num_of_symbols:                         54
% 7.41/1.41  num_of_terms:                           22476
% 7.41/1.41  
% 7.41/1.41  ------ Preprocessing
% 7.41/1.41  
% 7.41/1.41  num_of_splits:                          0
% 7.41/1.41  num_of_split_atoms:                     1
% 7.41/1.41  num_of_reused_defs:                     0
% 7.41/1.41  num_eq_ax_congr_red:                    20
% 7.41/1.41  num_of_sem_filtered_clauses:            1
% 7.41/1.41  num_of_subtypes:                        0
% 7.41/1.41  monotx_restored_types:                  0
% 7.41/1.41  sat_num_of_epr_types:                   0
% 7.41/1.41  sat_num_of_non_cyclic_types:            0
% 7.41/1.41  sat_guarded_non_collapsed_types:        0
% 7.41/1.41  num_pure_diseq_elim:                    0
% 7.41/1.41  simp_replaced_by:                       0
% 7.41/1.41  res_preprocessed:                       213
% 7.41/1.41  prep_upred:                             0
% 7.41/1.41  prep_unflattend:                        13
% 7.41/1.41  smt_new_axioms:                         0
% 7.41/1.41  pred_elim_cands:                        6
% 7.41/1.41  pred_elim:                              2
% 7.41/1.41  pred_elim_cl:                           2
% 7.41/1.41  pred_elim_cycles:                       6
% 7.41/1.41  merged_defs:                            8
% 7.41/1.41  merged_defs_ncl:                        0
% 7.41/1.41  bin_hyper_res:                          8
% 7.41/1.41  prep_cycles:                            4
% 7.41/1.41  pred_elim_time:                         0.005
% 7.41/1.41  splitting_time:                         0.
% 7.41/1.41  sem_filter_time:                        0.
% 7.41/1.41  monotx_time:                            0.
% 7.41/1.41  subtype_inf_time:                       0.
% 7.41/1.41  
% 7.41/1.41  ------ Problem properties
% 7.41/1.41  
% 7.41/1.41  clauses:                                45
% 7.41/1.41  conjectures:                            4
% 7.41/1.41  epr:                                    7
% 7.41/1.41  horn:                                   41
% 7.41/1.41  ground:                                 7
% 7.41/1.41  unary:                                  24
% 7.41/1.41  binary:                                 10
% 7.41/1.41  lits:                                   86
% 7.41/1.41  lits_eq:                                34
% 7.41/1.41  fd_pure:                                0
% 7.41/1.41  fd_pseudo:                              0
% 7.41/1.41  fd_cond:                                1
% 7.41/1.41  fd_pseudo_cond:                         6
% 7.41/1.41  ac_symbols:                             0
% 7.41/1.41  
% 7.41/1.41  ------ Propositional Solver
% 7.41/1.41  
% 7.41/1.41  prop_solver_calls:                      31
% 7.41/1.41  prop_fast_solver_calls:                 1578
% 7.41/1.41  smt_solver_calls:                       0
% 7.41/1.41  smt_fast_solver_calls:                  0
% 7.41/1.41  prop_num_of_clauses:                    9319
% 7.41/1.41  prop_preprocess_simplified:             23257
% 7.41/1.41  prop_fo_subsumed:                       30
% 7.41/1.41  prop_solver_time:                       0.
% 7.41/1.41  smt_solver_time:                        0.
% 7.41/1.41  smt_fast_solver_time:                   0.
% 7.41/1.41  prop_fast_solver_time:                  0.
% 7.41/1.41  prop_unsat_core_time:                   0.
% 7.41/1.41  
% 7.41/1.41  ------ QBF
% 7.41/1.41  
% 7.41/1.41  qbf_q_res:                              0
% 7.41/1.41  qbf_num_tautologies:                    0
% 7.41/1.41  qbf_prep_cycles:                        0
% 7.41/1.41  
% 7.41/1.41  ------ BMC1
% 7.41/1.41  
% 7.41/1.41  bmc1_current_bound:                     -1
% 7.41/1.41  bmc1_last_solved_bound:                 -1
% 7.41/1.41  bmc1_unsat_core_size:                   -1
% 7.41/1.41  bmc1_unsat_core_parents_size:           -1
% 7.41/1.41  bmc1_merge_next_fun:                    0
% 7.41/1.41  bmc1_unsat_core_clauses_time:           0.
% 7.41/1.41  
% 7.41/1.41  ------ Instantiation
% 7.41/1.41  
% 7.41/1.41  inst_num_of_clauses:                    2888
% 7.41/1.41  inst_num_in_passive:                    1835
% 7.41/1.41  inst_num_in_active:                     888
% 7.41/1.41  inst_num_in_unprocessed:                165
% 7.41/1.41  inst_num_of_loops:                      1090
% 7.41/1.41  inst_num_of_learning_restarts:          0
% 7.41/1.41  inst_num_moves_active_passive:          202
% 7.41/1.41  inst_lit_activity:                      0
% 7.41/1.41  inst_lit_activity_moves:                0
% 7.41/1.41  inst_num_tautologies:                   0
% 7.41/1.41  inst_num_prop_implied:                  0
% 7.41/1.41  inst_num_existing_simplified:           0
% 7.41/1.41  inst_num_eq_res_simplified:             0
% 7.41/1.41  inst_num_child_elim:                    0
% 7.41/1.41  inst_num_of_dismatching_blockings:      1415
% 7.41/1.41  inst_num_of_non_proper_insts:           2805
% 7.41/1.41  inst_num_of_duplicates:                 0
% 7.41/1.41  inst_inst_num_from_inst_to_res:         0
% 7.41/1.41  inst_dismatching_checking_time:         0.
% 7.41/1.41  
% 7.41/1.41  ------ Resolution
% 7.41/1.41  
% 7.41/1.41  res_num_of_clauses:                     0
% 7.41/1.41  res_num_in_passive:                     0
% 7.41/1.41  res_num_in_active:                      0
% 7.41/1.41  res_num_of_loops:                       217
% 7.41/1.41  res_forward_subset_subsumed:            293
% 7.41/1.41  res_backward_subset_subsumed:           0
% 7.41/1.41  res_forward_subsumed:                   0
% 7.41/1.41  res_backward_subsumed:                  0
% 7.41/1.41  res_forward_subsumption_resolution:     0
% 7.41/1.41  res_backward_subsumption_resolution:    0
% 7.41/1.41  res_clause_to_clause_subsumption:       2258
% 7.41/1.41  res_orphan_elimination:                 0
% 7.41/1.41  res_tautology_del:                      125
% 7.41/1.41  res_num_eq_res_simplified:              0
% 7.41/1.41  res_num_sel_changes:                    0
% 7.41/1.41  res_moves_from_active_to_pass:          0
% 7.41/1.41  
% 7.41/1.41  ------ Superposition
% 7.41/1.41  
% 7.41/1.41  sup_time_total:                         0.
% 7.41/1.41  sup_time_generating:                    0.
% 7.41/1.41  sup_time_sim_full:                      0.
% 7.41/1.41  sup_time_sim_immed:                     0.
% 7.41/1.41  
% 7.41/1.41  sup_num_of_clauses:                     399
% 7.41/1.41  sup_num_in_active:                      119
% 7.41/1.41  sup_num_in_passive:                     280
% 7.41/1.41  sup_num_of_loops:                       216
% 7.41/1.41  sup_fw_superposition:                   352
% 7.41/1.41  sup_bw_superposition:                   355
% 7.41/1.41  sup_immediate_simplified:               433
% 7.41/1.41  sup_given_eliminated:                   4
% 7.41/1.41  comparisons_done:                       0
% 7.41/1.41  comparisons_avoided:                    145
% 7.41/1.41  
% 7.41/1.41  ------ Simplifications
% 7.41/1.41  
% 7.41/1.41  
% 7.41/1.41  sim_fw_subset_subsumed:                 25
% 7.41/1.41  sim_bw_subset_subsumed:                 23
% 7.41/1.41  sim_fw_subsumed:                        59
% 7.41/1.41  sim_bw_subsumed:                        21
% 7.41/1.41  sim_fw_subsumption_res:                 0
% 7.41/1.41  sim_bw_subsumption_res:                 0
% 7.41/1.41  sim_tautology_del:                      6
% 7.41/1.41  sim_eq_tautology_del:                   74
% 7.41/1.41  sim_eq_res_simp:                        0
% 7.41/1.41  sim_fw_demodulated:                     167
% 7.41/1.41  sim_bw_demodulated:                     222
% 7.41/1.41  sim_light_normalised:                   128
% 7.41/1.41  sim_joinable_taut:                      0
% 7.41/1.41  sim_joinable_simp:                      0
% 7.41/1.41  sim_ac_normalised:                      0
% 7.41/1.41  sim_smt_subsumption:                    0
% 7.41/1.41  
%------------------------------------------------------------------------------
