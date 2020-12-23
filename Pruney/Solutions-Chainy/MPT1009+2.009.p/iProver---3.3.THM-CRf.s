%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:30 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 835 expanded)
%              Number of clauses        :   90 ( 219 expanded)
%              Number of leaves         :   19 ( 188 expanded)
%              Depth                    :   22
%              Number of atoms          :  404 (2087 expanded)
%              Number of equality atoms :  171 ( 744 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f42])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f50])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f75])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f72,f76])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f35])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_enumset1(X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f51,f76,f76])).

fof(f74,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f74,f76,f76])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(definition_unfolding,[],[f64,f76,f76])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f55])).

cnf(c_16,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1523,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1529,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1525,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_374,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_15])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_378,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_374,c_18])).

cnf(c_379,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_378])).

cnf(c_1515,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_2310,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1525,c_1515])).

cnf(c_4047,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1529,c_2310])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1531,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4282,plain,
    ( k2_relat_1(k1_xboole_0) = X0
    | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4047,c_1531])).

cnf(c_6612,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0)
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1523,c_4282])).

cnf(c_1649,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1913,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1649])).

cnf(c_1915,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1913])).

cnf(c_1914,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1919,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1914])).

cnf(c_2708,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2709,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2708])).

cnf(c_6952,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6612,c_1915,c_1919,c_2709])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1519,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1869,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_1515])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_353,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_13])).

cnf(c_357,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_353,c_18])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_357])).

cnf(c_1516,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_358])).

cnf(c_2398,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1519,c_1516])).

cnf(c_6,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1526,plain,
    ( k2_enumset1(X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3213,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2398,c_1526])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1654,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_330,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_331,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_1517,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_331])).

cnf(c_1706,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1517,c_26,c_331,c_1654])).

cnf(c_1707,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1706])).

cnf(c_1708,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1694,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1810,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1694])).

cnf(c_1083,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1688,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_1083])).

cnf(c_1809,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_1965,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1809])).

cnf(c_1740,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1966,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1740])).

cnf(c_3895,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3213,c_26,c_24,c_1654,c_1708,c_1810,c_1965,c_1966])).

cnf(c_22,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_315,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_316,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_1518,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_29,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_317,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_316])).

cnf(c_1655,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1654])).

cnf(c_1664,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1518,c_29,c_317,c_1655])).

cnf(c_1665,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1664])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1524,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2133,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1665,c_1524])).

cnf(c_3902,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3895,c_2133])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3916,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3902,c_8])).

cnf(c_4076,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_3916])).

cnf(c_4176,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4076,c_1531])).

cnf(c_2504,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2507,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2504])).

cnf(c_2485,plain,
    ( ~ r1_tarski(X0,sK3)
    | ~ r1_tarski(sK3,X0)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_4003,plain,
    ( ~ r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2485])).

cnf(c_4004,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4003])).

cnf(c_6047,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4176,c_2507,c_4004,c_4076])).

cnf(c_1521,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3368,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1519,c_1521])).

cnf(c_1520,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3591,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3368,c_1520])).

cnf(c_6061,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6047,c_3591])).

cnf(c_6958,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6952,c_6061])).

cnf(c_7062,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6958,c_4047])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:33:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.10/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.10/0.99  
% 3.10/0.99  ------  iProver source info
% 3.10/0.99  
% 3.10/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.10/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.10/0.99  git: non_committed_changes: false
% 3.10/0.99  git: last_make_outside_of_git: false
% 3.10/0.99  
% 3.10/0.99  ------ 
% 3.10/0.99  
% 3.10/0.99  ------ Input Options
% 3.10/0.99  
% 3.10/0.99  --out_options                           all
% 3.10/0.99  --tptp_safe_out                         true
% 3.10/0.99  --problem_path                          ""
% 3.10/0.99  --include_path                          ""
% 3.10/0.99  --clausifier                            res/vclausify_rel
% 3.10/0.99  --clausifier_options                    --mode clausify
% 3.10/0.99  --stdin                                 false
% 3.10/0.99  --stats_out                             all
% 3.10/0.99  
% 3.10/0.99  ------ General Options
% 3.10/0.99  
% 3.10/0.99  --fof                                   false
% 3.10/0.99  --time_out_real                         305.
% 3.10/0.99  --time_out_virtual                      -1.
% 3.10/0.99  --symbol_type_check                     false
% 3.10/0.99  --clausify_out                          false
% 3.10/0.99  --sig_cnt_out                           false
% 3.10/0.99  --trig_cnt_out                          false
% 3.10/0.99  --trig_cnt_out_tolerance                1.
% 3.10/0.99  --trig_cnt_out_sk_spl                   false
% 3.10/0.99  --abstr_cl_out                          false
% 3.10/0.99  
% 3.10/0.99  ------ Global Options
% 3.10/0.99  
% 3.10/0.99  --schedule                              default
% 3.10/0.99  --add_important_lit                     false
% 3.10/0.99  --prop_solver_per_cl                    1000
% 3.10/0.99  --min_unsat_core                        false
% 3.10/0.99  --soft_assumptions                      false
% 3.10/0.99  --soft_lemma_size                       3
% 3.10/0.99  --prop_impl_unit_size                   0
% 3.10/0.99  --prop_impl_unit                        []
% 3.10/0.99  --share_sel_clauses                     true
% 3.10/0.99  --reset_solvers                         false
% 3.10/0.99  --bc_imp_inh                            [conj_cone]
% 3.10/0.99  --conj_cone_tolerance                   3.
% 3.10/0.99  --extra_neg_conj                        none
% 3.10/0.99  --large_theory_mode                     true
% 3.10/0.99  --prolific_symb_bound                   200
% 3.10/0.99  --lt_threshold                          2000
% 3.10/0.99  --clause_weak_htbl                      true
% 3.10/0.99  --gc_record_bc_elim                     false
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing Options
% 3.10/0.99  
% 3.10/0.99  --preprocessing_flag                    true
% 3.10/0.99  --time_out_prep_mult                    0.1
% 3.10/0.99  --splitting_mode                        input
% 3.10/0.99  --splitting_grd                         true
% 3.10/0.99  --splitting_cvd                         false
% 3.10/0.99  --splitting_cvd_svl                     false
% 3.10/0.99  --splitting_nvd                         32
% 3.10/0.99  --sub_typing                            true
% 3.10/0.99  --prep_gs_sim                           true
% 3.10/0.99  --prep_unflatten                        true
% 3.10/0.99  --prep_res_sim                          true
% 3.10/0.99  --prep_upred                            true
% 3.10/0.99  --prep_sem_filter                       exhaustive
% 3.10/0.99  --prep_sem_filter_out                   false
% 3.10/0.99  --pred_elim                             true
% 3.10/0.99  --res_sim_input                         true
% 3.10/0.99  --eq_ax_congr_red                       true
% 3.10/0.99  --pure_diseq_elim                       true
% 3.10/0.99  --brand_transform                       false
% 3.10/0.99  --non_eq_to_eq                          false
% 3.10/0.99  --prep_def_merge                        true
% 3.10/0.99  --prep_def_merge_prop_impl              false
% 3.10/0.99  --prep_def_merge_mbd                    true
% 3.10/0.99  --prep_def_merge_tr_red                 false
% 3.10/0.99  --prep_def_merge_tr_cl                  false
% 3.10/0.99  --smt_preprocessing                     true
% 3.10/0.99  --smt_ac_axioms                         fast
% 3.10/0.99  --preprocessed_out                      false
% 3.10/0.99  --preprocessed_stats                    false
% 3.10/0.99  
% 3.10/0.99  ------ Abstraction refinement Options
% 3.10/0.99  
% 3.10/0.99  --abstr_ref                             []
% 3.10/0.99  --abstr_ref_prep                        false
% 3.10/0.99  --abstr_ref_until_sat                   false
% 3.10/0.99  --abstr_ref_sig_restrict                funpre
% 3.10/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.99  --abstr_ref_under                       []
% 3.10/0.99  
% 3.10/0.99  ------ SAT Options
% 3.10/0.99  
% 3.10/0.99  --sat_mode                              false
% 3.10/0.99  --sat_fm_restart_options                ""
% 3.10/0.99  --sat_gr_def                            false
% 3.10/0.99  --sat_epr_types                         true
% 3.10/0.99  --sat_non_cyclic_types                  false
% 3.10/0.99  --sat_finite_models                     false
% 3.10/0.99  --sat_fm_lemmas                         false
% 3.10/0.99  --sat_fm_prep                           false
% 3.10/0.99  --sat_fm_uc_incr                        true
% 3.10/0.99  --sat_out_model                         small
% 3.10/0.99  --sat_out_clauses                       false
% 3.10/0.99  
% 3.10/0.99  ------ QBF Options
% 3.10/0.99  
% 3.10/0.99  --qbf_mode                              false
% 3.10/0.99  --qbf_elim_univ                         false
% 3.10/0.99  --qbf_dom_inst                          none
% 3.10/0.99  --qbf_dom_pre_inst                      false
% 3.10/0.99  --qbf_sk_in                             false
% 3.10/0.99  --qbf_pred_elim                         true
% 3.10/0.99  --qbf_split                             512
% 3.10/0.99  
% 3.10/0.99  ------ BMC1 Options
% 3.10/0.99  
% 3.10/0.99  --bmc1_incremental                      false
% 3.10/0.99  --bmc1_axioms                           reachable_all
% 3.10/0.99  --bmc1_min_bound                        0
% 3.10/0.99  --bmc1_max_bound                        -1
% 3.10/0.99  --bmc1_max_bound_default                -1
% 3.10/0.99  --bmc1_symbol_reachability              true
% 3.10/0.99  --bmc1_property_lemmas                  false
% 3.10/0.99  --bmc1_k_induction                      false
% 3.10/0.99  --bmc1_non_equiv_states                 false
% 3.10/0.99  --bmc1_deadlock                         false
% 3.10/0.99  --bmc1_ucm                              false
% 3.10/0.99  --bmc1_add_unsat_core                   none
% 3.10/0.99  --bmc1_unsat_core_children              false
% 3.10/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.99  --bmc1_out_stat                         full
% 3.10/0.99  --bmc1_ground_init                      false
% 3.10/0.99  --bmc1_pre_inst_next_state              false
% 3.10/0.99  --bmc1_pre_inst_state                   false
% 3.10/0.99  --bmc1_pre_inst_reach_state             false
% 3.10/0.99  --bmc1_out_unsat_core                   false
% 3.10/0.99  --bmc1_aig_witness_out                  false
% 3.10/0.99  --bmc1_verbose                          false
% 3.10/0.99  --bmc1_dump_clauses_tptp                false
% 3.10/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.99  --bmc1_dump_file                        -
% 3.10/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.99  --bmc1_ucm_extend_mode                  1
% 3.10/0.99  --bmc1_ucm_init_mode                    2
% 3.10/0.99  --bmc1_ucm_cone_mode                    none
% 3.10/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.99  --bmc1_ucm_relax_model                  4
% 3.10/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.99  --bmc1_ucm_layered_model                none
% 3.10/0.99  --bmc1_ucm_max_lemma_size               10
% 3.10/0.99  
% 3.10/0.99  ------ AIG Options
% 3.10/0.99  
% 3.10/0.99  --aig_mode                              false
% 3.10/0.99  
% 3.10/0.99  ------ Instantiation Options
% 3.10/0.99  
% 3.10/0.99  --instantiation_flag                    true
% 3.10/0.99  --inst_sos_flag                         false
% 3.10/0.99  --inst_sos_phase                        true
% 3.10/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel_side                     num_symb
% 3.10/0.99  --inst_solver_per_active                1400
% 3.10/0.99  --inst_solver_calls_frac                1.
% 3.10/0.99  --inst_passive_queue_type               priority_queues
% 3.10/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.99  --inst_passive_queues_freq              [25;2]
% 3.10/0.99  --inst_dismatching                      true
% 3.10/0.99  --inst_eager_unprocessed_to_passive     true
% 3.10/0.99  --inst_prop_sim_given                   true
% 3.10/0.99  --inst_prop_sim_new                     false
% 3.10/0.99  --inst_subs_new                         false
% 3.10/0.99  --inst_eq_res_simp                      false
% 3.10/0.99  --inst_subs_given                       false
% 3.10/0.99  --inst_orphan_elimination               true
% 3.10/0.99  --inst_learning_loop_flag               true
% 3.10/0.99  --inst_learning_start                   3000
% 3.10/0.99  --inst_learning_factor                  2
% 3.10/0.99  --inst_start_prop_sim_after_learn       3
% 3.10/0.99  --inst_sel_renew                        solver
% 3.10/0.99  --inst_lit_activity_flag                true
% 3.10/0.99  --inst_restr_to_given                   false
% 3.10/0.99  --inst_activity_threshold               500
% 3.10/0.99  --inst_out_proof                        true
% 3.10/0.99  
% 3.10/0.99  ------ Resolution Options
% 3.10/0.99  
% 3.10/0.99  --resolution_flag                       true
% 3.10/0.99  --res_lit_sel                           adaptive
% 3.10/0.99  --res_lit_sel_side                      none
% 3.10/0.99  --res_ordering                          kbo
% 3.10/0.99  --res_to_prop_solver                    active
% 3.10/0.99  --res_prop_simpl_new                    false
% 3.10/0.99  --res_prop_simpl_given                  true
% 3.10/0.99  --res_passive_queue_type                priority_queues
% 3.10/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.99  --res_passive_queues_freq               [15;5]
% 3.10/0.99  --res_forward_subs                      full
% 3.10/0.99  --res_backward_subs                     full
% 3.10/0.99  --res_forward_subs_resolution           true
% 3.10/0.99  --res_backward_subs_resolution          true
% 3.10/0.99  --res_orphan_elimination                true
% 3.10/0.99  --res_time_limit                        2.
% 3.10/0.99  --res_out_proof                         true
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Options
% 3.10/0.99  
% 3.10/0.99  --superposition_flag                    true
% 3.10/0.99  --sup_passive_queue_type                priority_queues
% 3.10/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.99  --demod_completeness_check              fast
% 3.10/0.99  --demod_use_ground                      true
% 3.10/0.99  --sup_to_prop_solver                    passive
% 3.10/0.99  --sup_prop_simpl_new                    true
% 3.10/0.99  --sup_prop_simpl_given                  true
% 3.10/0.99  --sup_fun_splitting                     false
% 3.10/0.99  --sup_smt_interval                      50000
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Simplification Setup
% 3.10/0.99  
% 3.10/0.99  --sup_indices_passive                   []
% 3.10/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_full_bw                           [BwDemod]
% 3.10/0.99  --sup_immed_triv                        [TrivRules]
% 3.10/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_immed_bw_main                     []
% 3.10/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  
% 3.10/0.99  ------ Combination Options
% 3.10/0.99  
% 3.10/0.99  --comb_res_mult                         3
% 3.10/0.99  --comb_sup_mult                         2
% 3.10/0.99  --comb_inst_mult                        10
% 3.10/0.99  
% 3.10/0.99  ------ Debug Options
% 3.10/0.99  
% 3.10/0.99  --dbg_backtrace                         false
% 3.10/0.99  --dbg_dump_prop_clauses                 false
% 3.10/0.99  --dbg_dump_prop_clauses_file            -
% 3.10/0.99  --dbg_out_stat                          false
% 3.10/0.99  ------ Parsing...
% 3.10/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.10/0.99  ------ Proving...
% 3.10/0.99  ------ Problem Properties 
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  clauses                                 21
% 3.10/0.99  conjectures                             3
% 3.10/0.99  EPR                                     4
% 3.10/0.99  Horn                                    19
% 3.10/0.99  unary                                   9
% 3.10/0.99  binary                                  7
% 3.10/0.99  lits                                    38
% 3.10/0.99  lits eq                                 12
% 3.10/0.99  fd_pure                                 0
% 3.10/0.99  fd_pseudo                               0
% 3.10/0.99  fd_cond                                 1
% 3.10/0.99  fd_pseudo_cond                          2
% 3.10/0.99  AC symbols                              0
% 3.10/0.99  
% 3.10/0.99  ------ Schedule dynamic 5 is on 
% 3.10/0.99  
% 3.10/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  ------ 
% 3.10/0.99  Current options:
% 3.10/0.99  ------ 
% 3.10/0.99  
% 3.10/0.99  ------ Input Options
% 3.10/0.99  
% 3.10/0.99  --out_options                           all
% 3.10/0.99  --tptp_safe_out                         true
% 3.10/0.99  --problem_path                          ""
% 3.10/0.99  --include_path                          ""
% 3.10/0.99  --clausifier                            res/vclausify_rel
% 3.10/0.99  --clausifier_options                    --mode clausify
% 3.10/0.99  --stdin                                 false
% 3.10/0.99  --stats_out                             all
% 3.10/0.99  
% 3.10/0.99  ------ General Options
% 3.10/0.99  
% 3.10/0.99  --fof                                   false
% 3.10/0.99  --time_out_real                         305.
% 3.10/0.99  --time_out_virtual                      -1.
% 3.10/0.99  --symbol_type_check                     false
% 3.10/0.99  --clausify_out                          false
% 3.10/0.99  --sig_cnt_out                           false
% 3.10/0.99  --trig_cnt_out                          false
% 3.10/0.99  --trig_cnt_out_tolerance                1.
% 3.10/0.99  --trig_cnt_out_sk_spl                   false
% 3.10/0.99  --abstr_cl_out                          false
% 3.10/0.99  
% 3.10/0.99  ------ Global Options
% 3.10/0.99  
% 3.10/0.99  --schedule                              default
% 3.10/0.99  --add_important_lit                     false
% 3.10/0.99  --prop_solver_per_cl                    1000
% 3.10/0.99  --min_unsat_core                        false
% 3.10/0.99  --soft_assumptions                      false
% 3.10/0.99  --soft_lemma_size                       3
% 3.10/0.99  --prop_impl_unit_size                   0
% 3.10/0.99  --prop_impl_unit                        []
% 3.10/0.99  --share_sel_clauses                     true
% 3.10/0.99  --reset_solvers                         false
% 3.10/0.99  --bc_imp_inh                            [conj_cone]
% 3.10/0.99  --conj_cone_tolerance                   3.
% 3.10/0.99  --extra_neg_conj                        none
% 3.10/0.99  --large_theory_mode                     true
% 3.10/0.99  --prolific_symb_bound                   200
% 3.10/0.99  --lt_threshold                          2000
% 3.10/0.99  --clause_weak_htbl                      true
% 3.10/0.99  --gc_record_bc_elim                     false
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing Options
% 3.10/0.99  
% 3.10/0.99  --preprocessing_flag                    true
% 3.10/0.99  --time_out_prep_mult                    0.1
% 3.10/0.99  --splitting_mode                        input
% 3.10/0.99  --splitting_grd                         true
% 3.10/0.99  --splitting_cvd                         false
% 3.10/0.99  --splitting_cvd_svl                     false
% 3.10/0.99  --splitting_nvd                         32
% 3.10/0.99  --sub_typing                            true
% 3.10/0.99  --prep_gs_sim                           true
% 3.10/0.99  --prep_unflatten                        true
% 3.10/0.99  --prep_res_sim                          true
% 3.10/0.99  --prep_upred                            true
% 3.10/0.99  --prep_sem_filter                       exhaustive
% 3.10/0.99  --prep_sem_filter_out                   false
% 3.10/0.99  --pred_elim                             true
% 3.10/0.99  --res_sim_input                         true
% 3.10/0.99  --eq_ax_congr_red                       true
% 3.10/0.99  --pure_diseq_elim                       true
% 3.10/0.99  --brand_transform                       false
% 3.10/0.99  --non_eq_to_eq                          false
% 3.10/0.99  --prep_def_merge                        true
% 3.10/0.99  --prep_def_merge_prop_impl              false
% 3.10/0.99  --prep_def_merge_mbd                    true
% 3.10/0.99  --prep_def_merge_tr_red                 false
% 3.10/0.99  --prep_def_merge_tr_cl                  false
% 3.10/0.99  --smt_preprocessing                     true
% 3.10/0.99  --smt_ac_axioms                         fast
% 3.10/0.99  --preprocessed_out                      false
% 3.10/0.99  --preprocessed_stats                    false
% 3.10/0.99  
% 3.10/0.99  ------ Abstraction refinement Options
% 3.10/0.99  
% 3.10/0.99  --abstr_ref                             []
% 3.10/0.99  --abstr_ref_prep                        false
% 3.10/0.99  --abstr_ref_until_sat                   false
% 3.10/0.99  --abstr_ref_sig_restrict                funpre
% 3.10/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.10/0.99  --abstr_ref_under                       []
% 3.10/0.99  
% 3.10/0.99  ------ SAT Options
% 3.10/0.99  
% 3.10/0.99  --sat_mode                              false
% 3.10/0.99  --sat_fm_restart_options                ""
% 3.10/0.99  --sat_gr_def                            false
% 3.10/0.99  --sat_epr_types                         true
% 3.10/0.99  --sat_non_cyclic_types                  false
% 3.10/0.99  --sat_finite_models                     false
% 3.10/0.99  --sat_fm_lemmas                         false
% 3.10/0.99  --sat_fm_prep                           false
% 3.10/0.99  --sat_fm_uc_incr                        true
% 3.10/0.99  --sat_out_model                         small
% 3.10/0.99  --sat_out_clauses                       false
% 3.10/0.99  
% 3.10/0.99  ------ QBF Options
% 3.10/0.99  
% 3.10/0.99  --qbf_mode                              false
% 3.10/0.99  --qbf_elim_univ                         false
% 3.10/0.99  --qbf_dom_inst                          none
% 3.10/0.99  --qbf_dom_pre_inst                      false
% 3.10/0.99  --qbf_sk_in                             false
% 3.10/0.99  --qbf_pred_elim                         true
% 3.10/0.99  --qbf_split                             512
% 3.10/0.99  
% 3.10/0.99  ------ BMC1 Options
% 3.10/0.99  
% 3.10/0.99  --bmc1_incremental                      false
% 3.10/0.99  --bmc1_axioms                           reachable_all
% 3.10/0.99  --bmc1_min_bound                        0
% 3.10/0.99  --bmc1_max_bound                        -1
% 3.10/0.99  --bmc1_max_bound_default                -1
% 3.10/0.99  --bmc1_symbol_reachability              true
% 3.10/0.99  --bmc1_property_lemmas                  false
% 3.10/0.99  --bmc1_k_induction                      false
% 3.10/0.99  --bmc1_non_equiv_states                 false
% 3.10/0.99  --bmc1_deadlock                         false
% 3.10/0.99  --bmc1_ucm                              false
% 3.10/0.99  --bmc1_add_unsat_core                   none
% 3.10/0.99  --bmc1_unsat_core_children              false
% 3.10/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.10/0.99  --bmc1_out_stat                         full
% 3.10/0.99  --bmc1_ground_init                      false
% 3.10/0.99  --bmc1_pre_inst_next_state              false
% 3.10/0.99  --bmc1_pre_inst_state                   false
% 3.10/0.99  --bmc1_pre_inst_reach_state             false
% 3.10/0.99  --bmc1_out_unsat_core                   false
% 3.10/0.99  --bmc1_aig_witness_out                  false
% 3.10/0.99  --bmc1_verbose                          false
% 3.10/0.99  --bmc1_dump_clauses_tptp                false
% 3.10/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.10/0.99  --bmc1_dump_file                        -
% 3.10/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.10/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.10/0.99  --bmc1_ucm_extend_mode                  1
% 3.10/0.99  --bmc1_ucm_init_mode                    2
% 3.10/0.99  --bmc1_ucm_cone_mode                    none
% 3.10/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.10/0.99  --bmc1_ucm_relax_model                  4
% 3.10/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.10/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.10/0.99  --bmc1_ucm_layered_model                none
% 3.10/0.99  --bmc1_ucm_max_lemma_size               10
% 3.10/0.99  
% 3.10/0.99  ------ AIG Options
% 3.10/0.99  
% 3.10/0.99  --aig_mode                              false
% 3.10/0.99  
% 3.10/0.99  ------ Instantiation Options
% 3.10/0.99  
% 3.10/0.99  --instantiation_flag                    true
% 3.10/0.99  --inst_sos_flag                         false
% 3.10/0.99  --inst_sos_phase                        true
% 3.10/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.10/0.99  --inst_lit_sel_side                     none
% 3.10/0.99  --inst_solver_per_active                1400
% 3.10/0.99  --inst_solver_calls_frac                1.
% 3.10/0.99  --inst_passive_queue_type               priority_queues
% 3.10/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.10/0.99  --inst_passive_queues_freq              [25;2]
% 3.10/0.99  --inst_dismatching                      true
% 3.10/0.99  --inst_eager_unprocessed_to_passive     true
% 3.10/0.99  --inst_prop_sim_given                   true
% 3.10/0.99  --inst_prop_sim_new                     false
% 3.10/0.99  --inst_subs_new                         false
% 3.10/0.99  --inst_eq_res_simp                      false
% 3.10/0.99  --inst_subs_given                       false
% 3.10/0.99  --inst_orphan_elimination               true
% 3.10/0.99  --inst_learning_loop_flag               true
% 3.10/0.99  --inst_learning_start                   3000
% 3.10/0.99  --inst_learning_factor                  2
% 3.10/0.99  --inst_start_prop_sim_after_learn       3
% 3.10/0.99  --inst_sel_renew                        solver
% 3.10/0.99  --inst_lit_activity_flag                true
% 3.10/0.99  --inst_restr_to_given                   false
% 3.10/0.99  --inst_activity_threshold               500
% 3.10/0.99  --inst_out_proof                        true
% 3.10/0.99  
% 3.10/0.99  ------ Resolution Options
% 3.10/0.99  
% 3.10/0.99  --resolution_flag                       false
% 3.10/0.99  --res_lit_sel                           adaptive
% 3.10/0.99  --res_lit_sel_side                      none
% 3.10/0.99  --res_ordering                          kbo
% 3.10/0.99  --res_to_prop_solver                    active
% 3.10/0.99  --res_prop_simpl_new                    false
% 3.10/0.99  --res_prop_simpl_given                  true
% 3.10/0.99  --res_passive_queue_type                priority_queues
% 3.10/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.10/0.99  --res_passive_queues_freq               [15;5]
% 3.10/0.99  --res_forward_subs                      full
% 3.10/0.99  --res_backward_subs                     full
% 3.10/0.99  --res_forward_subs_resolution           true
% 3.10/0.99  --res_backward_subs_resolution          true
% 3.10/0.99  --res_orphan_elimination                true
% 3.10/0.99  --res_time_limit                        2.
% 3.10/0.99  --res_out_proof                         true
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Options
% 3.10/0.99  
% 3.10/0.99  --superposition_flag                    true
% 3.10/0.99  --sup_passive_queue_type                priority_queues
% 3.10/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.10/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.10/0.99  --demod_completeness_check              fast
% 3.10/0.99  --demod_use_ground                      true
% 3.10/0.99  --sup_to_prop_solver                    passive
% 3.10/0.99  --sup_prop_simpl_new                    true
% 3.10/0.99  --sup_prop_simpl_given                  true
% 3.10/0.99  --sup_fun_splitting                     false
% 3.10/0.99  --sup_smt_interval                      50000
% 3.10/0.99  
% 3.10/0.99  ------ Superposition Simplification Setup
% 3.10/0.99  
% 3.10/0.99  --sup_indices_passive                   []
% 3.10/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.10/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.10/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_full_bw                           [BwDemod]
% 3.10/0.99  --sup_immed_triv                        [TrivRules]
% 3.10/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.10/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_immed_bw_main                     []
% 3.10/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.10/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.10/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.10/0.99  
% 3.10/0.99  ------ Combination Options
% 3.10/0.99  
% 3.10/0.99  --comb_res_mult                         3
% 3.10/0.99  --comb_sup_mult                         2
% 3.10/0.99  --comb_inst_mult                        10
% 3.10/0.99  
% 3.10/0.99  ------ Debug Options
% 3.10/0.99  
% 3.10/0.99  --dbg_backtrace                         false
% 3.10/0.99  --dbg_dump_prop_clauses                 false
% 3.10/0.99  --dbg_dump_prop_clauses_file            -
% 3.10/0.99  --dbg_out_stat                          false
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  ------ Proving...
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  % SZS status Theorem for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99   Resolution empty clause
% 3.10/0.99  
% 3.10/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  fof(f11,axiom,(
% 3.10/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f23,plain,(
% 3.10/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.10/0.99    inference(ennf_transformation,[],[f11])).
% 3.10/0.99  
% 3.10/0.99  fof(f63,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f23])).
% 3.10/0.99  
% 3.10/0.99  fof(f2,axiom,(
% 3.10/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f47,plain,(
% 3.10/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f2])).
% 3.10/0.99  
% 3.10/0.99  fof(f8,axiom,(
% 3.10/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f39,plain,(
% 3.10/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.10/0.99    inference(nnf_transformation,[],[f8])).
% 3.10/0.99  
% 3.10/0.99  fof(f58,plain,(
% 3.10/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f39])).
% 3.10/0.99  
% 3.10/0.99  fof(f14,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f27,plain,(
% 3.10/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.99    inference(ennf_transformation,[],[f14])).
% 3.10/0.99  
% 3.10/0.99  fof(f67,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f27])).
% 3.10/0.99  
% 3.10/0.99  fof(f10,axiom,(
% 3.10/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f22,plain,(
% 3.10/0.99    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.10/0.99    inference(ennf_transformation,[],[f10])).
% 3.10/0.99  
% 3.10/0.99  fof(f41,plain,(
% 3.10/0.99    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.10/0.99    inference(nnf_transformation,[],[f22])).
% 3.10/0.99  
% 3.10/0.99  fof(f61,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f41])).
% 3.10/0.99  
% 3.10/0.99  fof(f13,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f26,plain,(
% 3.10/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.99    inference(ennf_transformation,[],[f13])).
% 3.10/0.99  
% 3.10/0.99  fof(f65,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f26])).
% 3.10/0.99  
% 3.10/0.99  fof(f1,axiom,(
% 3.10/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f33,plain,(
% 3.10/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.10/0.99    inference(nnf_transformation,[],[f1])).
% 3.10/0.99  
% 3.10/0.99  fof(f34,plain,(
% 3.10/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.10/0.99    inference(flattening,[],[f33])).
% 3.10/0.99  
% 3.10/0.99  fof(f46,plain,(
% 3.10/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f34])).
% 3.10/0.99  
% 3.10/0.99  fof(f17,conjecture,(
% 3.10/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f18,negated_conjecture,(
% 3.10/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.10/0.99    inference(negated_conjecture,[],[f17])).
% 3.10/0.99  
% 3.10/0.99  fof(f19,plain,(
% 3.10/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.10/0.99    inference(pure_predicate_removal,[],[f18])).
% 3.10/0.99  
% 3.10/0.99  fof(f31,plain,(
% 3.10/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 3.10/0.99    inference(ennf_transformation,[],[f19])).
% 3.10/0.99  
% 3.10/0.99  fof(f32,plain,(
% 3.10/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 3.10/0.99    inference(flattening,[],[f31])).
% 3.10/0.99  
% 3.10/0.99  fof(f42,plain,(
% 3.10/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 3.10/0.99    introduced(choice_axiom,[])).
% 3.10/0.99  
% 3.10/0.99  fof(f43,plain,(
% 3.10/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 3.10/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f42])).
% 3.10/0.99  
% 3.10/0.99  fof(f72,plain,(
% 3.10/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.10/0.99    inference(cnf_transformation,[],[f43])).
% 3.10/0.99  
% 3.10/0.99  fof(f3,axiom,(
% 3.10/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f48,plain,(
% 3.10/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f3])).
% 3.10/0.99  
% 3.10/0.99  fof(f4,axiom,(
% 3.10/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f49,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f4])).
% 3.10/0.99  
% 3.10/0.99  fof(f5,axiom,(
% 3.10/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f50,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f5])).
% 3.10/0.99  
% 3.10/0.99  fof(f75,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.10/0.99    inference(definition_unfolding,[],[f49,f50])).
% 3.10/0.99  
% 3.10/0.99  fof(f76,plain,(
% 3.10/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.10/0.99    inference(definition_unfolding,[],[f48,f75])).
% 3.10/0.99  
% 3.10/0.99  fof(f82,plain,(
% 3.10/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 3.10/0.99    inference(definition_unfolding,[],[f72,f76])).
% 3.10/0.99  
% 3.10/0.99  fof(f66,plain,(
% 3.10/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f27])).
% 3.10/0.99  
% 3.10/0.99  fof(f9,axiom,(
% 3.10/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f21,plain,(
% 3.10/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.10/0.99    inference(ennf_transformation,[],[f9])).
% 3.10/0.99  
% 3.10/0.99  fof(f40,plain,(
% 3.10/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.10/0.99    inference(nnf_transformation,[],[f21])).
% 3.10/0.99  
% 3.10/0.99  fof(f59,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f40])).
% 3.10/0.99  
% 3.10/0.99  fof(f6,axiom,(
% 3.10/0.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f35,plain,(
% 3.10/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.10/0.99    inference(nnf_transformation,[],[f6])).
% 3.10/0.99  
% 3.10/0.99  fof(f36,plain,(
% 3.10/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.10/0.99    inference(flattening,[],[f35])).
% 3.10/0.99  
% 3.10/0.99  fof(f51,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f36])).
% 3.10/0.99  
% 3.10/0.99  fof(f79,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k2_enumset1(X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 3.10/0.99    inference(definition_unfolding,[],[f51,f76,f76])).
% 3.10/0.99  
% 3.10/0.99  fof(f74,plain,(
% 3.10/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 3.10/0.99    inference(cnf_transformation,[],[f43])).
% 3.10/0.99  
% 3.10/0.99  fof(f81,plain,(
% 3.10/0.99    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 3.10/0.99    inference(definition_unfolding,[],[f74,f76,f76])).
% 3.10/0.99  
% 3.10/0.99  fof(f12,axiom,(
% 3.10/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f24,plain,(
% 3.10/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.10/0.99    inference(ennf_transformation,[],[f12])).
% 3.10/0.99  
% 3.10/0.99  fof(f25,plain,(
% 3.10/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.10/0.99    inference(flattening,[],[f24])).
% 3.10/0.99  
% 3.10/0.99  fof(f64,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f25])).
% 3.10/0.99  
% 3.10/0.99  fof(f80,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.10/0.99    inference(definition_unfolding,[],[f64,f76,f76])).
% 3.10/0.99  
% 3.10/0.99  fof(f71,plain,(
% 3.10/0.99    v1_funct_1(sK3)),
% 3.10/0.99    inference(cnf_transformation,[],[f43])).
% 3.10/0.99  
% 3.10/0.99  fof(f15,axiom,(
% 3.10/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f28,plain,(
% 3.10/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.99    inference(ennf_transformation,[],[f15])).
% 3.10/0.99  
% 3.10/0.99  fof(f68,plain,(
% 3.10/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f28])).
% 3.10/0.99  
% 3.10/0.99  fof(f16,axiom,(
% 3.10/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f20,plain,(
% 3.10/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1))))),
% 3.10/0.99    inference(pure_predicate_removal,[],[f16])).
% 3.10/0.99  
% 3.10/0.99  fof(f29,plain,(
% 3.10/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.10/0.99    inference(ennf_transformation,[],[f20])).
% 3.10/0.99  
% 3.10/0.99  fof(f30,plain,(
% 3.10/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.10/0.99    inference(flattening,[],[f29])).
% 3.10/0.99  
% 3.10/0.99  fof(f70,plain,(
% 3.10/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.10/0.99    inference(cnf_transformation,[],[f30])).
% 3.10/0.99  
% 3.10/0.99  fof(f57,plain,(
% 3.10/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.10/0.99    inference(cnf_transformation,[],[f39])).
% 3.10/0.99  
% 3.10/0.99  fof(f7,axiom,(
% 3.10/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.10/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.10/0.99  
% 3.10/0.99  fof(f37,plain,(
% 3.10/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.10/0.99    inference(nnf_transformation,[],[f7])).
% 3.10/0.99  
% 3.10/0.99  fof(f38,plain,(
% 3.10/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.10/0.99    inference(flattening,[],[f37])).
% 3.10/0.99  
% 3.10/0.99  fof(f55,plain,(
% 3.10/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.10/0.99    inference(cnf_transformation,[],[f38])).
% 3.10/0.99  
% 3.10/0.99  fof(f88,plain,(
% 3.10/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.10/0.99    inference(equality_resolution,[],[f55])).
% 3.10/0.99  
% 3.10/0.99  cnf(c_16,plain,
% 3.10/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1523,plain,
% 3.10/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 3.10/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3,plain,
% 3.10/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1529,plain,
% 3.10/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_10,plain,
% 3.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1525,plain,
% 3.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.10/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_19,plain,
% 3.10/0.99      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.10/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_15,plain,
% 3.10/0.99      ( ~ v5_relat_1(X0,X1) | r1_tarski(k2_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_374,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | r1_tarski(k2_relat_1(X0),X2)
% 3.10/0.99      | ~ v1_relat_1(X0) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_19,c_15]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_18,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_378,plain,
% 3.10/0.99      ( r1_tarski(k2_relat_1(X0),X2)
% 3.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.10/0.99      inference(global_propositional_subsumption,[status(thm)],[c_374,c_18]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_379,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | r1_tarski(k2_relat_1(X0),X2) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_378]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1515,plain,
% 3.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.10/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2310,plain,
% 3.10/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.10/0.99      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1525,c_1515]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4047,plain,
% 3.10/0.99      ( r1_tarski(k2_relat_1(k1_xboole_0),X0) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1529,c_2310]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_0,plain,
% 3.10/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.10/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1531,plain,
% 3.10/0.99      ( X0 = X1
% 3.10/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.10/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4282,plain,
% 3.10/0.99      ( k2_relat_1(k1_xboole_0) = X0
% 3.10/0.99      | r1_tarski(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_4047,c_1531]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6612,plain,
% 3.10/0.99      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0)
% 3.10/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1523,c_4282]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1649,plain,
% 3.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1913,plain,
% 3.10/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.10/0.99      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_1649]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1915,plain,
% 3.10/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 3.10/0.99      | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_1913]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1914,plain,
% 3.10/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1919,plain,
% 3.10/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_1914]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2708,plain,
% 3.10/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.10/0.99      | v1_relat_1(k1_xboole_0) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2709,plain,
% 3.10/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.10/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_2708]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6952,plain,
% 3.10/0.99      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_6612,c_1915,c_1919,c_2709]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_26,negated_conjecture,
% 3.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 3.10/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1519,plain,
% 3.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1869,plain,
% 3.10/0.99      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1519,c_1515]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_20,plain,
% 3.10/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.10/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_13,plain,
% 3.10/0.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_353,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.10/0.99      | ~ v1_relat_1(X0) ),
% 3.10/0.99      inference(resolution,[status(thm)],[c_20,c_13]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_357,plain,
% 3.10/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.10/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.10/0.99      inference(global_propositional_subsumption,[status(thm)],[c_353,c_18]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_358,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_357]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1516,plain,
% 3.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.10/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_358]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2398,plain,
% 3.10/0.99      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1519,c_1516]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6,plain,
% 3.10/0.99      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X1,X1))
% 3.10/0.99      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.10/0.99      | k1_xboole_0 = X0 ),
% 3.10/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1526,plain,
% 3.10/0.99      ( k2_enumset1(X0,X0,X0,X0) = X1
% 3.10/0.99      | k1_xboole_0 = X1
% 3.10/0.99      | r1_tarski(X1,k2_enumset1(X0,X0,X0,X0)) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3213,plain,
% 3.10/0.99      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.10/0.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_2398,c_1526]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_24,negated_conjecture,
% 3.10/0.99      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.10/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1654,plain,
% 3.10/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.10/0.99      | v1_relat_1(sK3) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_17,plain,
% 3.10/0.99      ( ~ v1_funct_1(X0)
% 3.10/0.99      | ~ v1_relat_1(X0)
% 3.10/0.99      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.10/0.99      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_27,negated_conjecture,
% 3.10/0.99      ( v1_funct_1(sK3) ),
% 3.10/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_330,plain,
% 3.10/0.99      ( ~ v1_relat_1(X0)
% 3.10/0.99      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.10/0.99      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.10/0.99      | sK3 != X0 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_331,plain,
% 3.10/0.99      ( ~ v1_relat_1(sK3)
% 3.10/0.99      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.10/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_330]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1517,plain,
% 3.10/0.99      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.10/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.10/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_331]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1706,plain,
% 3.10/0.99      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.10/0.99      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_1517,c_26,c_331,c_1654]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1707,plain,
% 3.10/0.99      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.10/0.99      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_1706]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1708,plain,
% 3.10/0.99      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.10/0.99      | k2_enumset1(sK0,sK0,sK0,sK0) != k1_relat_1(sK3) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_1707]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_21,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.10/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.10/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1694,plain,
% 3.10/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.10/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1810,plain,
% 3.10/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.10/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_1694]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1083,plain,
% 3.10/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.10/0.99      theory(equality) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1688,plain,
% 3.10/0.99      ( ~ r1_tarski(X0,X1)
% 3.10/0.99      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.10/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 3.10/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_1083]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1809,plain,
% 3.10/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.10/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 3.10/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.10/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_1688]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1965,plain,
% 3.10/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.10/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 3.10/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.10/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_1809]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1740,plain,
% 3.10/0.99      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1966,plain,
% 3.10/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_1740]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3895,plain,
% 3.10/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_3213,c_26,c_24,c_1654,c_1708,c_1810,c_1965,c_1966]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_22,plain,
% 3.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.10/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.10/0.99      | ~ v1_funct_1(X0)
% 3.10/0.99      | ~ v1_relat_1(X0) ),
% 3.10/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_315,plain,
% 3.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.10/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.10/0.99      | ~ v1_relat_1(X0)
% 3.10/0.99      | sK3 != X0 ),
% 3.10/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_316,plain,
% 3.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
% 3.10/0.99      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 3.10/0.99      | ~ v1_relat_1(sK3) ),
% 3.10/0.99      inference(unflattening,[status(thm)],[c_315]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1518,plain,
% 3.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 3.10/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.10/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_29,plain,
% 3.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_317,plain,
% 3.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 3.10/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.10/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_316]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1655,plain,
% 3.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 3.10/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_1654]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1664,plain,
% 3.10/0.99      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.10/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_1518,c_29,c_317,c_1655]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1665,plain,
% 3.10/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 3.10/0.99      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 3.10/0.99      inference(renaming,[status(thm)],[c_1664]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_11,plain,
% 3.10/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.10/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1524,plain,
% 3.10/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.10/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2133,plain,
% 3.10/0.99      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.10/0.99      | r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),X0)) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1665,c_1524]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3902,plain,
% 3.10/0.99      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.10/0.99      | r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,X0)) = iProver_top ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_3895,c_2133]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_8,plain,
% 3.10/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.10/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3916,plain,
% 3.10/0.99      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 3.10/0.99      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.10/0.99      inference(light_normalisation,[status(thm)],[c_3902,c_8]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4076,plain,
% 3.10/0.99      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1869,c_3916]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4176,plain,
% 3.10/0.99      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_4076,c_1531]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2504,plain,
% 3.10/0.99      ( r1_tarski(k1_xboole_0,sK3) ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2507,plain,
% 3.10/0.99      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_2504]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_2485,plain,
% 3.10/0.99      ( ~ r1_tarski(X0,sK3) | ~ r1_tarski(sK3,X0) | sK3 = X0 ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4003,plain,
% 3.10/0.99      ( ~ r1_tarski(sK3,k1_xboole_0)
% 3.10/0.99      | ~ r1_tarski(k1_xboole_0,sK3)
% 3.10/0.99      | sK3 = k1_xboole_0 ),
% 3.10/0.99      inference(instantiation,[status(thm)],[c_2485]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_4004,plain,
% 3.10/0.99      ( sK3 = k1_xboole_0
% 3.10/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.10/0.99      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_4003]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6047,plain,
% 3.10/0.99      ( sK3 = k1_xboole_0 ),
% 3.10/0.99      inference(global_propositional_subsumption,
% 3.10/0.99                [status(thm)],
% 3.10/0.99                [c_4176,c_2507,c_4004,c_4076]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1521,plain,
% 3.10/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.10/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3368,plain,
% 3.10/0.99      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.10/0.99      inference(superposition,[status(thm)],[c_1519,c_1521]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_1520,plain,
% 3.10/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.10/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_3591,plain,
% 3.10/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_3368,c_1520]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6061,plain,
% 3.10/0.99      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_6047,c_3591]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_6958,plain,
% 3.10/0.99      ( r1_tarski(k2_relat_1(k1_xboole_0),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.10/0.99      inference(demodulation,[status(thm)],[c_6952,c_6061]) ).
% 3.10/0.99  
% 3.10/0.99  cnf(c_7062,plain,
% 3.10/0.99      ( $false ),
% 3.10/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_6958,c_4047]) ).
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.10/0.99  
% 3.10/0.99  ------                               Statistics
% 3.10/0.99  
% 3.10/0.99  ------ General
% 3.10/0.99  
% 3.10/0.99  abstr_ref_over_cycles:                  0
% 3.10/0.99  abstr_ref_under_cycles:                 0
% 3.10/0.99  gc_basic_clause_elim:                   0
% 3.10/0.99  forced_gc_time:                         0
% 3.10/0.99  parsing_time:                           0.008
% 3.10/0.99  unif_index_cands_time:                  0.
% 3.10/0.99  unif_index_add_time:                    0.
% 3.10/0.99  orderings_time:                         0.
% 3.10/0.99  out_proof_time:                         0.018
% 3.10/0.99  total_time:                             0.222
% 3.10/0.99  num_of_symbols:                         50
% 3.10/0.99  num_of_terms:                           6163
% 3.10/0.99  
% 3.10/0.99  ------ Preprocessing
% 3.10/0.99  
% 3.10/0.99  num_of_splits:                          0
% 3.10/0.99  num_of_split_atoms:                     0
% 3.10/0.99  num_of_reused_defs:                     0
% 3.10/0.99  num_eq_ax_congr_red:                    13
% 3.10/0.99  num_of_sem_filtered_clauses:            1
% 3.10/0.99  num_of_subtypes:                        0
% 3.10/0.99  monotx_restored_types:                  0
% 3.10/0.99  sat_num_of_epr_types:                   0
% 3.10/0.99  sat_num_of_non_cyclic_types:            0
% 3.10/0.99  sat_guarded_non_collapsed_types:        0
% 3.10/0.99  num_pure_diseq_elim:                    0
% 3.10/0.99  simp_replaced_by:                       0
% 3.10/0.99  res_preprocessed:                       114
% 3.10/0.99  prep_upred:                             0
% 3.10/0.99  prep_unflattend:                        34
% 3.10/0.99  smt_new_axioms:                         0
% 3.10/0.99  pred_elim_cands:                        3
% 3.10/0.99  pred_elim:                              3
% 3.10/0.99  pred_elim_cl:                           5
% 3.10/0.99  pred_elim_cycles:                       7
% 3.10/0.99  merged_defs:                            8
% 3.10/0.99  merged_defs_ncl:                        0
% 3.10/0.99  bin_hyper_res:                          8
% 3.10/0.99  prep_cycles:                            4
% 3.10/0.99  pred_elim_time:                         0.01
% 3.10/0.99  splitting_time:                         0.
% 3.10/0.99  sem_filter_time:                        0.
% 3.10/0.99  monotx_time:                            0.
% 3.10/0.99  subtype_inf_time:                       0.
% 3.10/0.99  
% 3.10/0.99  ------ Problem properties
% 3.10/0.99  
% 3.10/0.99  clauses:                                21
% 3.10/0.99  conjectures:                            3
% 3.10/0.99  epr:                                    4
% 3.10/0.99  horn:                                   19
% 3.10/0.99  ground:                                 3
% 3.10/0.99  unary:                                  9
% 3.10/0.99  binary:                                 7
% 3.10/0.99  lits:                                   38
% 3.10/0.99  lits_eq:                                12
% 3.10/0.99  fd_pure:                                0
% 3.10/0.99  fd_pseudo:                              0
% 3.10/0.99  fd_cond:                                1
% 3.10/0.99  fd_pseudo_cond:                         2
% 3.10/0.99  ac_symbols:                             0
% 3.10/0.99  
% 3.10/0.99  ------ Propositional Solver
% 3.10/0.99  
% 3.10/0.99  prop_solver_calls:                      28
% 3.10/0.99  prop_fast_solver_calls:                 753
% 3.10/0.99  smt_solver_calls:                       0
% 3.10/0.99  smt_fast_solver_calls:                  0
% 3.10/0.99  prop_num_of_clauses:                    2692
% 3.10/0.99  prop_preprocess_simplified:             7090
% 3.10/0.99  prop_fo_subsumed:                       10
% 3.10/0.99  prop_solver_time:                       0.
% 3.10/0.99  smt_solver_time:                        0.
% 3.10/0.99  smt_fast_solver_time:                   0.
% 3.10/0.99  prop_fast_solver_time:                  0.
% 3.10/0.99  prop_unsat_core_time:                   0.
% 3.10/0.99  
% 3.10/0.99  ------ QBF
% 3.10/0.99  
% 3.10/0.99  qbf_q_res:                              0
% 3.10/0.99  qbf_num_tautologies:                    0
% 3.10/0.99  qbf_prep_cycles:                        0
% 3.10/0.99  
% 3.10/0.99  ------ BMC1
% 3.10/0.99  
% 3.10/0.99  bmc1_current_bound:                     -1
% 3.10/0.99  bmc1_last_solved_bound:                 -1
% 3.10/0.99  bmc1_unsat_core_size:                   -1
% 3.10/0.99  bmc1_unsat_core_parents_size:           -1
% 3.10/0.99  bmc1_merge_next_fun:                    0
% 3.10/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.10/0.99  
% 3.10/0.99  ------ Instantiation
% 3.10/0.99  
% 3.10/0.99  inst_num_of_clauses:                    734
% 3.10/0.99  inst_num_in_passive:                    197
% 3.10/0.99  inst_num_in_active:                     411
% 3.10/0.99  inst_num_in_unprocessed:                127
% 3.10/0.99  inst_num_of_loops:                      420
% 3.10/0.99  inst_num_of_learning_restarts:          0
% 3.10/0.99  inst_num_moves_active_passive:          7
% 3.10/0.99  inst_lit_activity:                      0
% 3.10/0.99  inst_lit_activity_moves:                0
% 3.10/0.99  inst_num_tautologies:                   0
% 3.10/0.99  inst_num_prop_implied:                  0
% 3.10/0.99  inst_num_existing_simplified:           0
% 3.10/0.99  inst_num_eq_res_simplified:             0
% 3.10/0.99  inst_num_child_elim:                    0
% 3.10/0.99  inst_num_of_dismatching_blockings:      279
% 3.10/0.99  inst_num_of_non_proper_insts:           1033
% 3.10/0.99  inst_num_of_duplicates:                 0
% 3.10/0.99  inst_inst_num_from_inst_to_res:         0
% 3.10/0.99  inst_dismatching_checking_time:         0.
% 3.10/0.99  
% 3.10/0.99  ------ Resolution
% 3.10/0.99  
% 3.10/0.99  res_num_of_clauses:                     0
% 3.10/0.99  res_num_in_passive:                     0
% 3.10/0.99  res_num_in_active:                      0
% 3.10/0.99  res_num_of_loops:                       118
% 3.10/0.99  res_forward_subset_subsumed:            125
% 3.10/0.99  res_backward_subset_subsumed:           4
% 3.10/0.99  res_forward_subsumed:                   0
% 3.10/0.99  res_backward_subsumed:                  0
% 3.10/0.99  res_forward_subsumption_resolution:     0
% 3.10/0.99  res_backward_subsumption_resolution:    0
% 3.10/0.99  res_clause_to_clause_subsumption:       513
% 3.10/0.99  res_orphan_elimination:                 0
% 3.10/0.99  res_tautology_del:                      73
% 3.10/0.99  res_num_eq_res_simplified:              0
% 3.10/0.99  res_num_sel_changes:                    0
% 3.10/0.99  res_moves_from_active_to_pass:          0
% 3.10/0.99  
% 3.10/0.99  ------ Superposition
% 3.10/0.99  
% 3.10/0.99  sup_time_total:                         0.
% 3.10/0.99  sup_time_generating:                    0.
% 3.10/0.99  sup_time_sim_full:                      0.
% 3.10/0.99  sup_time_sim_immed:                     0.
% 3.10/0.99  
% 3.10/0.99  sup_num_of_clauses:                     107
% 3.10/0.99  sup_num_in_active:                      50
% 3.10/0.99  sup_num_in_passive:                     57
% 3.10/0.99  sup_num_of_loops:                       83
% 3.10/0.99  sup_fw_superposition:                   123
% 3.10/0.99  sup_bw_superposition:                   73
% 3.10/0.99  sup_immediate_simplified:               36
% 3.10/0.99  sup_given_eliminated:                   1
% 3.10/0.99  comparisons_done:                       0
% 3.10/0.99  comparisons_avoided:                    0
% 3.10/0.99  
% 3.10/0.99  ------ Simplifications
% 3.10/0.99  
% 3.10/0.99  
% 3.10/0.99  sim_fw_subset_subsumed:                 1
% 3.10/0.99  sim_bw_subset_subsumed:                 5
% 3.10/0.99  sim_fw_subsumed:                        17
% 3.10/0.99  sim_bw_subsumed:                        4
% 3.10/0.99  sim_fw_subsumption_res:                 1
% 3.10/0.99  sim_bw_subsumption_res:                 0
% 3.10/0.99  sim_tautology_del:                      4
% 3.10/0.99  sim_eq_tautology_del:                   12
% 3.10/0.99  sim_eq_res_simp:                        0
% 3.10/0.99  sim_fw_demodulated:                     1
% 3.10/0.99  sim_bw_demodulated:                     30
% 3.10/0.99  sim_light_normalised:                   24
% 3.10/0.99  sim_joinable_taut:                      0
% 3.10/0.99  sim_joinable_simp:                      0
% 3.10/0.99  sim_ac_normalised:                      0
% 3.10/0.99  sim_smt_subsumption:                    0
% 3.10/0.99  
%------------------------------------------------------------------------------
