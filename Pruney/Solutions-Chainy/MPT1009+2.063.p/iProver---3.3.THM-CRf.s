%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:41 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 749 expanded)
%              Number of clauses        :   72 ( 154 expanded)
%              Number of leaves         :   21 ( 195 expanded)
%              Depth                    :   19
%              Number of atoms          :  386 (1788 expanded)
%              Number of equality atoms :  223 ( 928 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f36])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f42])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f44,f76])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f73,f77])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

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
    inference(cnf_transformation,[],[f39])).

fof(f86,plain,(
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
    inference(definition_unfolding,[],[f47,f46,f76,f76,f76,f77,f77,f77,f46])).

fof(f75,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f75,f77,f77])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f68,f77,f77])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
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
    inference(nnf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_3204,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_377,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_13])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_381,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_22])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_381])).

cnf(c_3201,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_4029,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3204,c_3201])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_3215,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5110,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4029,c_3215])).

cnf(c_5343,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5110,c_3204])).

cnf(c_25,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3400,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3444,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_3476,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_3444])).

cnf(c_2651,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3427,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_2651])).

cnf(c_3475,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_3427])).

cnf(c_3609,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3475])).

cnf(c_14,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_3610,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_341,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_342,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_3203,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_30,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_343,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_3401,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3400])).

cnf(c_3406,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3203,c_30,c_343,c_3401])).

cnf(c_3407,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_3406])).

cnf(c_5335,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5110,c_3407])).

cnf(c_5511,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5343,c_27,c_25,c_3400,c_3476,c_3609,c_3610,c_5335])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_3208,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5523,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5511,c_3208])).

cnf(c_2648,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3956,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2648])).

cnf(c_2649,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3957,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_2649])).

cnf(c_4387,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3957])).

cnf(c_4388,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_4387])).

cnf(c_4819,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_5540,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5523,c_27,c_25,c_3400,c_3476,c_3609,c_3610,c_3956,c_4388,c_4819,c_5335])).

cnf(c_3206,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4980,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_3204,c_3206])).

cnf(c_3205,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5195,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4980,c_3205])).

cnf(c_5544,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5540,c_5195])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_3214,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3207,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4045,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3214,c_3207])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3210,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4477,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_4045,c_3210])).

cnf(c_17,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_16,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_360,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_23,c_16])).

cnf(c_364,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_360,c_23,c_22,c_16])).

cnf(c_3202,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_364])).

cnf(c_4482,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3214,c_3202])).

cnf(c_4777,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_4477,c_17,c_4482])).

cnf(c_5569,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5544,c_4777])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3212,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3496,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3214,c_3212])).

cnf(c_5668,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5569,c_3496])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:21:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.57/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.57/1.02  
% 2.57/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.57/1.02  
% 2.57/1.02  ------  iProver source info
% 2.57/1.02  
% 2.57/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.57/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.57/1.02  git: non_committed_changes: false
% 2.57/1.02  git: last_make_outside_of_git: false
% 2.57/1.02  
% 2.57/1.02  ------ 
% 2.57/1.02  
% 2.57/1.02  ------ Input Options
% 2.57/1.02  
% 2.57/1.02  --out_options                           all
% 2.57/1.02  --tptp_safe_out                         true
% 2.57/1.02  --problem_path                          ""
% 2.57/1.02  --include_path                          ""
% 2.57/1.02  --clausifier                            res/vclausify_rel
% 2.57/1.02  --clausifier_options                    --mode clausify
% 2.57/1.02  --stdin                                 false
% 2.57/1.02  --stats_out                             all
% 2.57/1.02  
% 2.57/1.02  ------ General Options
% 2.57/1.02  
% 2.57/1.02  --fof                                   false
% 2.57/1.02  --time_out_real                         305.
% 2.57/1.02  --time_out_virtual                      -1.
% 2.57/1.02  --symbol_type_check                     false
% 2.57/1.02  --clausify_out                          false
% 2.57/1.02  --sig_cnt_out                           false
% 2.57/1.02  --trig_cnt_out                          false
% 2.57/1.02  --trig_cnt_out_tolerance                1.
% 2.57/1.02  --trig_cnt_out_sk_spl                   false
% 2.57/1.02  --abstr_cl_out                          false
% 2.57/1.02  
% 2.57/1.02  ------ Global Options
% 2.57/1.02  
% 2.57/1.02  --schedule                              default
% 2.57/1.02  --add_important_lit                     false
% 2.57/1.02  --prop_solver_per_cl                    1000
% 2.57/1.02  --min_unsat_core                        false
% 2.57/1.02  --soft_assumptions                      false
% 2.57/1.02  --soft_lemma_size                       3
% 2.57/1.02  --prop_impl_unit_size                   0
% 2.57/1.02  --prop_impl_unit                        []
% 2.57/1.02  --share_sel_clauses                     true
% 2.57/1.02  --reset_solvers                         false
% 2.57/1.02  --bc_imp_inh                            [conj_cone]
% 2.57/1.02  --conj_cone_tolerance                   3.
% 2.57/1.02  --extra_neg_conj                        none
% 2.57/1.02  --large_theory_mode                     true
% 2.57/1.02  --prolific_symb_bound                   200
% 2.57/1.02  --lt_threshold                          2000
% 2.57/1.02  --clause_weak_htbl                      true
% 2.57/1.02  --gc_record_bc_elim                     false
% 2.57/1.02  
% 2.57/1.02  ------ Preprocessing Options
% 2.57/1.02  
% 2.57/1.02  --preprocessing_flag                    true
% 2.57/1.02  --time_out_prep_mult                    0.1
% 2.57/1.02  --splitting_mode                        input
% 2.57/1.02  --splitting_grd                         true
% 2.57/1.02  --splitting_cvd                         false
% 2.57/1.02  --splitting_cvd_svl                     false
% 2.57/1.02  --splitting_nvd                         32
% 2.57/1.02  --sub_typing                            true
% 2.57/1.02  --prep_gs_sim                           true
% 2.57/1.02  --prep_unflatten                        true
% 2.57/1.02  --prep_res_sim                          true
% 2.57/1.02  --prep_upred                            true
% 2.57/1.02  --prep_sem_filter                       exhaustive
% 2.57/1.02  --prep_sem_filter_out                   false
% 2.57/1.02  --pred_elim                             true
% 2.57/1.02  --res_sim_input                         true
% 2.57/1.02  --eq_ax_congr_red                       true
% 2.57/1.02  --pure_diseq_elim                       true
% 2.57/1.02  --brand_transform                       false
% 2.57/1.02  --non_eq_to_eq                          false
% 2.57/1.02  --prep_def_merge                        true
% 2.57/1.02  --prep_def_merge_prop_impl              false
% 2.57/1.02  --prep_def_merge_mbd                    true
% 2.57/1.02  --prep_def_merge_tr_red                 false
% 2.57/1.02  --prep_def_merge_tr_cl                  false
% 2.57/1.02  --smt_preprocessing                     true
% 2.57/1.02  --smt_ac_axioms                         fast
% 2.57/1.02  --preprocessed_out                      false
% 2.57/1.02  --preprocessed_stats                    false
% 2.57/1.02  
% 2.57/1.02  ------ Abstraction refinement Options
% 2.57/1.02  
% 2.57/1.02  --abstr_ref                             []
% 2.57/1.02  --abstr_ref_prep                        false
% 2.57/1.02  --abstr_ref_until_sat                   false
% 2.57/1.02  --abstr_ref_sig_restrict                funpre
% 2.57/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/1.02  --abstr_ref_under                       []
% 2.57/1.02  
% 2.57/1.02  ------ SAT Options
% 2.57/1.02  
% 2.57/1.02  --sat_mode                              false
% 2.57/1.02  --sat_fm_restart_options                ""
% 2.57/1.02  --sat_gr_def                            false
% 2.57/1.02  --sat_epr_types                         true
% 2.57/1.02  --sat_non_cyclic_types                  false
% 2.57/1.02  --sat_finite_models                     false
% 2.57/1.02  --sat_fm_lemmas                         false
% 2.57/1.02  --sat_fm_prep                           false
% 2.57/1.02  --sat_fm_uc_incr                        true
% 2.57/1.02  --sat_out_model                         small
% 2.57/1.02  --sat_out_clauses                       false
% 2.57/1.02  
% 2.57/1.02  ------ QBF Options
% 2.57/1.02  
% 2.57/1.02  --qbf_mode                              false
% 2.57/1.02  --qbf_elim_univ                         false
% 2.57/1.02  --qbf_dom_inst                          none
% 2.57/1.02  --qbf_dom_pre_inst                      false
% 2.57/1.02  --qbf_sk_in                             false
% 2.57/1.02  --qbf_pred_elim                         true
% 2.57/1.02  --qbf_split                             512
% 2.57/1.02  
% 2.57/1.02  ------ BMC1 Options
% 2.57/1.02  
% 2.57/1.02  --bmc1_incremental                      false
% 2.57/1.02  --bmc1_axioms                           reachable_all
% 2.57/1.02  --bmc1_min_bound                        0
% 2.57/1.02  --bmc1_max_bound                        -1
% 2.57/1.02  --bmc1_max_bound_default                -1
% 2.57/1.02  --bmc1_symbol_reachability              true
% 2.57/1.02  --bmc1_property_lemmas                  false
% 2.57/1.02  --bmc1_k_induction                      false
% 2.57/1.02  --bmc1_non_equiv_states                 false
% 2.57/1.02  --bmc1_deadlock                         false
% 2.57/1.02  --bmc1_ucm                              false
% 2.57/1.02  --bmc1_add_unsat_core                   none
% 2.57/1.02  --bmc1_unsat_core_children              false
% 2.57/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/1.02  --bmc1_out_stat                         full
% 2.57/1.02  --bmc1_ground_init                      false
% 2.57/1.02  --bmc1_pre_inst_next_state              false
% 2.57/1.02  --bmc1_pre_inst_state                   false
% 2.57/1.02  --bmc1_pre_inst_reach_state             false
% 2.57/1.02  --bmc1_out_unsat_core                   false
% 2.57/1.02  --bmc1_aig_witness_out                  false
% 2.57/1.02  --bmc1_verbose                          false
% 2.57/1.02  --bmc1_dump_clauses_tptp                false
% 2.57/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.57/1.02  --bmc1_dump_file                        -
% 2.57/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.57/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.57/1.02  --bmc1_ucm_extend_mode                  1
% 2.57/1.02  --bmc1_ucm_init_mode                    2
% 2.57/1.02  --bmc1_ucm_cone_mode                    none
% 2.57/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.57/1.02  --bmc1_ucm_relax_model                  4
% 2.57/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.57/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/1.02  --bmc1_ucm_layered_model                none
% 2.57/1.02  --bmc1_ucm_max_lemma_size               10
% 2.57/1.02  
% 2.57/1.02  ------ AIG Options
% 2.57/1.02  
% 2.57/1.02  --aig_mode                              false
% 2.57/1.02  
% 2.57/1.02  ------ Instantiation Options
% 2.57/1.02  
% 2.57/1.02  --instantiation_flag                    true
% 2.57/1.02  --inst_sos_flag                         false
% 2.57/1.02  --inst_sos_phase                        true
% 2.57/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/1.02  --inst_lit_sel_side                     num_symb
% 2.57/1.02  --inst_solver_per_active                1400
% 2.57/1.02  --inst_solver_calls_frac                1.
% 2.57/1.02  --inst_passive_queue_type               priority_queues
% 2.57/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/1.02  --inst_passive_queues_freq              [25;2]
% 2.57/1.02  --inst_dismatching                      true
% 2.57/1.02  --inst_eager_unprocessed_to_passive     true
% 2.57/1.02  --inst_prop_sim_given                   true
% 2.57/1.02  --inst_prop_sim_new                     false
% 2.57/1.02  --inst_subs_new                         false
% 2.57/1.02  --inst_eq_res_simp                      false
% 2.57/1.02  --inst_subs_given                       false
% 2.57/1.02  --inst_orphan_elimination               true
% 2.57/1.02  --inst_learning_loop_flag               true
% 2.57/1.02  --inst_learning_start                   3000
% 2.57/1.02  --inst_learning_factor                  2
% 2.57/1.02  --inst_start_prop_sim_after_learn       3
% 2.57/1.02  --inst_sel_renew                        solver
% 2.57/1.02  --inst_lit_activity_flag                true
% 2.57/1.02  --inst_restr_to_given                   false
% 2.57/1.02  --inst_activity_threshold               500
% 2.57/1.02  --inst_out_proof                        true
% 2.57/1.02  
% 2.57/1.02  ------ Resolution Options
% 2.57/1.02  
% 2.57/1.02  --resolution_flag                       true
% 2.57/1.02  --res_lit_sel                           adaptive
% 2.57/1.02  --res_lit_sel_side                      none
% 2.57/1.02  --res_ordering                          kbo
% 2.57/1.02  --res_to_prop_solver                    active
% 2.57/1.02  --res_prop_simpl_new                    false
% 2.57/1.02  --res_prop_simpl_given                  true
% 2.57/1.02  --res_passive_queue_type                priority_queues
% 2.57/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/1.02  --res_passive_queues_freq               [15;5]
% 2.57/1.02  --res_forward_subs                      full
% 2.57/1.02  --res_backward_subs                     full
% 2.57/1.02  --res_forward_subs_resolution           true
% 2.57/1.02  --res_backward_subs_resolution          true
% 2.57/1.02  --res_orphan_elimination                true
% 2.57/1.02  --res_time_limit                        2.
% 2.57/1.02  --res_out_proof                         true
% 2.57/1.02  
% 2.57/1.02  ------ Superposition Options
% 2.57/1.02  
% 2.57/1.02  --superposition_flag                    true
% 2.57/1.02  --sup_passive_queue_type                priority_queues
% 2.57/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.57/1.02  --demod_completeness_check              fast
% 2.57/1.02  --demod_use_ground                      true
% 2.57/1.02  --sup_to_prop_solver                    passive
% 2.57/1.02  --sup_prop_simpl_new                    true
% 2.57/1.02  --sup_prop_simpl_given                  true
% 2.57/1.02  --sup_fun_splitting                     false
% 2.57/1.02  --sup_smt_interval                      50000
% 2.57/1.02  
% 2.57/1.02  ------ Superposition Simplification Setup
% 2.57/1.02  
% 2.57/1.02  --sup_indices_passive                   []
% 2.57/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.02  --sup_full_bw                           [BwDemod]
% 2.57/1.02  --sup_immed_triv                        [TrivRules]
% 2.57/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.02  --sup_immed_bw_main                     []
% 2.57/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.02  
% 2.57/1.02  ------ Combination Options
% 2.57/1.02  
% 2.57/1.02  --comb_res_mult                         3
% 2.57/1.02  --comb_sup_mult                         2
% 2.57/1.02  --comb_inst_mult                        10
% 2.57/1.02  
% 2.57/1.02  ------ Debug Options
% 2.57/1.02  
% 2.57/1.02  --dbg_backtrace                         false
% 2.57/1.02  --dbg_dump_prop_clauses                 false
% 2.57/1.02  --dbg_dump_prop_clauses_file            -
% 2.57/1.02  --dbg_out_stat                          false
% 2.57/1.02  ------ Parsing...
% 2.57/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.57/1.02  
% 2.57/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.57/1.02  
% 2.57/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.57/1.02  
% 2.57/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.57/1.02  ------ Proving...
% 2.57/1.02  ------ Problem Properties 
% 2.57/1.02  
% 2.57/1.02  
% 2.57/1.02  clauses                                 27
% 2.57/1.02  conjectures                             3
% 2.57/1.02  EPR                                     1
% 2.57/1.02  Horn                                    26
% 2.57/1.02  unary                                   14
% 2.57/1.02  binary                                  8
% 2.57/1.02  lits                                    51
% 2.57/1.02  lits eq                                 21
% 2.57/1.02  fd_pure                                 0
% 2.57/1.02  fd_pseudo                               0
% 2.57/1.02  fd_cond                                 2
% 2.57/1.02  fd_pseudo_cond                          1
% 2.57/1.02  AC symbols                              0
% 2.57/1.02  
% 2.57/1.02  ------ Schedule dynamic 5 is on 
% 2.57/1.02  
% 2.57/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.57/1.02  
% 2.57/1.02  
% 2.57/1.02  ------ 
% 2.57/1.02  Current options:
% 2.57/1.02  ------ 
% 2.57/1.02  
% 2.57/1.02  ------ Input Options
% 2.57/1.02  
% 2.57/1.02  --out_options                           all
% 2.57/1.02  --tptp_safe_out                         true
% 2.57/1.02  --problem_path                          ""
% 2.57/1.02  --include_path                          ""
% 2.57/1.02  --clausifier                            res/vclausify_rel
% 2.57/1.02  --clausifier_options                    --mode clausify
% 2.57/1.02  --stdin                                 false
% 2.57/1.02  --stats_out                             all
% 2.57/1.02  
% 2.57/1.02  ------ General Options
% 2.57/1.02  
% 2.57/1.02  --fof                                   false
% 2.57/1.02  --time_out_real                         305.
% 2.57/1.02  --time_out_virtual                      -1.
% 2.57/1.02  --symbol_type_check                     false
% 2.57/1.02  --clausify_out                          false
% 2.57/1.02  --sig_cnt_out                           false
% 2.57/1.02  --trig_cnt_out                          false
% 2.57/1.02  --trig_cnt_out_tolerance                1.
% 2.57/1.02  --trig_cnt_out_sk_spl                   false
% 2.57/1.02  --abstr_cl_out                          false
% 2.57/1.02  
% 2.57/1.02  ------ Global Options
% 2.57/1.02  
% 2.57/1.02  --schedule                              default
% 2.57/1.02  --add_important_lit                     false
% 2.57/1.02  --prop_solver_per_cl                    1000
% 2.57/1.02  --min_unsat_core                        false
% 2.57/1.02  --soft_assumptions                      false
% 2.57/1.02  --soft_lemma_size                       3
% 2.57/1.02  --prop_impl_unit_size                   0
% 2.57/1.02  --prop_impl_unit                        []
% 2.57/1.02  --share_sel_clauses                     true
% 2.57/1.02  --reset_solvers                         false
% 2.57/1.02  --bc_imp_inh                            [conj_cone]
% 2.57/1.02  --conj_cone_tolerance                   3.
% 2.57/1.02  --extra_neg_conj                        none
% 2.57/1.02  --large_theory_mode                     true
% 2.57/1.02  --prolific_symb_bound                   200
% 2.57/1.02  --lt_threshold                          2000
% 2.57/1.02  --clause_weak_htbl                      true
% 2.57/1.02  --gc_record_bc_elim                     false
% 2.57/1.02  
% 2.57/1.02  ------ Preprocessing Options
% 2.57/1.02  
% 2.57/1.02  --preprocessing_flag                    true
% 2.57/1.02  --time_out_prep_mult                    0.1
% 2.57/1.02  --splitting_mode                        input
% 2.57/1.02  --splitting_grd                         true
% 2.57/1.02  --splitting_cvd                         false
% 2.57/1.02  --splitting_cvd_svl                     false
% 2.57/1.02  --splitting_nvd                         32
% 2.57/1.02  --sub_typing                            true
% 2.57/1.02  --prep_gs_sim                           true
% 2.57/1.02  --prep_unflatten                        true
% 2.57/1.02  --prep_res_sim                          true
% 2.57/1.02  --prep_upred                            true
% 2.57/1.02  --prep_sem_filter                       exhaustive
% 2.57/1.02  --prep_sem_filter_out                   false
% 2.57/1.02  --pred_elim                             true
% 2.57/1.02  --res_sim_input                         true
% 2.57/1.02  --eq_ax_congr_red                       true
% 2.57/1.02  --pure_diseq_elim                       true
% 2.57/1.02  --brand_transform                       false
% 2.57/1.02  --non_eq_to_eq                          false
% 2.57/1.02  --prep_def_merge                        true
% 2.57/1.02  --prep_def_merge_prop_impl              false
% 2.57/1.02  --prep_def_merge_mbd                    true
% 2.57/1.02  --prep_def_merge_tr_red                 false
% 2.57/1.02  --prep_def_merge_tr_cl                  false
% 2.57/1.02  --smt_preprocessing                     true
% 2.57/1.02  --smt_ac_axioms                         fast
% 2.57/1.02  --preprocessed_out                      false
% 2.57/1.02  --preprocessed_stats                    false
% 2.57/1.02  
% 2.57/1.02  ------ Abstraction refinement Options
% 2.57/1.02  
% 2.57/1.02  --abstr_ref                             []
% 2.57/1.02  --abstr_ref_prep                        false
% 2.57/1.02  --abstr_ref_until_sat                   false
% 2.57/1.02  --abstr_ref_sig_restrict                funpre
% 2.57/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.57/1.02  --abstr_ref_under                       []
% 2.57/1.02  
% 2.57/1.02  ------ SAT Options
% 2.57/1.02  
% 2.57/1.02  --sat_mode                              false
% 2.57/1.02  --sat_fm_restart_options                ""
% 2.57/1.02  --sat_gr_def                            false
% 2.57/1.02  --sat_epr_types                         true
% 2.57/1.02  --sat_non_cyclic_types                  false
% 2.57/1.02  --sat_finite_models                     false
% 2.57/1.02  --sat_fm_lemmas                         false
% 2.57/1.02  --sat_fm_prep                           false
% 2.57/1.02  --sat_fm_uc_incr                        true
% 2.57/1.02  --sat_out_model                         small
% 2.57/1.02  --sat_out_clauses                       false
% 2.57/1.02  
% 2.57/1.02  ------ QBF Options
% 2.57/1.02  
% 2.57/1.02  --qbf_mode                              false
% 2.57/1.02  --qbf_elim_univ                         false
% 2.57/1.02  --qbf_dom_inst                          none
% 2.57/1.02  --qbf_dom_pre_inst                      false
% 2.57/1.02  --qbf_sk_in                             false
% 2.57/1.02  --qbf_pred_elim                         true
% 2.57/1.02  --qbf_split                             512
% 2.57/1.02  
% 2.57/1.02  ------ BMC1 Options
% 2.57/1.02  
% 2.57/1.02  --bmc1_incremental                      false
% 2.57/1.02  --bmc1_axioms                           reachable_all
% 2.57/1.02  --bmc1_min_bound                        0
% 2.57/1.02  --bmc1_max_bound                        -1
% 2.57/1.02  --bmc1_max_bound_default                -1
% 2.57/1.02  --bmc1_symbol_reachability              true
% 2.57/1.02  --bmc1_property_lemmas                  false
% 2.57/1.02  --bmc1_k_induction                      false
% 2.57/1.02  --bmc1_non_equiv_states                 false
% 2.57/1.02  --bmc1_deadlock                         false
% 2.57/1.02  --bmc1_ucm                              false
% 2.57/1.02  --bmc1_add_unsat_core                   none
% 2.57/1.02  --bmc1_unsat_core_children              false
% 2.57/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.57/1.02  --bmc1_out_stat                         full
% 2.57/1.02  --bmc1_ground_init                      false
% 2.57/1.02  --bmc1_pre_inst_next_state              false
% 2.57/1.02  --bmc1_pre_inst_state                   false
% 2.57/1.02  --bmc1_pre_inst_reach_state             false
% 2.57/1.02  --bmc1_out_unsat_core                   false
% 2.57/1.02  --bmc1_aig_witness_out                  false
% 2.57/1.02  --bmc1_verbose                          false
% 2.57/1.02  --bmc1_dump_clauses_tptp                false
% 2.57/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.57/1.02  --bmc1_dump_file                        -
% 2.57/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.57/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.57/1.02  --bmc1_ucm_extend_mode                  1
% 2.57/1.02  --bmc1_ucm_init_mode                    2
% 2.57/1.02  --bmc1_ucm_cone_mode                    none
% 2.57/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.57/1.02  --bmc1_ucm_relax_model                  4
% 2.57/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.57/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.57/1.02  --bmc1_ucm_layered_model                none
% 2.57/1.02  --bmc1_ucm_max_lemma_size               10
% 2.57/1.02  
% 2.57/1.02  ------ AIG Options
% 2.57/1.02  
% 2.57/1.02  --aig_mode                              false
% 2.57/1.02  
% 2.57/1.02  ------ Instantiation Options
% 2.57/1.02  
% 2.57/1.02  --instantiation_flag                    true
% 2.57/1.02  --inst_sos_flag                         false
% 2.57/1.02  --inst_sos_phase                        true
% 2.57/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.57/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.57/1.02  --inst_lit_sel_side                     none
% 2.57/1.02  --inst_solver_per_active                1400
% 2.57/1.02  --inst_solver_calls_frac                1.
% 2.57/1.02  --inst_passive_queue_type               priority_queues
% 2.57/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.57/1.02  --inst_passive_queues_freq              [25;2]
% 2.57/1.02  --inst_dismatching                      true
% 2.57/1.02  --inst_eager_unprocessed_to_passive     true
% 2.57/1.02  --inst_prop_sim_given                   true
% 2.57/1.02  --inst_prop_sim_new                     false
% 2.57/1.02  --inst_subs_new                         false
% 2.57/1.02  --inst_eq_res_simp                      false
% 2.57/1.02  --inst_subs_given                       false
% 2.57/1.02  --inst_orphan_elimination               true
% 2.57/1.02  --inst_learning_loop_flag               true
% 2.57/1.02  --inst_learning_start                   3000
% 2.57/1.02  --inst_learning_factor                  2
% 2.57/1.02  --inst_start_prop_sim_after_learn       3
% 2.57/1.02  --inst_sel_renew                        solver
% 2.57/1.02  --inst_lit_activity_flag                true
% 2.57/1.02  --inst_restr_to_given                   false
% 2.57/1.02  --inst_activity_threshold               500
% 2.57/1.02  --inst_out_proof                        true
% 2.57/1.02  
% 2.57/1.02  ------ Resolution Options
% 2.57/1.02  
% 2.57/1.02  --resolution_flag                       false
% 2.57/1.02  --res_lit_sel                           adaptive
% 2.57/1.02  --res_lit_sel_side                      none
% 2.57/1.02  --res_ordering                          kbo
% 2.57/1.02  --res_to_prop_solver                    active
% 2.57/1.02  --res_prop_simpl_new                    false
% 2.57/1.02  --res_prop_simpl_given                  true
% 2.57/1.02  --res_passive_queue_type                priority_queues
% 2.57/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.57/1.02  --res_passive_queues_freq               [15;5]
% 2.57/1.02  --res_forward_subs                      full
% 2.57/1.02  --res_backward_subs                     full
% 2.57/1.02  --res_forward_subs_resolution           true
% 2.57/1.02  --res_backward_subs_resolution          true
% 2.57/1.02  --res_orphan_elimination                true
% 2.57/1.02  --res_time_limit                        2.
% 2.57/1.02  --res_out_proof                         true
% 2.57/1.02  
% 2.57/1.02  ------ Superposition Options
% 2.57/1.02  
% 2.57/1.02  --superposition_flag                    true
% 2.57/1.02  --sup_passive_queue_type                priority_queues
% 2.57/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.57/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.57/1.02  --demod_completeness_check              fast
% 2.57/1.02  --demod_use_ground                      true
% 2.57/1.02  --sup_to_prop_solver                    passive
% 2.57/1.02  --sup_prop_simpl_new                    true
% 2.57/1.02  --sup_prop_simpl_given                  true
% 2.57/1.02  --sup_fun_splitting                     false
% 2.57/1.02  --sup_smt_interval                      50000
% 2.57/1.02  
% 2.57/1.02  ------ Superposition Simplification Setup
% 2.57/1.02  
% 2.57/1.02  --sup_indices_passive                   []
% 2.57/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.57/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.57/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.02  --sup_full_bw                           [BwDemod]
% 2.57/1.02  --sup_immed_triv                        [TrivRules]
% 2.57/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.57/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.02  --sup_immed_bw_main                     []
% 2.57/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.57/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.57/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.57/1.02  
% 2.57/1.02  ------ Combination Options
% 2.57/1.02  
% 2.57/1.02  --comb_res_mult                         3
% 2.57/1.02  --comb_sup_mult                         2
% 2.57/1.02  --comb_inst_mult                        10
% 2.57/1.02  
% 2.57/1.02  ------ Debug Options
% 2.57/1.02  
% 2.57/1.02  --dbg_backtrace                         false
% 2.57/1.02  --dbg_dump_prop_clauses                 false
% 2.57/1.02  --dbg_dump_prop_clauses_file            -
% 2.57/1.02  --dbg_out_stat                          false
% 2.57/1.02  
% 2.57/1.02  
% 2.57/1.02  
% 2.57/1.02  
% 2.57/1.02  ------ Proving...
% 2.57/1.02  
% 2.57/1.02  
% 2.57/1.02  % SZS status Theorem for theBenchmark.p
% 2.57/1.02  
% 2.57/1.02   Resolution empty clause
% 2.57/1.02  
% 2.57/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.57/1.02  
% 2.57/1.02  fof(f18,conjecture,(
% 2.57/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f19,negated_conjecture,(
% 2.57/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.57/1.02    inference(negated_conjecture,[],[f18])).
% 2.57/1.02  
% 2.57/1.02  fof(f20,plain,(
% 2.57/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.57/1.02    inference(pure_predicate_removal,[],[f19])).
% 2.57/1.02  
% 2.57/1.02  fof(f36,plain,(
% 2.57/1.02    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.57/1.02    inference(ennf_transformation,[],[f20])).
% 2.57/1.02  
% 2.57/1.02  fof(f37,plain,(
% 2.57/1.02    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.57/1.02    inference(flattening,[],[f36])).
% 2.57/1.02  
% 2.57/1.02  fof(f42,plain,(
% 2.57/1.02    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.57/1.02    introduced(choice_axiom,[])).
% 2.57/1.02  
% 2.57/1.02  fof(f43,plain,(
% 2.57/1.02    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.57/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f42])).
% 2.57/1.02  
% 2.57/1.02  fof(f73,plain,(
% 2.57/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.57/1.02    inference(cnf_transformation,[],[f43])).
% 2.57/1.02  
% 2.57/1.02  fof(f1,axiom,(
% 2.57/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f44,plain,(
% 2.57/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.57/1.02    inference(cnf_transformation,[],[f1])).
% 2.57/1.02  
% 2.57/1.02  fof(f2,axiom,(
% 2.57/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f45,plain,(
% 2.57/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.57/1.02    inference(cnf_transformation,[],[f2])).
% 2.57/1.02  
% 2.57/1.02  fof(f3,axiom,(
% 2.57/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f46,plain,(
% 2.57/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.57/1.02    inference(cnf_transformation,[],[f3])).
% 2.57/1.02  
% 2.57/1.02  fof(f76,plain,(
% 2.57/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 2.57/1.02    inference(definition_unfolding,[],[f45,f46])).
% 2.57/1.02  
% 2.57/1.02  fof(f77,plain,(
% 2.57/1.02    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.57/1.02    inference(definition_unfolding,[],[f44,f76])).
% 2.57/1.02  
% 2.57/1.02  fof(f89,plain,(
% 2.57/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.57/1.02    inference(definition_unfolding,[],[f73,f77])).
% 2.57/1.02  
% 2.57/1.02  fof(f16,axiom,(
% 2.57/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f21,plain,(
% 2.57/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.57/1.02    inference(pure_predicate_removal,[],[f16])).
% 2.57/1.02  
% 2.57/1.02  fof(f34,plain,(
% 2.57/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/1.02    inference(ennf_transformation,[],[f21])).
% 2.57/1.02  
% 2.57/1.02  fof(f70,plain,(
% 2.57/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/1.02    inference(cnf_transformation,[],[f34])).
% 2.57/1.02  
% 2.57/1.02  fof(f8,axiom,(
% 2.57/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f24,plain,(
% 2.57/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.57/1.02    inference(ennf_transformation,[],[f8])).
% 2.57/1.02  
% 2.57/1.02  fof(f41,plain,(
% 2.57/1.02    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.57/1.02    inference(nnf_transformation,[],[f24])).
% 2.57/1.02  
% 2.57/1.02  fof(f59,plain,(
% 2.57/1.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.57/1.02    inference(cnf_transformation,[],[f41])).
% 2.57/1.02  
% 2.57/1.02  fof(f15,axiom,(
% 2.57/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f33,plain,(
% 2.57/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/1.02    inference(ennf_transformation,[],[f15])).
% 2.57/1.02  
% 2.57/1.02  fof(f69,plain,(
% 2.57/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/1.02    inference(cnf_transformation,[],[f33])).
% 2.57/1.02  
% 2.57/1.02  fof(f4,axiom,(
% 2.57/1.02    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f23,plain,(
% 2.57/1.02    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 2.57/1.02    inference(ennf_transformation,[],[f4])).
% 2.57/1.02  
% 2.57/1.02  fof(f38,plain,(
% 2.57/1.02    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.57/1.02    inference(nnf_transformation,[],[f23])).
% 2.57/1.02  
% 2.57/1.02  fof(f39,plain,(
% 2.57/1.02    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 2.57/1.02    inference(flattening,[],[f38])).
% 2.57/1.02  
% 2.57/1.02  fof(f47,plain,(
% 2.57/1.02    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 2.57/1.02    inference(cnf_transformation,[],[f39])).
% 2.57/1.02  
% 2.57/1.02  fof(f86,plain,(
% 2.57/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 2.57/1.02    inference(definition_unfolding,[],[f47,f46,f76,f76,f76,f77,f77,f77,f46])).
% 2.57/1.02  
% 2.57/1.02  fof(f75,plain,(
% 2.57/1.02    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.57/1.02    inference(cnf_transformation,[],[f43])).
% 2.57/1.02  
% 2.57/1.02  fof(f88,plain,(
% 2.57/1.02    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.57/1.02    inference(definition_unfolding,[],[f75,f77,f77])).
% 2.57/1.02  
% 2.57/1.02  fof(f17,axiom,(
% 2.57/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f35,plain,(
% 2.57/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.57/1.02    inference(ennf_transformation,[],[f17])).
% 2.57/1.02  
% 2.57/1.02  fof(f71,plain,(
% 2.57/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.57/1.02    inference(cnf_transformation,[],[f35])).
% 2.57/1.02  
% 2.57/1.02  fof(f9,axiom,(
% 2.57/1.02    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f25,plain,(
% 2.57/1.02    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.57/1.02    inference(ennf_transformation,[],[f9])).
% 2.57/1.02  
% 2.57/1.02  fof(f61,plain,(
% 2.57/1.02    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.57/1.02    inference(cnf_transformation,[],[f25])).
% 2.57/1.02  
% 2.57/1.02  fof(f14,axiom,(
% 2.57/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f31,plain,(
% 2.57/1.02    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.57/1.02    inference(ennf_transformation,[],[f14])).
% 2.57/1.02  
% 2.57/1.02  fof(f32,plain,(
% 2.57/1.02    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.57/1.02    inference(flattening,[],[f31])).
% 2.57/1.02  
% 2.57/1.02  fof(f68,plain,(
% 2.57/1.02    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.57/1.02    inference(cnf_transformation,[],[f32])).
% 2.57/1.02  
% 2.57/1.02  fof(f87,plain,(
% 2.57/1.02    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.57/1.02    inference(definition_unfolding,[],[f68,f77,f77])).
% 2.57/1.02  
% 2.57/1.02  fof(f72,plain,(
% 2.57/1.02    v1_funct_1(sK3)),
% 2.57/1.02    inference(cnf_transformation,[],[f43])).
% 2.57/1.02  
% 2.57/1.02  fof(f13,axiom,(
% 2.57/1.02    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f29,plain,(
% 2.57/1.02    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.57/1.02    inference(ennf_transformation,[],[f13])).
% 2.57/1.02  
% 2.57/1.02  fof(f30,plain,(
% 2.57/1.02    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.57/1.02    inference(flattening,[],[f29])).
% 2.57/1.02  
% 2.57/1.02  fof(f66,plain,(
% 2.57/1.02    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.57/1.02    inference(cnf_transformation,[],[f30])).
% 2.57/1.02  
% 2.57/1.02  fof(f5,axiom,(
% 2.57/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f56,plain,(
% 2.57/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.57/1.02    inference(cnf_transformation,[],[f5])).
% 2.57/1.02  
% 2.57/1.02  fof(f10,axiom,(
% 2.57/1.02    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f26,plain,(
% 2.57/1.02    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.57/1.02    inference(ennf_transformation,[],[f10])).
% 2.57/1.02  
% 2.57/1.02  fof(f62,plain,(
% 2.57/1.02    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.57/1.02    inference(cnf_transformation,[],[f26])).
% 2.57/1.02  
% 2.57/1.02  fof(f12,axiom,(
% 2.57/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f65,plain,(
% 2.57/1.02    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.57/1.02    inference(cnf_transformation,[],[f12])).
% 2.57/1.02  
% 2.57/1.02  fof(f11,axiom,(
% 2.57/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f27,plain,(
% 2.57/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.57/1.02    inference(ennf_transformation,[],[f11])).
% 2.57/1.02  
% 2.57/1.02  fof(f28,plain,(
% 2.57/1.02    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.57/1.02    inference(flattening,[],[f27])).
% 2.57/1.02  
% 2.57/1.02  fof(f63,plain,(
% 2.57/1.02    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.57/1.02    inference(cnf_transformation,[],[f28])).
% 2.57/1.02  
% 2.57/1.02  fof(f6,axiom,(
% 2.57/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.57/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.57/1.02  
% 2.57/1.02  fof(f40,plain,(
% 2.57/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.57/1.02    inference(nnf_transformation,[],[f6])).
% 2.57/1.02  
% 2.57/1.02  fof(f57,plain,(
% 2.57/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.57/1.02    inference(cnf_transformation,[],[f40])).
% 2.57/1.02  
% 2.57/1.02  cnf(c_27,negated_conjecture,
% 2.57/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 2.57/1.02      inference(cnf_transformation,[],[f89]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3204,plain,
% 2.57/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_23,plain,
% 2.57/1.02      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.57/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_13,plain,
% 2.57/1.02      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.57/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_377,plain,
% 2.57/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 2.57/1.02      | ~ v1_relat_1(X0) ),
% 2.57/1.02      inference(resolution,[status(thm)],[c_23,c_13]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_22,plain,
% 2.57/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.57/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_381,plain,
% 2.57/1.02      ( r1_tarski(k1_relat_1(X0),X1)
% 2.57/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.57/1.02      inference(global_propositional_subsumption,[status(thm)],[c_377,c_22]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_382,plain,
% 2.57/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.02      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.57/1.02      inference(renaming,[status(thm)],[c_381]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3201,plain,
% 2.57/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.57/1.02      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4029,plain,
% 2.57/1.02      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_3204,c_3201]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_8,plain,
% 2.57/1.02      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 2.57/1.02      | k2_enumset1(X1,X1,X2,X3) = X0
% 2.57/1.02      | k2_enumset1(X1,X1,X1,X3) = X0
% 2.57/1.02      | k2_enumset1(X2,X2,X2,X3) = X0
% 2.57/1.02      | k2_enumset1(X1,X1,X1,X2) = X0
% 2.57/1.02      | k2_enumset1(X3,X3,X3,X3) = X0
% 2.57/1.02      | k2_enumset1(X2,X2,X2,X2) = X0
% 2.57/1.02      | k2_enumset1(X1,X1,X1,X1) = X0
% 2.57/1.02      | k1_xboole_0 = X0 ),
% 2.57/1.02      inference(cnf_transformation,[],[f86]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3215,plain,
% 2.57/1.02      ( k2_enumset1(X0,X0,X1,X2) = X3
% 2.57/1.02      | k2_enumset1(X0,X0,X0,X2) = X3
% 2.57/1.02      | k2_enumset1(X1,X1,X1,X2) = X3
% 2.57/1.02      | k2_enumset1(X0,X0,X0,X1) = X3
% 2.57/1.02      | k2_enumset1(X2,X2,X2,X2) = X3
% 2.57/1.02      | k2_enumset1(X1,X1,X1,X1) = X3
% 2.57/1.02      | k2_enumset1(X0,X0,X0,X0) = X3
% 2.57/1.02      | k1_xboole_0 = X3
% 2.57/1.02      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5110,plain,
% 2.57/1.02      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.57/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_4029,c_3215]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5343,plain,
% 2.57/1.02      ( k1_relat_1(sK3) = k1_xboole_0
% 2.57/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_5110,c_3204]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_25,negated_conjecture,
% 2.57/1.02      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.57/1.02      inference(cnf_transformation,[],[f88]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3400,plain,
% 2.57/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.57/1.02      | v1_relat_1(sK3) ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_22]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_24,plain,
% 2.57/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.57/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3444,plain,
% 2.57/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.57/1.02      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_24]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3476,plain,
% 2.57/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 2.57/1.02      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_3444]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2651,plain,
% 2.57/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.57/1.02      theory(equality) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3427,plain,
% 2.57/1.02      ( ~ r1_tarski(X0,X1)
% 2.57/1.02      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.57/1.02      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 2.57/1.02      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_2651]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3475,plain,
% 2.57/1.02      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.57/1.02      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 2.57/1.02      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.57/1.02      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_3427]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3609,plain,
% 2.57/1.02      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.57/1.02      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.57/1.02      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 2.57/1.02      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_3475]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_14,plain,
% 2.57/1.02      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.57/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3610,plain,
% 2.57/1.02      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_21,plain,
% 2.57/1.02      ( ~ v1_funct_1(X0)
% 2.57/1.02      | ~ v1_relat_1(X0)
% 2.57/1.02      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.57/1.02      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.57/1.02      inference(cnf_transformation,[],[f87]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_28,negated_conjecture,
% 2.57/1.02      ( v1_funct_1(sK3) ),
% 2.57/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_341,plain,
% 2.57/1.02      ( ~ v1_relat_1(X0)
% 2.57/1.02      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 2.57/1.02      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.57/1.02      | sK3 != X0 ),
% 2.57/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_342,plain,
% 2.57/1.02      ( ~ v1_relat_1(sK3)
% 2.57/1.02      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.57/1.02      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.57/1.02      inference(unflattening,[status(thm)],[c_341]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3203,plain,
% 2.57/1.02      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.57/1.02      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.57/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_30,plain,
% 2.57/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_343,plain,
% 2.57/1.02      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.57/1.02      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.57/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3401,plain,
% 2.57/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 2.57/1.02      | v1_relat_1(sK3) = iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_3400]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3406,plain,
% 2.57/1.02      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.57/1.02      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 2.57/1.02      inference(global_propositional_subsumption,
% 2.57/1.02                [status(thm)],
% 2.57/1.02                [c_3203,c_30,c_343,c_3401]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3407,plain,
% 2.57/1.02      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.57/1.02      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.57/1.02      inference(renaming,[status(thm)],[c_3406]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5335,plain,
% 2.57/1.02      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.57/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_5110,c_3407]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5511,plain,
% 2.57/1.02      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.57/1.02      inference(global_propositional_subsumption,
% 2.57/1.02                [status(thm)],
% 2.57/1.02                [c_5343,c_27,c_25,c_3400,c_3476,c_3609,c_3610,c_5335]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_20,plain,
% 2.57/1.02      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 2.57/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3208,plain,
% 2.57/1.02      ( k1_relat_1(X0) != k1_xboole_0
% 2.57/1.02      | k1_xboole_0 = X0
% 2.57/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5523,plain,
% 2.57/1.02      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_5511,c_3208]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2648,plain,( X0 = X0 ),theory(equality) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3956,plain,
% 2.57/1.02      ( sK3 = sK3 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_2648]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_2649,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3957,plain,
% 2.57/1.02      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_2649]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4387,plain,
% 2.57/1.02      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_3957]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4388,plain,
% 2.57/1.02      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_4387]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4819,plain,
% 2.57/1.02      ( ~ v1_relat_1(sK3)
% 2.57/1.02      | k1_relat_1(sK3) != k1_xboole_0
% 2.57/1.02      | k1_xboole_0 = sK3 ),
% 2.57/1.02      inference(instantiation,[status(thm)],[c_20]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5540,plain,
% 2.57/1.02      ( sK3 = k1_xboole_0 ),
% 2.57/1.02      inference(global_propositional_subsumption,
% 2.57/1.02                [status(thm)],
% 2.57/1.02                [c_5523,c_27,c_25,c_3400,c_3476,c_3609,c_3610,c_3956,c_4388,
% 2.57/1.02                 c_4819,c_5335]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3206,plain,
% 2.57/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.57/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4980,plain,
% 2.57/1.02      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_3204,c_3206]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3205,plain,
% 2.57/1.02      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5195,plain,
% 2.57/1.02      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.57/1.02      inference(demodulation,[status(thm)],[c_4980,c_3205]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5544,plain,
% 2.57/1.02      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.57/1.02      inference(demodulation,[status(thm)],[c_5540,c_5195]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_9,plain,
% 2.57/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.57/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3214,plain,
% 2.57/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3207,plain,
% 2.57/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.57/1.02      | v1_relat_1(X0) = iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4045,plain,
% 2.57/1.02      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_3214,c_3207]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_15,plain,
% 2.57/1.02      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.57/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3210,plain,
% 2.57/1.02      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.57/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4477,plain,
% 2.57/1.02      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_4045,c_3210]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_17,plain,
% 2.57/1.02      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.57/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_16,plain,
% 2.57/1.02      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.57/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_360,plain,
% 2.57/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.02      | ~ v1_relat_1(X0)
% 2.57/1.02      | k7_relat_1(X0,X1) = X0 ),
% 2.57/1.02      inference(resolution,[status(thm)],[c_23,c_16]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_364,plain,
% 2.57/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.57/1.02      | k7_relat_1(X0,X1) = X0 ),
% 2.57/1.02      inference(global_propositional_subsumption,
% 2.57/1.02                [status(thm)],
% 2.57/1.02                [c_360,c_23,c_22,c_16]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3202,plain,
% 2.57/1.02      ( k7_relat_1(X0,X1) = X0
% 2.57/1.02      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_364]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4482,plain,
% 2.57/1.02      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_3214,c_3202]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_4777,plain,
% 2.57/1.02      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.57/1.02      inference(light_normalisation,[status(thm)],[c_4477,c_17,c_4482]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5569,plain,
% 2.57/1.02      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.57/1.02      inference(demodulation,[status(thm)],[c_5544,c_4777]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_11,plain,
% 2.57/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.57/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3212,plain,
% 2.57/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.57/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 2.57/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_3496,plain,
% 2.57/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.57/1.02      inference(superposition,[status(thm)],[c_3214,c_3212]) ).
% 2.57/1.02  
% 2.57/1.02  cnf(c_5668,plain,
% 2.57/1.02      ( $false ),
% 2.57/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_5569,c_3496]) ).
% 2.57/1.02  
% 2.57/1.02  
% 2.57/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.57/1.02  
% 2.57/1.02  ------                               Statistics
% 2.57/1.02  
% 2.57/1.02  ------ General
% 2.57/1.02  
% 2.57/1.02  abstr_ref_over_cycles:                  0
% 2.57/1.02  abstr_ref_under_cycles:                 0
% 2.57/1.02  gc_basic_clause_elim:                   0
% 2.57/1.02  forced_gc_time:                         0
% 2.57/1.02  parsing_time:                           0.009
% 2.57/1.02  unif_index_cands_time:                  0.
% 2.57/1.02  unif_index_add_time:                    0.
% 2.57/1.02  orderings_time:                         0.
% 2.57/1.02  out_proof_time:                         0.011
% 2.57/1.02  total_time:                             0.183
% 2.57/1.02  num_of_symbols:                         50
% 2.57/1.02  num_of_terms:                           3583
% 2.57/1.02  
% 2.57/1.02  ------ Preprocessing
% 2.57/1.02  
% 2.57/1.02  num_of_splits:                          0
% 2.57/1.02  num_of_split_atoms:                     0
% 2.57/1.02  num_of_reused_defs:                     0
% 2.57/1.02  num_eq_ax_congr_red:                    15
% 2.57/1.02  num_of_sem_filtered_clauses:            1
% 2.57/1.02  num_of_subtypes:                        0
% 2.57/1.02  monotx_restored_types:                  0
% 2.57/1.02  sat_num_of_epr_types:                   0
% 2.57/1.02  sat_num_of_non_cyclic_types:            0
% 2.57/1.02  sat_guarded_non_collapsed_types:        0
% 2.57/1.02  num_pure_diseq_elim:                    0
% 2.57/1.02  simp_replaced_by:                       0
% 2.57/1.02  res_preprocessed:                       135
% 2.57/1.02  prep_upred:                             0
% 2.57/1.02  prep_unflattend:                        125
% 2.57/1.02  smt_new_axioms:                         0
% 2.57/1.02  pred_elim_cands:                        3
% 2.57/1.02  pred_elim:                              2
% 2.57/1.02  pred_elim_cl:                           2
% 2.57/1.02  pred_elim_cycles:                       8
% 2.57/1.02  merged_defs:                            8
% 2.57/1.02  merged_defs_ncl:                        0
% 2.57/1.02  bin_hyper_res:                          8
% 2.57/1.02  prep_cycles:                            4
% 2.57/1.02  pred_elim_time:                         0.038
% 2.57/1.02  splitting_time:                         0.
% 2.57/1.02  sem_filter_time:                        0.
% 2.57/1.02  monotx_time:                            0.
% 2.57/1.02  subtype_inf_time:                       0.
% 2.57/1.02  
% 2.57/1.02  ------ Problem properties
% 2.57/1.02  
% 2.57/1.02  clauses:                                27
% 2.57/1.02  conjectures:                            3
% 2.57/1.02  epr:                                    1
% 2.57/1.02  horn:                                   26
% 2.57/1.02  ground:                                 5
% 2.57/1.02  unary:                                  14
% 2.57/1.02  binary:                                 8
% 2.57/1.02  lits:                                   51
% 2.57/1.02  lits_eq:                                21
% 2.57/1.02  fd_pure:                                0
% 2.57/1.02  fd_pseudo:                              0
% 2.57/1.02  fd_cond:                                2
% 2.57/1.02  fd_pseudo_cond:                         1
% 2.57/1.02  ac_symbols:                             0
% 2.57/1.02  
% 2.57/1.02  ------ Propositional Solver
% 2.57/1.02  
% 2.57/1.02  prop_solver_calls:                      28
% 2.57/1.02  prop_fast_solver_calls:                 1107
% 2.57/1.02  smt_solver_calls:                       0
% 2.57/1.02  smt_fast_solver_calls:                  0
% 2.57/1.02  prop_num_of_clauses:                    1309
% 2.57/1.02  prop_preprocess_simplified:             5774
% 2.57/1.02  prop_fo_subsumed:                       18
% 2.57/1.02  prop_solver_time:                       0.
% 2.57/1.02  smt_solver_time:                        0.
% 2.57/1.02  smt_fast_solver_time:                   0.
% 2.57/1.02  prop_fast_solver_time:                  0.
% 2.57/1.02  prop_unsat_core_time:                   0.
% 2.57/1.02  
% 2.57/1.02  ------ QBF
% 2.57/1.02  
% 2.57/1.02  qbf_q_res:                              0
% 2.57/1.02  qbf_num_tautologies:                    0
% 2.57/1.02  qbf_prep_cycles:                        0
% 2.57/1.02  
% 2.57/1.02  ------ BMC1
% 2.57/1.02  
% 2.57/1.02  bmc1_current_bound:                     -1
% 2.57/1.02  bmc1_last_solved_bound:                 -1
% 2.57/1.02  bmc1_unsat_core_size:                   -1
% 2.57/1.02  bmc1_unsat_core_parents_size:           -1
% 2.57/1.02  bmc1_merge_next_fun:                    0
% 2.57/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.57/1.02  
% 2.57/1.02  ------ Instantiation
% 2.57/1.02  
% 2.57/1.02  inst_num_of_clauses:                    381
% 2.57/1.02  inst_num_in_passive:                    90
% 2.57/1.02  inst_num_in_active:                     245
% 2.57/1.02  inst_num_in_unprocessed:                46
% 2.57/1.02  inst_num_of_loops:                      270
% 2.57/1.02  inst_num_of_learning_restarts:          0
% 2.57/1.02  inst_num_moves_active_passive:          21
% 2.57/1.02  inst_lit_activity:                      0
% 2.57/1.02  inst_lit_activity_moves:                0
% 2.57/1.02  inst_num_tautologies:                   0
% 2.57/1.02  inst_num_prop_implied:                  0
% 2.57/1.02  inst_num_existing_simplified:           0
% 2.57/1.02  inst_num_eq_res_simplified:             0
% 2.57/1.02  inst_num_child_elim:                    0
% 2.57/1.02  inst_num_of_dismatching_blockings:      94
% 2.57/1.02  inst_num_of_non_proper_insts:           422
% 2.57/1.02  inst_num_of_duplicates:                 0
% 2.57/1.02  inst_inst_num_from_inst_to_res:         0
% 2.57/1.02  inst_dismatching_checking_time:         0.
% 2.57/1.02  
% 2.57/1.02  ------ Resolution
% 2.57/1.02  
% 2.57/1.02  res_num_of_clauses:                     0
% 2.57/1.02  res_num_in_passive:                     0
% 2.57/1.02  res_num_in_active:                      0
% 2.57/1.02  res_num_of_loops:                       139
% 2.57/1.02  res_forward_subset_subsumed:            45
% 2.57/1.02  res_backward_subset_subsumed:           2
% 2.57/1.02  res_forward_subsumed:                   4
% 2.57/1.02  res_backward_subsumed:                  0
% 2.57/1.02  res_forward_subsumption_resolution:     0
% 2.57/1.02  res_backward_subsumption_resolution:    0
% 2.57/1.02  res_clause_to_clause_subsumption:       454
% 2.57/1.02  res_orphan_elimination:                 0
% 2.57/1.02  res_tautology_del:                      57
% 2.57/1.02  res_num_eq_res_simplified:              0
% 2.57/1.02  res_num_sel_changes:                    0
% 2.57/1.02  res_moves_from_active_to_pass:          0
% 2.57/1.02  
% 2.57/1.02  ------ Superposition
% 2.57/1.02  
% 2.57/1.02  sup_time_total:                         0.
% 2.57/1.02  sup_time_generating:                    0.
% 2.57/1.02  sup_time_sim_full:                      0.
% 2.57/1.02  sup_time_sim_immed:                     0.
% 2.57/1.02  
% 2.57/1.02  sup_num_of_clauses:                     40
% 2.57/1.02  sup_num_in_active:                      35
% 2.57/1.02  sup_num_in_passive:                     5
% 2.57/1.02  sup_num_of_loops:                       53
% 2.57/1.02  sup_fw_superposition:                   40
% 2.57/1.02  sup_bw_superposition:                   33
% 2.57/1.02  sup_immediate_simplified:               21
% 2.57/1.02  sup_given_eliminated:                   0
% 2.57/1.02  comparisons_done:                       0
% 2.57/1.02  comparisons_avoided:                    0
% 2.57/1.02  
% 2.57/1.02  ------ Simplifications
% 2.57/1.02  
% 2.57/1.02  
% 2.57/1.02  sim_fw_subset_subsumed:                 1
% 2.57/1.02  sim_bw_subset_subsumed:                 7
% 2.57/1.02  sim_fw_subsumed:                        14
% 2.57/1.02  sim_bw_subsumed:                        0
% 2.57/1.02  sim_fw_subsumption_res:                 1
% 2.57/1.02  sim_bw_subsumption_res:                 0
% 2.57/1.02  sim_tautology_del:                      1
% 2.57/1.02  sim_eq_tautology_del:                   12
% 2.57/1.02  sim_eq_res_simp:                        0
% 2.57/1.02  sim_fw_demodulated:                     3
% 2.57/1.02  sim_bw_demodulated:                     18
% 2.57/1.02  sim_light_normalised:                   12
% 2.57/1.02  sim_joinable_taut:                      0
% 2.57/1.02  sim_joinable_simp:                      0
% 2.57/1.02  sim_ac_normalised:                      0
% 2.57/1.02  sim_smt_subsumption:                    0
% 2.57/1.02  
%------------------------------------------------------------------------------
