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
% DateTime   : Thu Dec  3 12:05:45 EST 2020

% Result     : Theorem 7.63s
% Output     : CNFRefutation 7.63s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 548 expanded)
%              Number of clauses        :   64 ( 109 expanded)
%              Number of leaves         :   19 ( 140 expanded)
%              Depth                    :   22
%              Number of atoms          :  373 (1333 expanded)
%              Number of equality atoms :  213 ( 667 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f40,plain,
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

fof(f41,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f40])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f76,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f77,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f46,f76])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f73,f77])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
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
    inference(flattening,[],[f37])).

fof(f52,plain,(
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
    inference(cnf_transformation,[],[f38])).

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
    inference(definition_unfolding,[],[f52,f48,f76,f76,f76,f77,f77,f77,f48])).

fof(f75,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f75,f77,f77])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f65,f77,f77])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f41])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f29,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f71,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f93,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1208,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1211,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2556,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1208,c_1211])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1212,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3108,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2556,c_1212])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3335,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3108,c_32])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1215,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3340,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3335,c_1215])).

cnf(c_15,plain,
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

cnf(c_1217,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_26792,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3340,c_1217])).

cnf(c_28341,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_26792,c_1208])).

cnf(c_27,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1384,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1427,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1510,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_660,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1415,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_1509,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_1651,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_18,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1441,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1652,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1441])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_30,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_341,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_30])).

cnf(c_342,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_341])).

cnf(c_1206,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_342])).

cnf(c_1409,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1206,c_29,c_342,c_1384])).

cnf(c_1410,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1409])).

cnf(c_28330,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_26792,c_1410])).

cnf(c_28437,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28341,c_29,c_27,c_1384,c_1510,c_1651,c_1652,c_28330])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_331,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_332,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_331])).

cnf(c_1207,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_333,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_332])).

cnf(c_1385,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1384])).

cnf(c_1390,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1207,c_32,c_333,c_1385])).

cnf(c_1697,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1390,c_1215])).

cnf(c_28449,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28437,c_1697])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_28460,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_28449,c_5])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1226,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1228,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2742,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1228])).

cnf(c_28928,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_28460,c_2742])).

cnf(c_1210,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2935,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1208,c_1210])).

cnf(c_1209,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3147,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2935,c_1209])).

cnf(c_30403,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_28928,c_3147])).

cnf(c_19,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_30413,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_30403,c_19])).

cnf(c_30432,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_30413,c_1226])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 7.63/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.63/1.49  
% 7.63/1.49  ------  iProver source info
% 7.63/1.49  
% 7.63/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.63/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.63/1.49  git: non_committed_changes: false
% 7.63/1.49  git: last_make_outside_of_git: false
% 7.63/1.49  
% 7.63/1.49  ------ 
% 7.63/1.49  
% 7.63/1.49  ------ Input Options
% 7.63/1.49  
% 7.63/1.49  --out_options                           all
% 7.63/1.49  --tptp_safe_out                         true
% 7.63/1.49  --problem_path                          ""
% 7.63/1.49  --include_path                          ""
% 7.63/1.49  --clausifier                            res/vclausify_rel
% 7.63/1.49  --clausifier_options                    --mode clausify
% 7.63/1.49  --stdin                                 false
% 7.63/1.49  --stats_out                             all
% 7.63/1.49  
% 7.63/1.49  ------ General Options
% 7.63/1.49  
% 7.63/1.49  --fof                                   false
% 7.63/1.49  --time_out_real                         305.
% 7.63/1.49  --time_out_virtual                      -1.
% 7.63/1.49  --symbol_type_check                     false
% 7.63/1.49  --clausify_out                          false
% 7.63/1.49  --sig_cnt_out                           false
% 7.63/1.49  --trig_cnt_out                          false
% 7.63/1.49  --trig_cnt_out_tolerance                1.
% 7.63/1.49  --trig_cnt_out_sk_spl                   false
% 7.63/1.49  --abstr_cl_out                          false
% 7.63/1.49  
% 7.63/1.49  ------ Global Options
% 7.63/1.49  
% 7.63/1.49  --schedule                              default
% 7.63/1.49  --add_important_lit                     false
% 7.63/1.49  --prop_solver_per_cl                    1000
% 7.63/1.49  --min_unsat_core                        false
% 7.63/1.49  --soft_assumptions                      false
% 7.63/1.49  --soft_lemma_size                       3
% 7.63/1.49  --prop_impl_unit_size                   0
% 7.63/1.49  --prop_impl_unit                        []
% 7.63/1.49  --share_sel_clauses                     true
% 7.63/1.49  --reset_solvers                         false
% 7.63/1.49  --bc_imp_inh                            [conj_cone]
% 7.63/1.49  --conj_cone_tolerance                   3.
% 7.63/1.49  --extra_neg_conj                        none
% 7.63/1.49  --large_theory_mode                     true
% 7.63/1.49  --prolific_symb_bound                   200
% 7.63/1.49  --lt_threshold                          2000
% 7.63/1.49  --clause_weak_htbl                      true
% 7.63/1.49  --gc_record_bc_elim                     false
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing Options
% 7.63/1.49  
% 7.63/1.49  --preprocessing_flag                    true
% 7.63/1.49  --time_out_prep_mult                    0.1
% 7.63/1.49  --splitting_mode                        input
% 7.63/1.49  --splitting_grd                         true
% 7.63/1.49  --splitting_cvd                         false
% 7.63/1.49  --splitting_cvd_svl                     false
% 7.63/1.49  --splitting_nvd                         32
% 7.63/1.49  --sub_typing                            true
% 7.63/1.49  --prep_gs_sim                           true
% 7.63/1.49  --prep_unflatten                        true
% 7.63/1.49  --prep_res_sim                          true
% 7.63/1.49  --prep_upred                            true
% 7.63/1.49  --prep_sem_filter                       exhaustive
% 7.63/1.49  --prep_sem_filter_out                   false
% 7.63/1.49  --pred_elim                             true
% 7.63/1.49  --res_sim_input                         true
% 7.63/1.49  --eq_ax_congr_red                       true
% 7.63/1.49  --pure_diseq_elim                       true
% 7.63/1.49  --brand_transform                       false
% 7.63/1.49  --non_eq_to_eq                          false
% 7.63/1.49  --prep_def_merge                        true
% 7.63/1.49  --prep_def_merge_prop_impl              false
% 7.63/1.49  --prep_def_merge_mbd                    true
% 7.63/1.49  --prep_def_merge_tr_red                 false
% 7.63/1.49  --prep_def_merge_tr_cl                  false
% 7.63/1.49  --smt_preprocessing                     true
% 7.63/1.49  --smt_ac_axioms                         fast
% 7.63/1.49  --preprocessed_out                      false
% 7.63/1.49  --preprocessed_stats                    false
% 7.63/1.49  
% 7.63/1.49  ------ Abstraction refinement Options
% 7.63/1.49  
% 7.63/1.49  --abstr_ref                             []
% 7.63/1.49  --abstr_ref_prep                        false
% 7.63/1.49  --abstr_ref_until_sat                   false
% 7.63/1.49  --abstr_ref_sig_restrict                funpre
% 7.63/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.49  --abstr_ref_under                       []
% 7.63/1.49  
% 7.63/1.49  ------ SAT Options
% 7.63/1.49  
% 7.63/1.49  --sat_mode                              false
% 7.63/1.49  --sat_fm_restart_options                ""
% 7.63/1.49  --sat_gr_def                            false
% 7.63/1.49  --sat_epr_types                         true
% 7.63/1.49  --sat_non_cyclic_types                  false
% 7.63/1.49  --sat_finite_models                     false
% 7.63/1.49  --sat_fm_lemmas                         false
% 7.63/1.49  --sat_fm_prep                           false
% 7.63/1.49  --sat_fm_uc_incr                        true
% 7.63/1.49  --sat_out_model                         small
% 7.63/1.49  --sat_out_clauses                       false
% 7.63/1.49  
% 7.63/1.49  ------ QBF Options
% 7.63/1.49  
% 7.63/1.49  --qbf_mode                              false
% 7.63/1.49  --qbf_elim_univ                         false
% 7.63/1.49  --qbf_dom_inst                          none
% 7.63/1.49  --qbf_dom_pre_inst                      false
% 7.63/1.49  --qbf_sk_in                             false
% 7.63/1.49  --qbf_pred_elim                         true
% 7.63/1.49  --qbf_split                             512
% 7.63/1.49  
% 7.63/1.49  ------ BMC1 Options
% 7.63/1.49  
% 7.63/1.49  --bmc1_incremental                      false
% 7.63/1.49  --bmc1_axioms                           reachable_all
% 7.63/1.49  --bmc1_min_bound                        0
% 7.63/1.49  --bmc1_max_bound                        -1
% 7.63/1.49  --bmc1_max_bound_default                -1
% 7.63/1.49  --bmc1_symbol_reachability              true
% 7.63/1.49  --bmc1_property_lemmas                  false
% 7.63/1.49  --bmc1_k_induction                      false
% 7.63/1.49  --bmc1_non_equiv_states                 false
% 7.63/1.49  --bmc1_deadlock                         false
% 7.63/1.49  --bmc1_ucm                              false
% 7.63/1.49  --bmc1_add_unsat_core                   none
% 7.63/1.49  --bmc1_unsat_core_children              false
% 7.63/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.49  --bmc1_out_stat                         full
% 7.63/1.49  --bmc1_ground_init                      false
% 7.63/1.49  --bmc1_pre_inst_next_state              false
% 7.63/1.49  --bmc1_pre_inst_state                   false
% 7.63/1.49  --bmc1_pre_inst_reach_state             false
% 7.63/1.49  --bmc1_out_unsat_core                   false
% 7.63/1.49  --bmc1_aig_witness_out                  false
% 7.63/1.49  --bmc1_verbose                          false
% 7.63/1.49  --bmc1_dump_clauses_tptp                false
% 7.63/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.49  --bmc1_dump_file                        -
% 7.63/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.49  --bmc1_ucm_extend_mode                  1
% 7.63/1.49  --bmc1_ucm_init_mode                    2
% 7.63/1.49  --bmc1_ucm_cone_mode                    none
% 7.63/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.49  --bmc1_ucm_relax_model                  4
% 7.63/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.49  --bmc1_ucm_layered_model                none
% 7.63/1.49  --bmc1_ucm_max_lemma_size               10
% 7.63/1.49  
% 7.63/1.49  ------ AIG Options
% 7.63/1.49  
% 7.63/1.49  --aig_mode                              false
% 7.63/1.49  
% 7.63/1.49  ------ Instantiation Options
% 7.63/1.49  
% 7.63/1.49  --instantiation_flag                    true
% 7.63/1.49  --inst_sos_flag                         false
% 7.63/1.49  --inst_sos_phase                        true
% 7.63/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.49  --inst_lit_sel_side                     num_symb
% 7.63/1.49  --inst_solver_per_active                1400
% 7.63/1.49  --inst_solver_calls_frac                1.
% 7.63/1.49  --inst_passive_queue_type               priority_queues
% 7.63/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.49  --inst_passive_queues_freq              [25;2]
% 7.63/1.49  --inst_dismatching                      true
% 7.63/1.49  --inst_eager_unprocessed_to_passive     true
% 7.63/1.49  --inst_prop_sim_given                   true
% 7.63/1.49  --inst_prop_sim_new                     false
% 7.63/1.49  --inst_subs_new                         false
% 7.63/1.49  --inst_eq_res_simp                      false
% 7.63/1.49  --inst_subs_given                       false
% 7.63/1.49  --inst_orphan_elimination               true
% 7.63/1.49  --inst_learning_loop_flag               true
% 7.63/1.49  --inst_learning_start                   3000
% 7.63/1.49  --inst_learning_factor                  2
% 7.63/1.49  --inst_start_prop_sim_after_learn       3
% 7.63/1.49  --inst_sel_renew                        solver
% 7.63/1.49  --inst_lit_activity_flag                true
% 7.63/1.49  --inst_restr_to_given                   false
% 7.63/1.49  --inst_activity_threshold               500
% 7.63/1.49  --inst_out_proof                        true
% 7.63/1.49  
% 7.63/1.49  ------ Resolution Options
% 7.63/1.49  
% 7.63/1.49  --resolution_flag                       true
% 7.63/1.49  --res_lit_sel                           adaptive
% 7.63/1.49  --res_lit_sel_side                      none
% 7.63/1.49  --res_ordering                          kbo
% 7.63/1.49  --res_to_prop_solver                    active
% 7.63/1.49  --res_prop_simpl_new                    false
% 7.63/1.49  --res_prop_simpl_given                  true
% 7.63/1.49  --res_passive_queue_type                priority_queues
% 7.63/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.49  --res_passive_queues_freq               [15;5]
% 7.63/1.49  --res_forward_subs                      full
% 7.63/1.49  --res_backward_subs                     full
% 7.63/1.49  --res_forward_subs_resolution           true
% 7.63/1.49  --res_backward_subs_resolution          true
% 7.63/1.49  --res_orphan_elimination                true
% 7.63/1.49  --res_time_limit                        2.
% 7.63/1.49  --res_out_proof                         true
% 7.63/1.49  
% 7.63/1.49  ------ Superposition Options
% 7.63/1.49  
% 7.63/1.49  --superposition_flag                    true
% 7.63/1.49  --sup_passive_queue_type                priority_queues
% 7.63/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.63/1.49  --demod_completeness_check              fast
% 7.63/1.49  --demod_use_ground                      true
% 7.63/1.49  --sup_to_prop_solver                    passive
% 7.63/1.49  --sup_prop_simpl_new                    true
% 7.63/1.49  --sup_prop_simpl_given                  true
% 7.63/1.49  --sup_fun_splitting                     false
% 7.63/1.49  --sup_smt_interval                      50000
% 7.63/1.49  
% 7.63/1.49  ------ Superposition Simplification Setup
% 7.63/1.49  
% 7.63/1.49  --sup_indices_passive                   []
% 7.63/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_full_bw                           [BwDemod]
% 7.63/1.49  --sup_immed_triv                        [TrivRules]
% 7.63/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_immed_bw_main                     []
% 7.63/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.49  
% 7.63/1.49  ------ Combination Options
% 7.63/1.49  
% 7.63/1.49  --comb_res_mult                         3
% 7.63/1.49  --comb_sup_mult                         2
% 7.63/1.49  --comb_inst_mult                        10
% 7.63/1.49  
% 7.63/1.49  ------ Debug Options
% 7.63/1.49  
% 7.63/1.49  --dbg_backtrace                         false
% 7.63/1.49  --dbg_dump_prop_clauses                 false
% 7.63/1.49  --dbg_dump_prop_clauses_file            -
% 7.63/1.49  --dbg_out_stat                          false
% 7.63/1.49  ------ Parsing...
% 7.63/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.63/1.49  ------ Proving...
% 7.63/1.49  ------ Problem Properties 
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  clauses                                 28
% 7.63/1.49  conjectures                             3
% 7.63/1.49  EPR                                     4
% 7.63/1.49  Horn                                    26
% 7.63/1.49  unary                                   16
% 7.63/1.49  binary                                  8
% 7.63/1.49  lits                                    50
% 7.63/1.49  lits eq                                 20
% 7.63/1.49  fd_pure                                 0
% 7.63/1.49  fd_pseudo                               0
% 7.63/1.49  fd_cond                                 1
% 7.63/1.49  fd_pseudo_cond                          2
% 7.63/1.49  AC symbols                              0
% 7.63/1.49  
% 7.63/1.49  ------ Schedule dynamic 5 is on 
% 7.63/1.49  
% 7.63/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ 
% 7.63/1.49  Current options:
% 7.63/1.49  ------ 
% 7.63/1.49  
% 7.63/1.49  ------ Input Options
% 7.63/1.49  
% 7.63/1.49  --out_options                           all
% 7.63/1.49  --tptp_safe_out                         true
% 7.63/1.49  --problem_path                          ""
% 7.63/1.49  --include_path                          ""
% 7.63/1.49  --clausifier                            res/vclausify_rel
% 7.63/1.49  --clausifier_options                    --mode clausify
% 7.63/1.49  --stdin                                 false
% 7.63/1.49  --stats_out                             all
% 7.63/1.49  
% 7.63/1.49  ------ General Options
% 7.63/1.49  
% 7.63/1.49  --fof                                   false
% 7.63/1.49  --time_out_real                         305.
% 7.63/1.49  --time_out_virtual                      -1.
% 7.63/1.49  --symbol_type_check                     false
% 7.63/1.49  --clausify_out                          false
% 7.63/1.49  --sig_cnt_out                           false
% 7.63/1.49  --trig_cnt_out                          false
% 7.63/1.49  --trig_cnt_out_tolerance                1.
% 7.63/1.49  --trig_cnt_out_sk_spl                   false
% 7.63/1.49  --abstr_cl_out                          false
% 7.63/1.49  
% 7.63/1.49  ------ Global Options
% 7.63/1.49  
% 7.63/1.49  --schedule                              default
% 7.63/1.49  --add_important_lit                     false
% 7.63/1.49  --prop_solver_per_cl                    1000
% 7.63/1.49  --min_unsat_core                        false
% 7.63/1.49  --soft_assumptions                      false
% 7.63/1.49  --soft_lemma_size                       3
% 7.63/1.49  --prop_impl_unit_size                   0
% 7.63/1.49  --prop_impl_unit                        []
% 7.63/1.49  --share_sel_clauses                     true
% 7.63/1.49  --reset_solvers                         false
% 7.63/1.49  --bc_imp_inh                            [conj_cone]
% 7.63/1.49  --conj_cone_tolerance                   3.
% 7.63/1.49  --extra_neg_conj                        none
% 7.63/1.49  --large_theory_mode                     true
% 7.63/1.49  --prolific_symb_bound                   200
% 7.63/1.49  --lt_threshold                          2000
% 7.63/1.49  --clause_weak_htbl                      true
% 7.63/1.49  --gc_record_bc_elim                     false
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing Options
% 7.63/1.49  
% 7.63/1.49  --preprocessing_flag                    true
% 7.63/1.49  --time_out_prep_mult                    0.1
% 7.63/1.49  --splitting_mode                        input
% 7.63/1.49  --splitting_grd                         true
% 7.63/1.49  --splitting_cvd                         false
% 7.63/1.49  --splitting_cvd_svl                     false
% 7.63/1.49  --splitting_nvd                         32
% 7.63/1.49  --sub_typing                            true
% 7.63/1.49  --prep_gs_sim                           true
% 7.63/1.49  --prep_unflatten                        true
% 7.63/1.49  --prep_res_sim                          true
% 7.63/1.49  --prep_upred                            true
% 7.63/1.49  --prep_sem_filter                       exhaustive
% 7.63/1.49  --prep_sem_filter_out                   false
% 7.63/1.49  --pred_elim                             true
% 7.63/1.49  --res_sim_input                         true
% 7.63/1.49  --eq_ax_congr_red                       true
% 7.63/1.49  --pure_diseq_elim                       true
% 7.63/1.49  --brand_transform                       false
% 7.63/1.49  --non_eq_to_eq                          false
% 7.63/1.49  --prep_def_merge                        true
% 7.63/1.49  --prep_def_merge_prop_impl              false
% 7.63/1.49  --prep_def_merge_mbd                    true
% 7.63/1.49  --prep_def_merge_tr_red                 false
% 7.63/1.49  --prep_def_merge_tr_cl                  false
% 7.63/1.49  --smt_preprocessing                     true
% 7.63/1.49  --smt_ac_axioms                         fast
% 7.63/1.49  --preprocessed_out                      false
% 7.63/1.49  --preprocessed_stats                    false
% 7.63/1.49  
% 7.63/1.49  ------ Abstraction refinement Options
% 7.63/1.49  
% 7.63/1.49  --abstr_ref                             []
% 7.63/1.49  --abstr_ref_prep                        false
% 7.63/1.49  --abstr_ref_until_sat                   false
% 7.63/1.49  --abstr_ref_sig_restrict                funpre
% 7.63/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.63/1.49  --abstr_ref_under                       []
% 7.63/1.49  
% 7.63/1.49  ------ SAT Options
% 7.63/1.49  
% 7.63/1.49  --sat_mode                              false
% 7.63/1.49  --sat_fm_restart_options                ""
% 7.63/1.49  --sat_gr_def                            false
% 7.63/1.49  --sat_epr_types                         true
% 7.63/1.49  --sat_non_cyclic_types                  false
% 7.63/1.49  --sat_finite_models                     false
% 7.63/1.49  --sat_fm_lemmas                         false
% 7.63/1.49  --sat_fm_prep                           false
% 7.63/1.49  --sat_fm_uc_incr                        true
% 7.63/1.49  --sat_out_model                         small
% 7.63/1.49  --sat_out_clauses                       false
% 7.63/1.49  
% 7.63/1.49  ------ QBF Options
% 7.63/1.49  
% 7.63/1.49  --qbf_mode                              false
% 7.63/1.49  --qbf_elim_univ                         false
% 7.63/1.49  --qbf_dom_inst                          none
% 7.63/1.49  --qbf_dom_pre_inst                      false
% 7.63/1.49  --qbf_sk_in                             false
% 7.63/1.49  --qbf_pred_elim                         true
% 7.63/1.49  --qbf_split                             512
% 7.63/1.49  
% 7.63/1.49  ------ BMC1 Options
% 7.63/1.49  
% 7.63/1.49  --bmc1_incremental                      false
% 7.63/1.49  --bmc1_axioms                           reachable_all
% 7.63/1.49  --bmc1_min_bound                        0
% 7.63/1.49  --bmc1_max_bound                        -1
% 7.63/1.49  --bmc1_max_bound_default                -1
% 7.63/1.49  --bmc1_symbol_reachability              true
% 7.63/1.49  --bmc1_property_lemmas                  false
% 7.63/1.49  --bmc1_k_induction                      false
% 7.63/1.49  --bmc1_non_equiv_states                 false
% 7.63/1.49  --bmc1_deadlock                         false
% 7.63/1.49  --bmc1_ucm                              false
% 7.63/1.49  --bmc1_add_unsat_core                   none
% 7.63/1.49  --bmc1_unsat_core_children              false
% 7.63/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.63/1.49  --bmc1_out_stat                         full
% 7.63/1.49  --bmc1_ground_init                      false
% 7.63/1.49  --bmc1_pre_inst_next_state              false
% 7.63/1.49  --bmc1_pre_inst_state                   false
% 7.63/1.49  --bmc1_pre_inst_reach_state             false
% 7.63/1.49  --bmc1_out_unsat_core                   false
% 7.63/1.49  --bmc1_aig_witness_out                  false
% 7.63/1.49  --bmc1_verbose                          false
% 7.63/1.49  --bmc1_dump_clauses_tptp                false
% 7.63/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.63/1.49  --bmc1_dump_file                        -
% 7.63/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.63/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.63/1.49  --bmc1_ucm_extend_mode                  1
% 7.63/1.49  --bmc1_ucm_init_mode                    2
% 7.63/1.49  --bmc1_ucm_cone_mode                    none
% 7.63/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.63/1.49  --bmc1_ucm_relax_model                  4
% 7.63/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.63/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.63/1.49  --bmc1_ucm_layered_model                none
% 7.63/1.49  --bmc1_ucm_max_lemma_size               10
% 7.63/1.49  
% 7.63/1.49  ------ AIG Options
% 7.63/1.49  
% 7.63/1.49  --aig_mode                              false
% 7.63/1.49  
% 7.63/1.49  ------ Instantiation Options
% 7.63/1.49  
% 7.63/1.49  --instantiation_flag                    true
% 7.63/1.49  --inst_sos_flag                         false
% 7.63/1.49  --inst_sos_phase                        true
% 7.63/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.63/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.63/1.49  --inst_lit_sel_side                     none
% 7.63/1.49  --inst_solver_per_active                1400
% 7.63/1.49  --inst_solver_calls_frac                1.
% 7.63/1.49  --inst_passive_queue_type               priority_queues
% 7.63/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.63/1.49  --inst_passive_queues_freq              [25;2]
% 7.63/1.49  --inst_dismatching                      true
% 7.63/1.49  --inst_eager_unprocessed_to_passive     true
% 7.63/1.49  --inst_prop_sim_given                   true
% 7.63/1.49  --inst_prop_sim_new                     false
% 7.63/1.49  --inst_subs_new                         false
% 7.63/1.49  --inst_eq_res_simp                      false
% 7.63/1.49  --inst_subs_given                       false
% 7.63/1.49  --inst_orphan_elimination               true
% 7.63/1.49  --inst_learning_loop_flag               true
% 7.63/1.49  --inst_learning_start                   3000
% 7.63/1.49  --inst_learning_factor                  2
% 7.63/1.49  --inst_start_prop_sim_after_learn       3
% 7.63/1.49  --inst_sel_renew                        solver
% 7.63/1.49  --inst_lit_activity_flag                true
% 7.63/1.49  --inst_restr_to_given                   false
% 7.63/1.49  --inst_activity_threshold               500
% 7.63/1.49  --inst_out_proof                        true
% 7.63/1.49  
% 7.63/1.49  ------ Resolution Options
% 7.63/1.49  
% 7.63/1.49  --resolution_flag                       false
% 7.63/1.49  --res_lit_sel                           adaptive
% 7.63/1.49  --res_lit_sel_side                      none
% 7.63/1.49  --res_ordering                          kbo
% 7.63/1.49  --res_to_prop_solver                    active
% 7.63/1.49  --res_prop_simpl_new                    false
% 7.63/1.49  --res_prop_simpl_given                  true
% 7.63/1.49  --res_passive_queue_type                priority_queues
% 7.63/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.63/1.49  --res_passive_queues_freq               [15;5]
% 7.63/1.49  --res_forward_subs                      full
% 7.63/1.49  --res_backward_subs                     full
% 7.63/1.49  --res_forward_subs_resolution           true
% 7.63/1.49  --res_backward_subs_resolution          true
% 7.63/1.49  --res_orphan_elimination                true
% 7.63/1.49  --res_time_limit                        2.
% 7.63/1.49  --res_out_proof                         true
% 7.63/1.49  
% 7.63/1.49  ------ Superposition Options
% 7.63/1.49  
% 7.63/1.49  --superposition_flag                    true
% 7.63/1.49  --sup_passive_queue_type                priority_queues
% 7.63/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.63/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.63/1.49  --demod_completeness_check              fast
% 7.63/1.49  --demod_use_ground                      true
% 7.63/1.49  --sup_to_prop_solver                    passive
% 7.63/1.49  --sup_prop_simpl_new                    true
% 7.63/1.49  --sup_prop_simpl_given                  true
% 7.63/1.49  --sup_fun_splitting                     false
% 7.63/1.49  --sup_smt_interval                      50000
% 7.63/1.49  
% 7.63/1.49  ------ Superposition Simplification Setup
% 7.63/1.49  
% 7.63/1.49  --sup_indices_passive                   []
% 7.63/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.63/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.63/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_full_bw                           [BwDemod]
% 7.63/1.49  --sup_immed_triv                        [TrivRules]
% 7.63/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.63/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_immed_bw_main                     []
% 7.63/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.63/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.63/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.63/1.49  
% 7.63/1.49  ------ Combination Options
% 7.63/1.49  
% 7.63/1.49  --comb_res_mult                         3
% 7.63/1.49  --comb_sup_mult                         2
% 7.63/1.49  --comb_inst_mult                        10
% 7.63/1.49  
% 7.63/1.49  ------ Debug Options
% 7.63/1.49  
% 7.63/1.49  --dbg_backtrace                         false
% 7.63/1.49  --dbg_dump_prop_clauses                 false
% 7.63/1.49  --dbg_dump_prop_clauses_file            -
% 7.63/1.49  --dbg_out_stat                          false
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  ------ Proving...
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  % SZS status Theorem for theBenchmark.p
% 7.63/1.49  
% 7.63/1.49   Resolution empty clause
% 7.63/1.49  
% 7.63/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  fof(f17,conjecture,(
% 7.63/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f18,negated_conjecture,(
% 7.63/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.63/1.49    inference(negated_conjecture,[],[f17])).
% 7.63/1.49  
% 7.63/1.49  fof(f19,plain,(
% 7.63/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 7.63/1.49    inference(pure_predicate_removal,[],[f18])).
% 7.63/1.49  
% 7.63/1.49  fof(f31,plain,(
% 7.63/1.49    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 7.63/1.49    inference(ennf_transformation,[],[f19])).
% 7.63/1.49  
% 7.63/1.49  fof(f32,plain,(
% 7.63/1.49    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 7.63/1.49    inference(flattening,[],[f31])).
% 7.63/1.49  
% 7.63/1.49  fof(f40,plain,(
% 7.63/1.49    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 7.63/1.49    introduced(choice_axiom,[])).
% 7.63/1.49  
% 7.63/1.49  fof(f41,plain,(
% 7.63/1.49    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 7.63/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f40])).
% 7.63/1.49  
% 7.63/1.49  fof(f73,plain,(
% 7.63/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 7.63/1.49    inference(cnf_transformation,[],[f41])).
% 7.63/1.49  
% 7.63/1.49  fof(f3,axiom,(
% 7.63/1.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f46,plain,(
% 7.63/1.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f3])).
% 7.63/1.49  
% 7.63/1.49  fof(f4,axiom,(
% 7.63/1.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f47,plain,(
% 7.63/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f4])).
% 7.63/1.49  
% 7.63/1.49  fof(f5,axiom,(
% 7.63/1.49    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f48,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f5])).
% 7.63/1.49  
% 7.63/1.49  fof(f76,plain,(
% 7.63/1.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 7.63/1.49    inference(definition_unfolding,[],[f47,f48])).
% 7.63/1.49  
% 7.63/1.49  fof(f77,plain,(
% 7.63/1.49    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 7.63/1.49    inference(definition_unfolding,[],[f46,f76])).
% 7.63/1.49  
% 7.63/1.49  fof(f89,plain,(
% 7.63/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 7.63/1.49    inference(definition_unfolding,[],[f73,f77])).
% 7.63/1.49  
% 7.63/1.49  fof(f14,axiom,(
% 7.63/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f27,plain,(
% 7.63/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.63/1.49    inference(ennf_transformation,[],[f14])).
% 7.63/1.49  
% 7.63/1.49  fof(f68,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f27])).
% 7.63/1.49  
% 7.63/1.49  fof(f13,axiom,(
% 7.63/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f26,plain,(
% 7.63/1.49    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.63/1.49    inference(ennf_transformation,[],[f13])).
% 7.63/1.49  
% 7.63/1.49  fof(f67,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f26])).
% 7.63/1.49  
% 7.63/1.49  fof(f8,axiom,(
% 7.63/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f39,plain,(
% 7.63/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.63/1.49    inference(nnf_transformation,[],[f8])).
% 7.63/1.49  
% 7.63/1.49  fof(f61,plain,(
% 7.63/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f39])).
% 7.63/1.49  
% 7.63/1.49  fof(f7,axiom,(
% 7.63/1.49    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f21,plain,(
% 7.63/1.49    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 7.63/1.49    inference(ennf_transformation,[],[f7])).
% 7.63/1.49  
% 7.63/1.49  fof(f37,plain,(
% 7.63/1.49    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 7.63/1.49    inference(nnf_transformation,[],[f21])).
% 7.63/1.49  
% 7.63/1.49  fof(f38,plain,(
% 7.63/1.49    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 7.63/1.49    inference(flattening,[],[f37])).
% 7.63/1.49  
% 7.63/1.49  fof(f52,plain,(
% 7.63/1.49    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f38])).
% 7.63/1.49  
% 7.63/1.49  fof(f86,plain,(
% 7.63/1.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 7.63/1.49    inference(definition_unfolding,[],[f52,f48,f76,f76,f76,f77,f77,f77,f48])).
% 7.63/1.49  
% 7.63/1.49  fof(f75,plain,(
% 7.63/1.49    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 7.63/1.49    inference(cnf_transformation,[],[f41])).
% 7.63/1.49  
% 7.63/1.49  fof(f88,plain,(
% 7.63/1.49    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 7.63/1.49    inference(definition_unfolding,[],[f75,f77,f77])).
% 7.63/1.49  
% 7.63/1.49  fof(f12,axiom,(
% 7.63/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f25,plain,(
% 7.63/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.63/1.49    inference(ennf_transformation,[],[f12])).
% 7.63/1.49  
% 7.63/1.49  fof(f66,plain,(
% 7.63/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f25])).
% 7.63/1.49  
% 7.63/1.49  fof(f15,axiom,(
% 7.63/1.49    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f28,plain,(
% 7.63/1.49    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.63/1.49    inference(ennf_transformation,[],[f15])).
% 7.63/1.49  
% 7.63/1.49  fof(f69,plain,(
% 7.63/1.49    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.63/1.49    inference(cnf_transformation,[],[f28])).
% 7.63/1.49  
% 7.63/1.49  fof(f9,axiom,(
% 7.63/1.49    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f22,plain,(
% 7.63/1.49    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 7.63/1.49    inference(ennf_transformation,[],[f9])).
% 7.63/1.49  
% 7.63/1.49  fof(f63,plain,(
% 7.63/1.49    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f22])).
% 7.63/1.49  
% 7.63/1.49  fof(f11,axiom,(
% 7.63/1.49    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f23,plain,(
% 7.63/1.49    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.63/1.49    inference(ennf_transformation,[],[f11])).
% 7.63/1.49  
% 7.63/1.49  fof(f24,plain,(
% 7.63/1.49    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.63/1.49    inference(flattening,[],[f23])).
% 7.63/1.49  
% 7.63/1.49  fof(f65,plain,(
% 7.63/1.49    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f24])).
% 7.63/1.49  
% 7.63/1.49  fof(f87,plain,(
% 7.63/1.49    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.63/1.49    inference(definition_unfolding,[],[f65,f77,f77])).
% 7.63/1.49  
% 7.63/1.49  fof(f72,plain,(
% 7.63/1.49    v1_funct_1(sK3)),
% 7.63/1.49    inference(cnf_transformation,[],[f41])).
% 7.63/1.49  
% 7.63/1.49  fof(f16,axiom,(
% 7.63/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f20,plain,(
% 7.63/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)))),
% 7.63/1.49    inference(pure_predicate_removal,[],[f16])).
% 7.63/1.49  
% 7.63/1.49  fof(f29,plain,(
% 7.63/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.63/1.49    inference(ennf_transformation,[],[f20])).
% 7.63/1.49  
% 7.63/1.49  fof(f30,plain,(
% 7.63/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.63/1.49    inference(flattening,[],[f29])).
% 7.63/1.49  
% 7.63/1.49  fof(f71,plain,(
% 7.63/1.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f30])).
% 7.63/1.49  
% 7.63/1.49  fof(f6,axiom,(
% 7.63/1.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f35,plain,(
% 7.63/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.63/1.49    inference(nnf_transformation,[],[f6])).
% 7.63/1.49  
% 7.63/1.49  fof(f36,plain,(
% 7.63/1.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 7.63/1.49    inference(flattening,[],[f35])).
% 7.63/1.49  
% 7.63/1.49  fof(f50,plain,(
% 7.63/1.49    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 7.63/1.49    inference(cnf_transformation,[],[f36])).
% 7.63/1.49  
% 7.63/1.49  fof(f93,plain,(
% 7.63/1.49    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 7.63/1.49    inference(equality_resolution,[],[f50])).
% 7.63/1.49  
% 7.63/1.49  fof(f2,axiom,(
% 7.63/1.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f45,plain,(
% 7.63/1.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f2])).
% 7.63/1.49  
% 7.63/1.49  fof(f1,axiom,(
% 7.63/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f33,plain,(
% 7.63/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.63/1.49    inference(nnf_transformation,[],[f1])).
% 7.63/1.49  
% 7.63/1.49  fof(f34,plain,(
% 7.63/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.63/1.49    inference(flattening,[],[f33])).
% 7.63/1.49  
% 7.63/1.49  fof(f44,plain,(
% 7.63/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f34])).
% 7.63/1.49  
% 7.63/1.49  fof(f10,axiom,(
% 7.63/1.49    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 7.63/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.63/1.49  
% 7.63/1.49  fof(f64,plain,(
% 7.63/1.49    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 7.63/1.49    inference(cnf_transformation,[],[f10])).
% 7.63/1.49  
% 7.63/1.49  cnf(c_29,negated_conjecture,
% 7.63/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 7.63/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1208,plain,
% 7.63/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_23,plain,
% 7.63/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.63/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.63/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1211,plain,
% 7.63/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.63/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_2556,plain,
% 7.63/1.49      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_1208,c_1211]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_22,plain,
% 7.63/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.63/1.49      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 7.63/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1212,plain,
% 7.63/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.63/1.49      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_3108,plain,
% 7.63/1.49      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top
% 7.63/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_2556,c_1212]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_32,plain,
% 7.63/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_3335,plain,
% 7.63/1.49      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top ),
% 7.63/1.49      inference(global_propositional_subsumption,[status(thm)],[c_3108,c_32]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_17,plain,
% 7.63/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.63/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1215,plain,
% 7.63/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.63/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_3340,plain,
% 7.63/1.49      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_3335,c_1215]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_15,plain,
% 7.63/1.49      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 7.63/1.49      | k2_enumset1(X1,X1,X2,X3) = X0
% 7.63/1.49      | k2_enumset1(X1,X1,X1,X3) = X0
% 7.63/1.49      | k2_enumset1(X2,X2,X2,X3) = X0
% 7.63/1.49      | k2_enumset1(X1,X1,X1,X2) = X0
% 7.63/1.49      | k2_enumset1(X3,X3,X3,X3) = X0
% 7.63/1.49      | k2_enumset1(X2,X2,X2,X2) = X0
% 7.63/1.49      | k2_enumset1(X1,X1,X1,X1) = X0
% 7.63/1.49      | k1_xboole_0 = X0 ),
% 7.63/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1217,plain,
% 7.63/1.49      ( k2_enumset1(X0,X0,X1,X2) = X3
% 7.63/1.49      | k2_enumset1(X0,X0,X0,X2) = X3
% 7.63/1.49      | k2_enumset1(X1,X1,X1,X2) = X3
% 7.63/1.49      | k2_enumset1(X0,X0,X0,X1) = X3
% 7.63/1.49      | k2_enumset1(X2,X2,X2,X2) = X3
% 7.63/1.49      | k2_enumset1(X1,X1,X1,X1) = X3
% 7.63/1.49      | k2_enumset1(X0,X0,X0,X0) = X3
% 7.63/1.49      | k1_xboole_0 = X3
% 7.63/1.49      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_26792,plain,
% 7.63/1.49      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 7.63/1.49      | k1_relat_1(sK3) = k1_xboole_0 ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_3340,c_1217]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_28341,plain,
% 7.63/1.49      ( k1_relat_1(sK3) = k1_xboole_0
% 7.63/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_26792,c_1208]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_27,negated_conjecture,
% 7.63/1.49      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 7.63/1.49      inference(cnf_transformation,[],[f88]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_21,plain,
% 7.63/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.63/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1384,plain,
% 7.63/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 7.63/1.49      | v1_relat_1(sK3) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_21]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_24,plain,
% 7.63/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.63/1.49      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.63/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1427,plain,
% 7.63/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 7.63/1.49      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_24]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1510,plain,
% 7.63/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 7.63/1.49      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_1427]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_660,plain,
% 7.63/1.49      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 7.63/1.49      theory(equality) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1415,plain,
% 7.63/1.49      ( ~ r1_tarski(X0,X1)
% 7.63/1.49      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 7.63/1.49      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 7.63/1.49      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_660]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1509,plain,
% 7.63/1.49      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 7.63/1.49      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 7.63/1.49      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 7.63/1.49      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_1415]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1651,plain,
% 7.63/1.49      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 7.63/1.49      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 7.63/1.49      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 7.63/1.49      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_1509]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_18,plain,
% 7.63/1.49      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 7.63/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1441,plain,
% 7.63/1.49      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_18]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1652,plain,
% 7.63/1.49      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 7.63/1.49      inference(instantiation,[status(thm)],[c_1441]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_20,plain,
% 7.63/1.49      ( ~ v1_funct_1(X0)
% 7.63/1.49      | ~ v1_relat_1(X0)
% 7.63/1.49      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 7.63/1.49      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 7.63/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_30,negated_conjecture,
% 7.63/1.49      ( v1_funct_1(sK3) ),
% 7.63/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_341,plain,
% 7.63/1.49      ( ~ v1_relat_1(X0)
% 7.63/1.49      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 7.63/1.49      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 7.63/1.49      | sK3 != X0 ),
% 7.63/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_30]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_342,plain,
% 7.63/1.49      ( ~ v1_relat_1(sK3)
% 7.63/1.49      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 7.63/1.49      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 7.63/1.49      inference(unflattening,[status(thm)],[c_341]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1206,plain,
% 7.63/1.49      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 7.63/1.49      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 7.63/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_342]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1409,plain,
% 7.63/1.49      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 7.63/1.49      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 7.63/1.49      inference(global_propositional_subsumption,
% 7.63/1.49                [status(thm)],
% 7.63/1.49                [c_1206,c_29,c_342,c_1384]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1410,plain,
% 7.63/1.49      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 7.63/1.49      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 7.63/1.49      inference(renaming,[status(thm)],[c_1409]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_28330,plain,
% 7.63/1.49      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 7.63/1.49      | k1_relat_1(sK3) = k1_xboole_0 ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_26792,c_1410]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_28437,plain,
% 7.63/1.49      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 7.63/1.49      inference(global_propositional_subsumption,
% 7.63/1.49                [status(thm)],
% 7.63/1.49                [c_28341,c_29,c_27,c_1384,c_1510,c_1651,c_1652,c_28330]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_25,plain,
% 7.63/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.63/1.49      | ~ v1_funct_1(X0)
% 7.63/1.49      | ~ v1_relat_1(X0) ),
% 7.63/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_331,plain,
% 7.63/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.63/1.49      | ~ v1_relat_1(X0)
% 7.63/1.49      | sK3 != X0 ),
% 7.63/1.49      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_332,plain,
% 7.63/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
% 7.63/1.49      | ~ v1_relat_1(sK3) ),
% 7.63/1.49      inference(unflattening,[status(thm)],[c_331]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1207,plain,
% 7.63/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
% 7.63/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_333,plain,
% 7.63/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
% 7.63/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_332]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1385,plain,
% 7.63/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 7.63/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_1384]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1390,plain,
% 7.63/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top ),
% 7.63/1.49      inference(global_propositional_subsumption,
% 7.63/1.49                [status(thm)],
% 7.63/1.49                [c_1207,c_32,c_333,c_1385]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1697,plain,
% 7.63/1.49      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))) = iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_1390,c_1215]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_28449,plain,
% 7.63/1.49      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK3))) = iProver_top ),
% 7.63/1.49      inference(demodulation,[status(thm)],[c_28437,c_1697]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_5,plain,
% 7.63/1.49      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.63/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_28460,plain,
% 7.63/1.49      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 7.63/1.49      inference(demodulation,[status(thm)],[c_28449,c_5]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_3,plain,
% 7.63/1.49      ( r1_tarski(k1_xboole_0,X0) ),
% 7.63/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1226,plain,
% 7.63/1.49      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_0,plain,
% 7.63/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.63/1.49      inference(cnf_transformation,[],[f44]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1228,plain,
% 7.63/1.49      ( X0 = X1
% 7.63/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.63/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_2742,plain,
% 7.63/1.49      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_1226,c_1228]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_28928,plain,
% 7.63/1.49      ( sK3 = k1_xboole_0 ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_28460,c_2742]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1210,plain,
% 7.63/1.49      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.63/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_2935,plain,
% 7.63/1.49      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 7.63/1.49      inference(superposition,[status(thm)],[c_1208,c_1210]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_1209,plain,
% 7.63/1.49      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 7.63/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_3147,plain,
% 7.63/1.49      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 7.63/1.49      inference(demodulation,[status(thm)],[c_2935,c_1209]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_30403,plain,
% 7.63/1.49      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 7.63/1.49      inference(demodulation,[status(thm)],[c_28928,c_3147]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_19,plain,
% 7.63/1.49      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 7.63/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_30413,plain,
% 7.63/1.49      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 7.63/1.49      inference(demodulation,[status(thm)],[c_30403,c_19]) ).
% 7.63/1.49  
% 7.63/1.49  cnf(c_30432,plain,
% 7.63/1.49      ( $false ),
% 7.63/1.49      inference(forward_subsumption_resolution,[status(thm)],[c_30413,c_1226]) ).
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.63/1.49  
% 7.63/1.49  ------                               Statistics
% 7.63/1.49  
% 7.63/1.49  ------ General
% 7.63/1.49  
% 7.63/1.49  abstr_ref_over_cycles:                  0
% 7.63/1.49  abstr_ref_under_cycles:                 0
% 7.63/1.49  gc_basic_clause_elim:                   0
% 7.63/1.49  forced_gc_time:                         0
% 7.63/1.49  parsing_time:                           0.011
% 7.63/1.49  unif_index_cands_time:                  0.
% 7.63/1.49  unif_index_add_time:                    0.
% 7.63/1.49  orderings_time:                         0.
% 7.63/1.49  out_proof_time:                         0.012
% 7.63/1.49  total_time:                             0.805
% 7.63/1.49  num_of_symbols:                         49
% 7.63/1.49  num_of_terms:                           29909
% 7.63/1.49  
% 7.63/1.49  ------ Preprocessing
% 7.63/1.49  
% 7.63/1.49  num_of_splits:                          0
% 7.63/1.49  num_of_split_atoms:                     0
% 7.63/1.49  num_of_reused_defs:                     0
% 7.63/1.49  num_eq_ax_congr_red:                    15
% 7.63/1.49  num_of_sem_filtered_clauses:            1
% 7.63/1.49  num_of_subtypes:                        0
% 7.63/1.49  monotx_restored_types:                  0
% 7.63/1.49  sat_num_of_epr_types:                   0
% 7.63/1.49  sat_num_of_non_cyclic_types:            0
% 7.63/1.49  sat_guarded_non_collapsed_types:        0
% 7.63/1.49  num_pure_diseq_elim:                    0
% 7.63/1.49  simp_replaced_by:                       0
% 7.63/1.49  res_preprocessed:                       140
% 7.63/1.49  prep_upred:                             0
% 7.63/1.49  prep_unflattend:                        6
% 7.63/1.49  smt_new_axioms:                         0
% 7.63/1.49  pred_elim_cands:                        3
% 7.63/1.49  pred_elim:                              1
% 7.63/1.49  pred_elim_cl:                           1
% 7.63/1.49  pred_elim_cycles:                       3
% 7.63/1.49  merged_defs:                            8
% 7.63/1.49  merged_defs_ncl:                        0
% 7.63/1.49  bin_hyper_res:                          8
% 7.63/1.49  prep_cycles:                            4
% 7.63/1.49  pred_elim_time:                         0.003
% 7.63/1.49  splitting_time:                         0.
% 7.63/1.49  sem_filter_time:                        0.
% 7.63/1.49  monotx_time:                            0.001
% 7.63/1.49  subtype_inf_time:                       0.
% 7.63/1.49  
% 7.63/1.49  ------ Problem properties
% 7.63/1.49  
% 7.63/1.49  clauses:                                28
% 7.63/1.49  conjectures:                            3
% 7.63/1.49  epr:                                    4
% 7.63/1.49  horn:                                   26
% 7.63/1.49  ground:                                 4
% 7.63/1.49  unary:                                  16
% 7.63/1.49  binary:                                 8
% 7.63/1.49  lits:                                   50
% 7.63/1.49  lits_eq:                                20
% 7.63/1.49  fd_pure:                                0
% 7.63/1.49  fd_pseudo:                              0
% 7.63/1.49  fd_cond:                                1
% 7.63/1.49  fd_pseudo_cond:                         2
% 7.63/1.49  ac_symbols:                             0
% 7.63/1.49  
% 7.63/1.49  ------ Propositional Solver
% 7.63/1.49  
% 7.63/1.49  prop_solver_calls:                      33
% 7.63/1.49  prop_fast_solver_calls:                 1201
% 7.63/1.49  smt_solver_calls:                       0
% 7.63/1.49  smt_fast_solver_calls:                  0
% 7.63/1.49  prop_num_of_clauses:                    9247
% 7.63/1.49  prop_preprocess_simplified:             20703
% 7.63/1.49  prop_fo_subsumed:                       21
% 7.63/1.49  prop_solver_time:                       0.
% 7.63/1.49  smt_solver_time:                        0.
% 7.63/1.49  smt_fast_solver_time:                   0.
% 7.63/1.49  prop_fast_solver_time:                  0.
% 7.63/1.49  prop_unsat_core_time:                   0.
% 7.63/1.49  
% 7.63/1.49  ------ QBF
% 7.63/1.49  
% 7.63/1.49  qbf_q_res:                              0
% 7.63/1.49  qbf_num_tautologies:                    0
% 7.63/1.49  qbf_prep_cycles:                        0
% 7.63/1.49  
% 7.63/1.49  ------ BMC1
% 7.63/1.49  
% 7.63/1.49  bmc1_current_bound:                     -1
% 7.63/1.49  bmc1_last_solved_bound:                 -1
% 7.63/1.49  bmc1_unsat_core_size:                   -1
% 7.63/1.49  bmc1_unsat_core_parents_size:           -1
% 7.63/1.49  bmc1_merge_next_fun:                    0
% 7.63/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.63/1.49  
% 7.63/1.49  ------ Instantiation
% 7.63/1.49  
% 7.63/1.49  inst_num_of_clauses:                    3139
% 7.63/1.49  inst_num_in_passive:                    1425
% 7.63/1.49  inst_num_in_active:                     1422
% 7.63/1.49  inst_num_in_unprocessed:                294
% 7.63/1.49  inst_num_of_loops:                      1470
% 7.63/1.49  inst_num_of_learning_restarts:          0
% 7.63/1.49  inst_num_moves_active_passive:          44
% 7.63/1.49  inst_lit_activity:                      0
% 7.63/1.49  inst_lit_activity_moves:                0
% 7.63/1.49  inst_num_tautologies:                   0
% 7.63/1.49  inst_num_prop_implied:                  0
% 7.63/1.49  inst_num_existing_simplified:           0
% 7.63/1.49  inst_num_eq_res_simplified:             0
% 7.63/1.49  inst_num_child_elim:                    0
% 7.63/1.49  inst_num_of_dismatching_blockings:      1048
% 7.63/1.49  inst_num_of_non_proper_insts:           4288
% 7.63/1.49  inst_num_of_duplicates:                 0
% 7.63/1.49  inst_inst_num_from_inst_to_res:         0
% 7.63/1.49  inst_dismatching_checking_time:         0.
% 7.63/1.49  
% 7.63/1.49  ------ Resolution
% 7.63/1.49  
% 7.63/1.49  res_num_of_clauses:                     0
% 7.63/1.49  res_num_in_passive:                     0
% 7.63/1.49  res_num_in_active:                      0
% 7.63/1.49  res_num_of_loops:                       144
% 7.63/1.49  res_forward_subset_subsumed:            494
% 7.63/1.49  res_backward_subset_subsumed:           6
% 7.63/1.49  res_forward_subsumed:                   0
% 7.63/1.49  res_backward_subsumed:                  0
% 7.63/1.49  res_forward_subsumption_resolution:     0
% 7.63/1.49  res_backward_subsumption_resolution:    0
% 7.63/1.49  res_clause_to_clause_subsumption:       4688
% 7.63/1.49  res_orphan_elimination:                 0
% 7.63/1.49  res_tautology_del:                      226
% 7.63/1.49  res_num_eq_res_simplified:              0
% 7.63/1.49  res_num_sel_changes:                    0
% 7.63/1.49  res_moves_from_active_to_pass:          0
% 7.63/1.49  
% 7.63/1.49  ------ Superposition
% 7.63/1.49  
% 7.63/1.49  sup_time_total:                         0.
% 7.63/1.49  sup_time_generating:                    0.
% 7.63/1.49  sup_time_sim_full:                      0.
% 7.63/1.49  sup_time_sim_immed:                     0.
% 7.63/1.49  
% 7.63/1.49  sup_num_of_clauses:                     414
% 7.63/1.49  sup_num_in_active:                      258
% 7.63/1.49  sup_num_in_passive:                     156
% 7.63/1.49  sup_num_of_loops:                       293
% 7.63/1.49  sup_fw_superposition:                   1648
% 7.63/1.49  sup_bw_superposition:                   972
% 7.63/1.49  sup_immediate_simplified:               1583
% 7.63/1.49  sup_given_eliminated:                   2
% 7.63/1.49  comparisons_done:                       0
% 7.63/1.49  comparisons_avoided:                    0
% 7.63/1.49  
% 7.63/1.49  ------ Simplifications
% 7.63/1.49  
% 7.63/1.49  
% 7.63/1.49  sim_fw_subset_subsumed:                 22
% 7.63/1.49  sim_bw_subset_subsumed:                 11
% 7.63/1.49  sim_fw_subsumed:                        226
% 7.63/1.49  sim_bw_subsumed:                        10
% 7.63/1.49  sim_fw_subsumption_res:                 5
% 7.63/1.49  sim_bw_subsumption_res:                 0
% 7.63/1.49  sim_tautology_del:                      1
% 7.63/1.49  sim_eq_tautology_del:                   675
% 7.63/1.49  sim_eq_res_simp:                        0
% 7.63/1.49  sim_fw_demodulated:                     1198
% 7.63/1.49  sim_bw_demodulated:                     244
% 7.63/1.49  sim_light_normalised:                   321
% 7.63/1.49  sim_joinable_taut:                      0
% 7.63/1.49  sim_joinable_simp:                      0
% 7.63/1.49  sim_ac_normalised:                      0
% 7.63/1.49  sim_smt_subsumption:                    0
% 7.63/1.49  
%------------------------------------------------------------------------------
