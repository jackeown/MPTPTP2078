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
% DateTime   : Thu Dec  3 12:05:48 EST 2020

% Result     : Theorem 3.31s
% Output     : CNFRefutation 3.31s
% Verified   : 
% Statistics : Number of formulae       :  137 (1676 expanded)
%              Number of clauses        :   73 ( 285 expanded)
%              Number of leaves         :   20 ( 469 expanded)
%              Depth                    :   29
%              Number of atoms          :  382 (4064 expanded)
%              Number of equality atoms :  245 (2641 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f30])).

fof(f36,plain,
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

fof(f37,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f36])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f71])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f68,f72])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

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

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f42,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
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
    inference(definition_unfolding,[],[f42,f41,f71,f71,f71,f72,f72,f72,f41])).

fof(f67,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f70,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f70,f72,f72])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f62,f72,f72])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_28,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_879,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_882,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2187,plain,
    ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_879,c_882])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_883,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2205,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2187,c_883])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2318,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2205,c_31])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_891,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2323,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2318,c_891])).

cnf(c_9,plain,
    ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
    | k2_enumset1(X1,X1,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X3) = X0
    | k2_enumset1(X2,X2,X2,X3) = X0
    | k2_enumset1(X1,X1,X1,X2) = X0
    | k2_enumset1(X3,X3,X3,X3) = X0
    | k2_enumset1(X2,X2,X2,X2) = X0
    | k2_enumset1(X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_893,plain,
    ( k2_enumset1(X0,X0,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X2) = X3
    | k2_enumset1(X1,X1,X1,X2) = X3
    | k2_enumset1(X0,X0,X0,X1) = X3
    | k2_enumset1(X2,X2,X2,X2) = X3
    | k2_enumset1(X1,X1,X1,X1) = X3
    | k2_enumset1(X0,X0,X0,X0) = X3
    | k1_xboole_0 = X3
    | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3664,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2323,c_893])).

cnf(c_3713,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3664,c_879])).

cnf(c_1532,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_883,c_891])).

cnf(c_3972,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k1_relset_1(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3713,c_1532])).

cnf(c_3692,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = X0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3664,c_893])).

cnf(c_5016,plain,
    ( k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3972,c_3692])).

cnf(c_5327,plain,
    ( k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5016,c_879])).

cnf(c_5450,plain,
    ( k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3),k1_relset_1(k1_relat_1(sK3),sK1,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5327,c_1532])).

cnf(c_5304,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = X0
    | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_relset_1(k1_relat_1(sK3),sK1,sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5016,c_893])).

cnf(c_6965,plain,
    ( k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0)
    | k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k1_xboole_0
    | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5450,c_5304])).

cnf(c_7016,plain,
    ( k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k1_xboole_0
    | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6965,c_883])).

cnf(c_7191,plain,
    ( m1_subset_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3))) = iProver_top
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
    | k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7016,c_5327])).

cnf(c_7192,plain,
    ( k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k1_xboole_0
    | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3))) = iProver_top ),
    inference(renaming,[status(thm)],[c_7191])).

cnf(c_7199,plain,
    ( k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k1_xboole_0
    | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
    | k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),k1_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5016,c_7192])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1092,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1093,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1092])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1181,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1315,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1181])).

cnf(c_292,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1148,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_1314,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
    inference(instantiation,[status(thm)],[c_1148])).

cnf(c_1447,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
    | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1314])).

cnf(c_12,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1195,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1448,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1195])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_885,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
    | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3702,plain,
    ( k2_enumset1(k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0)) = k2_relat_1(X0)
    | k1_relat_1(X0) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3664,c_885])).

cnf(c_7840,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3702])).

cnf(c_8173,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7199,c_30,c_28,c_31,c_26,c_1092,c_1093,c_1315,c_1447,c_1448,c_7840])).

cnf(c_14,plain,
    ( ~ r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_889,plain,
    ( k9_relat_1(X0,X1) = k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_8207,plain,
    ( k9_relat_1(sK3,X0) = k1_xboole_0
    | r1_xboole_0(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8173,c_889])).

cnf(c_18,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_886,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_1218,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_886])).

cnf(c_13,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,plain,
    ( r1_xboole_0(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k9_relat_1(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_888,plain,
    ( k9_relat_1(X0,X1) != k1_xboole_0
    | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2447,plain,
    ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13,c_888])).

cnf(c_17,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2448,plain,
    ( r1_xboole_0(k1_xboole_0,X0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2447,c_17])).

cnf(c_8263,plain,
    ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8207,c_31,c_1093,c_1218,c_2448])).

cnf(c_881,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2674,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_879,c_881])).

cnf(c_880,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_2915,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2674,c_880])).

cnf(c_8268,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8263,c_2915])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_3238,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3241,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3238])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8268,c_3241])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 19:19:52 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.31/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.31/0.99  
% 3.31/0.99  ------  iProver source info
% 3.31/0.99  
% 3.31/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.31/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.31/0.99  git: non_committed_changes: false
% 3.31/0.99  git: last_make_outside_of_git: false
% 3.31/0.99  
% 3.31/0.99  ------ 
% 3.31/0.99  ------ Parsing...
% 3.31/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.31/0.99  
% 3.31/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.31/0.99  ------ Proving...
% 3.31/0.99  ------ Problem Properties 
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  clauses                                 30
% 3.31/0.99  conjectures                             4
% 3.31/0.99  EPR                                     3
% 3.31/0.99  Horn                                    29
% 3.31/0.99  unary                                   19
% 3.31/0.99  binary                                  7
% 3.31/0.99  lits                                    52
% 3.31/0.99  lits eq                                 19
% 3.31/0.99  fd_pure                                 0
% 3.31/0.99  fd_pseudo                               0
% 3.31/0.99  fd_cond                                 0
% 3.31/0.99  fd_pseudo_cond                          1
% 3.31/0.99  AC symbols                              0
% 3.31/0.99  
% 3.31/0.99  ------ Input Options Time Limit: Unbounded
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  ------ 
% 3.31/0.99  Current options:
% 3.31/0.99  ------ 
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  ------ Proving...
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  % SZS status Theorem for theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  fof(f18,conjecture,(
% 3.31/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f19,negated_conjecture,(
% 3.31/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.31/0.99    inference(negated_conjecture,[],[f18])).
% 3.31/0.99  
% 3.31/0.99  fof(f20,plain,(
% 3.31/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.31/0.99    inference(pure_predicate_removal,[],[f19])).
% 3.31/0.99  
% 3.31/0.99  fof(f30,plain,(
% 3.31/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 3.31/0.99    inference(ennf_transformation,[],[f20])).
% 3.31/0.99  
% 3.31/0.99  fof(f31,plain,(
% 3.31/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 3.31/0.99    inference(flattening,[],[f30])).
% 3.31/0.99  
% 3.31/0.99  fof(f36,plain,(
% 3.31/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 3.31/0.99    introduced(choice_axiom,[])).
% 3.31/0.99  
% 3.31/0.99  fof(f37,plain,(
% 3.31/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 3.31/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f36])).
% 3.31/0.99  
% 3.31/0.99  fof(f68,plain,(
% 3.31/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.31/0.99    inference(cnf_transformation,[],[f37])).
% 3.31/0.99  
% 3.31/0.99  fof(f2,axiom,(
% 3.31/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f39,plain,(
% 3.31/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f2])).
% 3.31/0.99  
% 3.31/0.99  fof(f3,axiom,(
% 3.31/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f40,plain,(
% 3.31/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f3])).
% 3.31/0.99  
% 3.31/0.99  fof(f4,axiom,(
% 3.31/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f41,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f4])).
% 3.31/0.99  
% 3.31/0.99  fof(f71,plain,(
% 3.31/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 3.31/0.99    inference(definition_unfolding,[],[f40,f41])).
% 3.31/0.99  
% 3.31/0.99  fof(f72,plain,(
% 3.31/0.99    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 3.31/0.99    inference(definition_unfolding,[],[f39,f71])).
% 3.31/0.99  
% 3.31/0.99  fof(f84,plain,(
% 3.31/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 3.31/0.99    inference(definition_unfolding,[],[f68,f72])).
% 3.31/0.99  
% 3.31/0.99  fof(f16,axiom,(
% 3.31/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f28,plain,(
% 3.31/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.99    inference(ennf_transformation,[],[f16])).
% 3.31/0.99  
% 3.31/0.99  fof(f65,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f28])).
% 3.31/0.99  
% 3.31/0.99  fof(f15,axiom,(
% 3.31/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f27,plain,(
% 3.31/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.99    inference(ennf_transformation,[],[f15])).
% 3.31/0.99  
% 3.31/0.99  fof(f64,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f27])).
% 3.31/0.99  
% 3.31/0.99  fof(f6,axiom,(
% 3.31/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f34,plain,(
% 3.31/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.31/0.99    inference(nnf_transformation,[],[f6])).
% 3.31/0.99  
% 3.31/0.99  fof(f51,plain,(
% 3.31/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f34])).
% 3.31/0.99  
% 3.31/0.99  fof(f5,axiom,(
% 3.31/0.99    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f21,plain,(
% 3.31/0.99    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 3.31/0.99    inference(ennf_transformation,[],[f5])).
% 3.31/0.99  
% 3.31/0.99  fof(f32,plain,(
% 3.31/0.99    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 3.31/0.99    inference(nnf_transformation,[],[f21])).
% 3.31/0.99  
% 3.31/0.99  fof(f33,plain,(
% 3.31/0.99    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 3.31/0.99    inference(flattening,[],[f32])).
% 3.31/0.99  
% 3.31/0.99  fof(f42,plain,(
% 3.31/0.99    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f33])).
% 3.31/0.99  
% 3.31/0.99  fof(f81,plain,(
% 3.31/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 3.31/0.99    inference(definition_unfolding,[],[f42,f41,f71,f71,f71,f72,f72,f72,f41])).
% 3.31/0.99  
% 3.31/0.99  fof(f67,plain,(
% 3.31/0.99    v1_funct_1(sK3)),
% 3.31/0.99    inference(cnf_transformation,[],[f37])).
% 3.31/0.99  
% 3.31/0.99  fof(f70,plain,(
% 3.31/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 3.31/0.99    inference(cnf_transformation,[],[f37])).
% 3.31/0.99  
% 3.31/0.99  fof(f83,plain,(
% 3.31/0.99    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 3.31/0.99    inference(definition_unfolding,[],[f70,f72,f72])).
% 3.31/0.99  
% 3.31/0.99  fof(f14,axiom,(
% 3.31/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f26,plain,(
% 3.31/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.99    inference(ennf_transformation,[],[f14])).
% 3.31/0.99  
% 3.31/0.99  fof(f63,plain,(
% 3.31/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f26])).
% 3.31/0.99  
% 3.31/0.99  fof(f17,axiom,(
% 3.31/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f29,plain,(
% 3.31/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.31/0.99    inference(ennf_transformation,[],[f17])).
% 3.31/0.99  
% 3.31/0.99  fof(f66,plain,(
% 3.31/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f29])).
% 3.31/0.99  
% 3.31/0.99  fof(f7,axiom,(
% 3.31/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f22,plain,(
% 3.31/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 3.31/0.99    inference(ennf_transformation,[],[f7])).
% 3.31/0.99  
% 3.31/0.99  fof(f53,plain,(
% 3.31/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f22])).
% 3.31/0.99  
% 3.31/0.99  fof(f13,axiom,(
% 3.31/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f24,plain,(
% 3.31/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.31/0.99    inference(ennf_transformation,[],[f13])).
% 3.31/0.99  
% 3.31/0.99  fof(f25,plain,(
% 3.31/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.31/0.99    inference(flattening,[],[f24])).
% 3.31/0.99  
% 3.31/0.99  fof(f62,plain,(
% 3.31/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f25])).
% 3.31/0.99  
% 3.31/0.99  fof(f82,plain,(
% 3.31/0.99    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.31/0.99    inference(definition_unfolding,[],[f62,f72,f72])).
% 3.31/0.99  
% 3.31/0.99  fof(f9,axiom,(
% 3.31/0.99    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f23,plain,(
% 3.31/0.99    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.31/0.99    inference(ennf_transformation,[],[f9])).
% 3.31/0.99  
% 3.31/0.99  fof(f35,plain,(
% 3.31/0.99    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.31/0.99    inference(nnf_transformation,[],[f23])).
% 3.31/0.99  
% 3.31/0.99  fof(f56,plain,(
% 3.31/0.99    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f35])).
% 3.31/0.99  
% 3.31/0.99  fof(f11,axiom,(
% 3.31/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f59,plain,(
% 3.31/0.99    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.31/0.99    inference(cnf_transformation,[],[f11])).
% 3.31/0.99  
% 3.31/0.99  fof(f12,axiom,(
% 3.31/0.99    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f60,plain,(
% 3.31/0.99    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.31/0.99    inference(cnf_transformation,[],[f12])).
% 3.31/0.99  
% 3.31/0.99  fof(f8,axiom,(
% 3.31/0.99    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f54,plain,(
% 3.31/0.99    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f8])).
% 3.31/0.99  
% 3.31/0.99  fof(f55,plain,(
% 3.31/0.99    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f35])).
% 3.31/0.99  
% 3.31/0.99  fof(f10,axiom,(
% 3.31/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f57,plain,(
% 3.31/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.31/0.99    inference(cnf_transformation,[],[f10])).
% 3.31/0.99  
% 3.31/0.99  fof(f1,axiom,(
% 3.31/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.31/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.31/0.99  
% 3.31/0.99  fof(f38,plain,(
% 3.31/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.31/0.99    inference(cnf_transformation,[],[f1])).
% 3.31/0.99  
% 3.31/0.99  cnf(c_28,negated_conjecture,
% 3.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 3.31/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_879,plain,
% 3.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_24,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_882,plain,
% 3.31/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.31/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2187,plain,
% 3.31/0.99      ( k1_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3) = k1_relat_1(sK3) ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_879,c_882]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_23,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.31/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_883,plain,
% 3.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2205,plain,
% 3.31/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top
% 3.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_2187,c_883]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_31,plain,
% 3.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2318,plain,
% 3.31/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0))) = iProver_top ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_2205,c_31]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_11,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.31/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_891,plain,
% 3.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.31/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2323,plain,
% 3.31/0.99      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_2318,c_891]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_9,plain,
% 3.31/0.99      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 3.31/0.99      | k2_enumset1(X1,X1,X2,X3) = X0
% 3.31/0.99      | k2_enumset1(X1,X1,X1,X3) = X0
% 3.31/0.99      | k2_enumset1(X2,X2,X2,X3) = X0
% 3.31/0.99      | k2_enumset1(X1,X1,X1,X2) = X0
% 3.31/0.99      | k2_enumset1(X3,X3,X3,X3) = X0
% 3.31/0.99      | k2_enumset1(X2,X2,X2,X2) = X0
% 3.31/0.99      | k2_enumset1(X1,X1,X1,X1) = X0
% 3.31/0.99      | k1_xboole_0 = X0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_893,plain,
% 3.31/0.99      ( k2_enumset1(X0,X0,X1,X2) = X3
% 3.31/0.99      | k2_enumset1(X0,X0,X0,X2) = X3
% 3.31/0.99      | k2_enumset1(X1,X1,X1,X2) = X3
% 3.31/0.99      | k2_enumset1(X0,X0,X0,X1) = X3
% 3.31/0.99      | k2_enumset1(X2,X2,X2,X2) = X3
% 3.31/0.99      | k2_enumset1(X1,X1,X1,X1) = X3
% 3.31/0.99      | k2_enumset1(X0,X0,X0,X0) = X3
% 3.31/0.99      | k1_xboole_0 = X3
% 3.31/0.99      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3664,plain,
% 3.31/0.99      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_2323,c_893]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3713,plain,
% 3.31/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_3664,c_879]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1532,plain,
% 3.31/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.31/0.99      | r1_tarski(k1_relset_1(X1,X2,X0),X1) = iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_883,c_891]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3972,plain,
% 3.31/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | r1_tarski(k1_relset_1(k1_relat_1(sK3),sK1,sK3),k1_relat_1(sK3)) = iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_3713,c_1532]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3692,plain,
% 3.31/0.99      ( k2_enumset1(sK0,sK0,sK0,sK0) = X0
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | k1_xboole_0 = X0
% 3.31/0.99      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_3664,c_893]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5016,plain,
% 3.31/0.99      ( k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0)
% 3.31/0.99      | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_3972,c_3692]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5327,plain,
% 3.31/0.99      ( k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1))) = iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_5016,c_879]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5450,plain,
% 3.31/0.99      ( k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | r1_tarski(k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3),k1_relset_1(k1_relat_1(sK3),sK1,sK3)) = iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_5327,c_1532]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_5304,plain,
% 3.31/0.99      ( k2_enumset1(sK0,sK0,sK0,sK0) = X0
% 3.31/0.99      | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | k1_xboole_0 = X0
% 3.31/0.99      | r1_tarski(X0,k1_relset_1(k1_relat_1(sK3),sK1,sK3)) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_5016,c_893]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_6965,plain,
% 3.31/0.99      ( k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k2_enumset1(sK0,sK0,sK0,sK0)
% 3.31/0.99      | k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_5450,c_5304]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7016,plain,
% 3.31/0.99      ( k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | m1_subset_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3))) = iProver_top
% 3.31/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1))) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_6965,c_883]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7191,plain,
% 3.31/0.99      ( m1_subset_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3))) = iProver_top
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k1_xboole_0 ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_7016,c_5327]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7192,plain,
% 3.31/0.99      ( k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | m1_subset_1(k2_enumset1(sK0,sK0,sK0,sK0),k1_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3))) = iProver_top ),
% 3.31/0.99      inference(renaming,[status(thm)],[c_7191]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7199,plain,
% 3.31/0.99      ( k1_relset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relset_1(k1_relat_1(sK3),sK1,sK3) = k1_xboole_0
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | m1_subset_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3),k1_zfmisc_1(k1_relset_1(k1_relat_1(sK3),sK1,sK3))) = iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_5016,c_7192]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_29,negated_conjecture,
% 3.31/0.99      ( v1_funct_1(sK3) ),
% 3.31/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_30,plain,
% 3.31/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_26,negated_conjecture,
% 3.31/0.99      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.31/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_22,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | v1_relat_1(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1092,plain,
% 3.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.31/0.99      | v1_relat_1(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_22]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1093,plain,
% 3.31/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 3.31/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_1092]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_25,plain,
% 3.31/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.31/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.31/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1181,plain,
% 3.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.31/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1315,plain,
% 3.31/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 3.31/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1181]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_292,plain,
% 3.31/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.31/0.99      theory(equality) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1148,plain,
% 3.31/0.99      ( ~ r1_tarski(X0,X1)
% 3.31/0.99      | r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.31/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0
% 3.31/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_292]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1314,plain,
% 3.31/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.31/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 3.31/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.31/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0 ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1148]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1447,plain,
% 3.31/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 3.31/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 3.31/0.99      | k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2)
% 3.31/0.99      | k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1314]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_12,plain,
% 3.31/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1195,plain,
% 3.31/0.99      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
% 3.31/0.99      | ~ v1_relat_1(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1448,plain,
% 3.31/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 3.31/0.99      | ~ v1_relat_1(sK3) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_1195]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_21,plain,
% 3.31/0.99      ( ~ v1_funct_1(X0)
% 3.31/0.99      | ~ v1_relat_1(X0)
% 3.31/0.99      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 3.31/0.99      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_885,plain,
% 3.31/0.99      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
% 3.31/0.99      | k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
% 3.31/0.99      | v1_funct_1(X1) != iProver_top
% 3.31/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3702,plain,
% 3.31/0.99      ( k2_enumset1(k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0),k1_funct_1(X0,sK0)) = k2_relat_1(X0)
% 3.31/0.99      | k1_relat_1(X0) != k1_relat_1(sK3)
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | v1_funct_1(X0) != iProver_top
% 3.31/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_3664,c_885]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_7840,plain,
% 3.31/0.99      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.31/0.99      | k1_relat_1(sK3) = k1_xboole_0
% 3.31/0.99      | v1_funct_1(sK3) != iProver_top
% 3.31/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.31/0.99      inference(equality_resolution,[status(thm)],[c_3702]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_8173,plain,
% 3.31/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_7199,c_30,c_28,c_31,c_26,c_1092,c_1093,c_1315,c_1447,
% 3.31/0.99                 c_1448,c_7840]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_14,plain,
% 3.31/0.99      ( ~ r1_xboole_0(k1_relat_1(X0),X1)
% 3.31/0.99      | ~ v1_relat_1(X0)
% 3.31/0.99      | k9_relat_1(X0,X1) = k1_xboole_0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_889,plain,
% 3.31/0.99      ( k9_relat_1(X0,X1) = k1_xboole_0
% 3.31/0.99      | r1_xboole_0(k1_relat_1(X0),X1) != iProver_top
% 3.31/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_8207,plain,
% 3.31/0.99      ( k9_relat_1(sK3,X0) = k1_xboole_0
% 3.31/0.99      | r1_xboole_0(k1_xboole_0,X0) != iProver_top
% 3.31/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_8173,c_889]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_18,plain,
% 3.31/0.99      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_20,plain,
% 3.31/0.99      ( v1_relat_1(k6_relat_1(X0)) ),
% 3.31/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_886,plain,
% 3.31/0.99      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_1218,plain,
% 3.31/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_18,c_886]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_13,plain,
% 3.31/0.99      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_15,plain,
% 3.31/0.99      ( r1_xboole_0(k1_relat_1(X0),X1)
% 3.31/0.99      | ~ v1_relat_1(X0)
% 3.31/0.99      | k9_relat_1(X0,X1) != k1_xboole_0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_888,plain,
% 3.31/0.99      ( k9_relat_1(X0,X1) != k1_xboole_0
% 3.31/0.99      | r1_xboole_0(k1_relat_1(X0),X1) = iProver_top
% 3.31/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2447,plain,
% 3.31/0.99      ( r1_xboole_0(k1_relat_1(k1_xboole_0),X0) = iProver_top
% 3.31/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_13,c_888]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_17,plain,
% 3.31/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.31/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2448,plain,
% 3.31/0.99      ( r1_xboole_0(k1_xboole_0,X0) = iProver_top
% 3.31/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.31/0.99      inference(light_normalisation,[status(thm)],[c_2447,c_17]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_8263,plain,
% 3.31/0.99      ( k9_relat_1(sK3,X0) = k1_xboole_0 ),
% 3.31/0.99      inference(global_propositional_subsumption,
% 3.31/0.99                [status(thm)],
% 3.31/0.99                [c_8207,c_31,c_1093,c_1218,c_2448]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_881,plain,
% 3.31/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.31/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2674,plain,
% 3.31/0.99      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.31/0.99      inference(superposition,[status(thm)],[c_879,c_881]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_880,plain,
% 3.31/0.99      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_2915,plain,
% 3.31/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_2674,c_880]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_8268,plain,
% 3.31/0.99      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.31/0.99      inference(demodulation,[status(thm)],[c_8263,c_2915]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_0,plain,
% 3.31/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.31/0.99      inference(cnf_transformation,[],[f38]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3238,plain,
% 3.31/0.99      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.31/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(c_3241,plain,
% 3.31/0.99      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) = iProver_top ),
% 3.31/0.99      inference(predicate_to_equality,[status(thm)],[c_3238]) ).
% 3.31/0.99  
% 3.31/0.99  cnf(contradiction,plain,
% 3.31/0.99      ( $false ),
% 3.31/0.99      inference(minisat,[status(thm)],[c_8268,c_3241]) ).
% 3.31/0.99  
% 3.31/0.99  
% 3.31/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.31/0.99  
% 3.31/0.99  ------                               Statistics
% 3.31/0.99  
% 3.31/0.99  ------ Selected
% 3.31/0.99  
% 3.31/0.99  total_time:                             0.28
% 3.31/0.99  
%------------------------------------------------------------------------------
