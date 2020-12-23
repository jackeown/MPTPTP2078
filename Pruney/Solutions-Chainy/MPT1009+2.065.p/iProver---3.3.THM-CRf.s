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
% DateTime   : Thu Dec  3 12:05:41 EST 2020

% Result     : Theorem 0.63s
% Output     : CNFRefutation 0.63s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 657 expanded)
%              Number of clauses        :   57 ( 131 expanded)
%              Number of leaves         :   18 ( 169 expanded)
%              Depth                    :   20
%              Number of atoms          :  331 (1548 expanded)
%              Number of equality atoms :  193 ( 788 expanded)
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

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f31])).

fof(f37,plain,
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

fof(f38,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f37])).

fof(f65,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f41])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f68])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f65,f69])).

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

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(ennf_transformation,[],[f4])).

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
    inference(nnf_transformation,[],[f21])).

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
    inference(flattening,[],[f33])).

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
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
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
    inference(definition_unfolding,[],[f42,f41,f68,f68,f68,f69,f69,f69,f41])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f60,f69,f69])).

fof(f64,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f67,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f80,plain,(
    ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f67,f69,f69])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2586,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_333,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_20,c_13])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_337,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_333,c_19])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_337])).

cnf(c_2584,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_338])).

cnf(c_2970,plain,
    ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2586,c_2584])).

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
    inference(cnf_transformation,[],[f78])).

cnf(c_2596,plain,
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

cnf(c_4279,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2970,c_2596])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_314,plain,
    ( ~ v1_relat_1(X0)
    | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
    | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_25])).

cnf(c_315,plain,
    ( ~ v1_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_2585,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_27,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_316,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_2760,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2761,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2760])).

cnf(c_2773,plain,
    ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2585,c_27,c_316,c_2761])).

cnf(c_2774,plain,
    ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
    | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_2773])).

cnf(c_4359,plain,
    ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4279,c_2774])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2588,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3618,plain,
    ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2586,c_2588])).

cnf(c_22,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2587,plain,
    ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3756,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3618,c_2587])).

cnf(c_4659,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4359,c_3756])).

cnf(c_14,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2882,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4483,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2882])).

cnf(c_4484,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4483])).

cnf(c_4716,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4659,c_27,c_2761,c_4484])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2590,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4729,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4716,c_2590])).

cnf(c_2883,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2082,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2931,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_2082])).

cnf(c_2083,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3247,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_2083])).

cnf(c_3527,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3247])).

cnf(c_4523,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3527])).

cnf(c_4841,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4729,c_24,c_27,c_2760,c_2761,c_2883,c_2931,c_4484,c_4523,c_4659])).

cnf(c_4847,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4841,c_3756])).

cnf(c_15,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_4857,plain,
    ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4847,c_15])).

cnf(c_9,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_2595,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2593,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2918,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2595,c_2593])).

cnf(c_5005,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4857,c_2918])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:27:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 0.63/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.63/1.01  
% 0.63/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.63/1.01  
% 0.63/1.01  ------  iProver source info
% 0.63/1.01  
% 0.63/1.01  git: date: 2020-06-30 10:37:57 +0100
% 0.63/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.63/1.01  git: non_committed_changes: false
% 0.63/1.01  git: last_make_outside_of_git: false
% 0.63/1.01  
% 0.63/1.01  ------ 
% 0.63/1.01  
% 0.63/1.01  ------ Input Options
% 0.63/1.01  
% 0.63/1.01  --out_options                           all
% 0.63/1.01  --tptp_safe_out                         true
% 0.63/1.01  --problem_path                          ""
% 0.63/1.01  --include_path                          ""
% 0.63/1.01  --clausifier                            res/vclausify_rel
% 0.63/1.01  --clausifier_options                    --mode clausify
% 0.63/1.01  --stdin                                 false
% 0.63/1.01  --stats_out                             all
% 0.63/1.01  
% 0.63/1.01  ------ General Options
% 0.63/1.01  
% 0.63/1.01  --fof                                   false
% 0.63/1.01  --time_out_real                         305.
% 0.63/1.01  --time_out_virtual                      -1.
% 0.63/1.01  --symbol_type_check                     false
% 0.63/1.01  --clausify_out                          false
% 0.63/1.01  --sig_cnt_out                           false
% 0.63/1.01  --trig_cnt_out                          false
% 0.63/1.01  --trig_cnt_out_tolerance                1.
% 0.63/1.01  --trig_cnt_out_sk_spl                   false
% 0.63/1.01  --abstr_cl_out                          false
% 0.63/1.01  
% 0.63/1.01  ------ Global Options
% 0.63/1.01  
% 0.63/1.01  --schedule                              default
% 0.63/1.01  --add_important_lit                     false
% 0.63/1.01  --prop_solver_per_cl                    1000
% 0.63/1.01  --min_unsat_core                        false
% 0.63/1.01  --soft_assumptions                      false
% 0.63/1.01  --soft_lemma_size                       3
% 0.63/1.01  --prop_impl_unit_size                   0
% 0.63/1.01  --prop_impl_unit                        []
% 0.63/1.01  --share_sel_clauses                     true
% 0.63/1.01  --reset_solvers                         false
% 0.63/1.01  --bc_imp_inh                            [conj_cone]
% 0.63/1.01  --conj_cone_tolerance                   3.
% 0.63/1.01  --extra_neg_conj                        none
% 0.63/1.01  --large_theory_mode                     true
% 0.63/1.01  --prolific_symb_bound                   200
% 0.63/1.01  --lt_threshold                          2000
% 0.63/1.01  --clause_weak_htbl                      true
% 0.63/1.01  --gc_record_bc_elim                     false
% 0.63/1.01  
% 0.63/1.01  ------ Preprocessing Options
% 0.63/1.01  
% 0.63/1.01  --preprocessing_flag                    true
% 0.63/1.01  --time_out_prep_mult                    0.1
% 0.63/1.01  --splitting_mode                        input
% 0.63/1.01  --splitting_grd                         true
% 0.63/1.01  --splitting_cvd                         false
% 0.63/1.01  --splitting_cvd_svl                     false
% 0.63/1.01  --splitting_nvd                         32
% 0.63/1.01  --sub_typing                            true
% 0.63/1.01  --prep_gs_sim                           true
% 0.63/1.01  --prep_unflatten                        true
% 0.63/1.01  --prep_res_sim                          true
% 0.63/1.01  --prep_upred                            true
% 0.63/1.01  --prep_sem_filter                       exhaustive
% 0.63/1.01  --prep_sem_filter_out                   false
% 0.63/1.01  --pred_elim                             true
% 0.63/1.01  --res_sim_input                         true
% 0.63/1.01  --eq_ax_congr_red                       true
% 0.63/1.01  --pure_diseq_elim                       true
% 0.63/1.01  --brand_transform                       false
% 0.63/1.01  --non_eq_to_eq                          false
% 0.63/1.01  --prep_def_merge                        true
% 0.63/1.01  --prep_def_merge_prop_impl              false
% 0.63/1.01  --prep_def_merge_mbd                    true
% 0.63/1.01  --prep_def_merge_tr_red                 false
% 0.63/1.01  --prep_def_merge_tr_cl                  false
% 0.63/1.01  --smt_preprocessing                     true
% 0.63/1.01  --smt_ac_axioms                         fast
% 0.63/1.01  --preprocessed_out                      false
% 0.63/1.01  --preprocessed_stats                    false
% 0.63/1.01  
% 0.63/1.01  ------ Abstraction refinement Options
% 0.63/1.01  
% 0.63/1.01  --abstr_ref                             []
% 0.63/1.01  --abstr_ref_prep                        false
% 0.63/1.01  --abstr_ref_until_sat                   false
% 0.63/1.01  --abstr_ref_sig_restrict                funpre
% 0.63/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.63/1.01  --abstr_ref_under                       []
% 0.63/1.01  
% 0.63/1.01  ------ SAT Options
% 0.63/1.01  
% 0.63/1.01  --sat_mode                              false
% 0.63/1.01  --sat_fm_restart_options                ""
% 0.63/1.01  --sat_gr_def                            false
% 0.63/1.01  --sat_epr_types                         true
% 0.63/1.01  --sat_non_cyclic_types                  false
% 0.63/1.01  --sat_finite_models                     false
% 0.63/1.01  --sat_fm_lemmas                         false
% 0.63/1.01  --sat_fm_prep                           false
% 0.63/1.01  --sat_fm_uc_incr                        true
% 0.63/1.01  --sat_out_model                         small
% 0.63/1.01  --sat_out_clauses                       false
% 0.63/1.01  
% 0.63/1.01  ------ QBF Options
% 0.63/1.01  
% 0.63/1.01  --qbf_mode                              false
% 0.63/1.01  --qbf_elim_univ                         false
% 0.63/1.01  --qbf_dom_inst                          none
% 0.63/1.01  --qbf_dom_pre_inst                      false
% 0.63/1.01  --qbf_sk_in                             false
% 0.63/1.01  --qbf_pred_elim                         true
% 0.63/1.01  --qbf_split                             512
% 0.63/1.01  
% 0.63/1.01  ------ BMC1 Options
% 0.63/1.01  
% 0.63/1.01  --bmc1_incremental                      false
% 0.63/1.01  --bmc1_axioms                           reachable_all
% 0.63/1.01  --bmc1_min_bound                        0
% 0.63/1.01  --bmc1_max_bound                        -1
% 0.63/1.01  --bmc1_max_bound_default                -1
% 0.63/1.01  --bmc1_symbol_reachability              true
% 0.63/1.01  --bmc1_property_lemmas                  false
% 0.63/1.01  --bmc1_k_induction                      false
% 0.63/1.01  --bmc1_non_equiv_states                 false
% 0.63/1.01  --bmc1_deadlock                         false
% 0.63/1.01  --bmc1_ucm                              false
% 0.63/1.01  --bmc1_add_unsat_core                   none
% 0.63/1.01  --bmc1_unsat_core_children              false
% 0.63/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.63/1.01  --bmc1_out_stat                         full
% 0.63/1.01  --bmc1_ground_init                      false
% 0.63/1.01  --bmc1_pre_inst_next_state              false
% 0.63/1.01  --bmc1_pre_inst_state                   false
% 0.63/1.01  --bmc1_pre_inst_reach_state             false
% 0.63/1.01  --bmc1_out_unsat_core                   false
% 0.63/1.01  --bmc1_aig_witness_out                  false
% 0.63/1.01  --bmc1_verbose                          false
% 0.63/1.01  --bmc1_dump_clauses_tptp                false
% 0.63/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.63/1.01  --bmc1_dump_file                        -
% 0.63/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.63/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.63/1.01  --bmc1_ucm_extend_mode                  1
% 0.63/1.01  --bmc1_ucm_init_mode                    2
% 0.63/1.01  --bmc1_ucm_cone_mode                    none
% 0.63/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.63/1.01  --bmc1_ucm_relax_model                  4
% 0.63/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.63/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.63/1.01  --bmc1_ucm_layered_model                none
% 0.63/1.01  --bmc1_ucm_max_lemma_size               10
% 0.63/1.01  
% 0.63/1.01  ------ AIG Options
% 0.63/1.01  
% 0.63/1.01  --aig_mode                              false
% 0.63/1.01  
% 0.63/1.01  ------ Instantiation Options
% 0.63/1.01  
% 0.63/1.01  --instantiation_flag                    true
% 0.63/1.01  --inst_sos_flag                         false
% 0.63/1.01  --inst_sos_phase                        true
% 0.63/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.63/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.63/1.01  --inst_lit_sel_side                     num_symb
% 0.63/1.01  --inst_solver_per_active                1400
% 0.63/1.01  --inst_solver_calls_frac                1.
% 0.63/1.01  --inst_passive_queue_type               priority_queues
% 0.63/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.63/1.01  --inst_passive_queues_freq              [25;2]
% 0.63/1.01  --inst_dismatching                      true
% 0.63/1.01  --inst_eager_unprocessed_to_passive     true
% 0.63/1.01  --inst_prop_sim_given                   true
% 0.63/1.01  --inst_prop_sim_new                     false
% 0.63/1.01  --inst_subs_new                         false
% 0.63/1.01  --inst_eq_res_simp                      false
% 0.63/1.01  --inst_subs_given                       false
% 0.63/1.01  --inst_orphan_elimination               true
% 0.63/1.01  --inst_learning_loop_flag               true
% 0.63/1.01  --inst_learning_start                   3000
% 0.63/1.01  --inst_learning_factor                  2
% 0.63/1.01  --inst_start_prop_sim_after_learn       3
% 0.63/1.01  --inst_sel_renew                        solver
% 0.63/1.01  --inst_lit_activity_flag                true
% 0.63/1.01  --inst_restr_to_given                   false
% 0.63/1.01  --inst_activity_threshold               500
% 0.63/1.01  --inst_out_proof                        true
% 0.63/1.01  
% 0.63/1.01  ------ Resolution Options
% 0.63/1.01  
% 0.63/1.01  --resolution_flag                       true
% 0.63/1.01  --res_lit_sel                           adaptive
% 0.63/1.01  --res_lit_sel_side                      none
% 0.63/1.01  --res_ordering                          kbo
% 0.63/1.01  --res_to_prop_solver                    active
% 0.63/1.01  --res_prop_simpl_new                    false
% 0.63/1.01  --res_prop_simpl_given                  true
% 0.63/1.01  --res_passive_queue_type                priority_queues
% 0.63/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.63/1.01  --res_passive_queues_freq               [15;5]
% 0.63/1.01  --res_forward_subs                      full
% 0.63/1.01  --res_backward_subs                     full
% 0.63/1.01  --res_forward_subs_resolution           true
% 0.63/1.01  --res_backward_subs_resolution          true
% 0.63/1.01  --res_orphan_elimination                true
% 0.63/1.01  --res_time_limit                        2.
% 0.63/1.01  --res_out_proof                         true
% 0.63/1.01  
% 0.63/1.01  ------ Superposition Options
% 0.63/1.01  
% 0.63/1.01  --superposition_flag                    true
% 0.63/1.01  --sup_passive_queue_type                priority_queues
% 0.63/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.63/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.63/1.01  --demod_completeness_check              fast
% 0.63/1.01  --demod_use_ground                      true
% 0.63/1.01  --sup_to_prop_solver                    passive
% 0.63/1.01  --sup_prop_simpl_new                    true
% 0.63/1.01  --sup_prop_simpl_given                  true
% 0.63/1.01  --sup_fun_splitting                     false
% 0.63/1.01  --sup_smt_interval                      50000
% 0.63/1.01  
% 0.63/1.01  ------ Superposition Simplification Setup
% 0.63/1.01  
% 0.63/1.01  --sup_indices_passive                   []
% 0.63/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.63/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.63/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.63/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.63/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.63/1.01  --sup_full_bw                           [BwDemod]
% 0.63/1.01  --sup_immed_triv                        [TrivRules]
% 0.63/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.63/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.63/1.01  --sup_immed_bw_main                     []
% 0.63/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.63/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.63/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.63/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.63/1.01  
% 0.63/1.01  ------ Combination Options
% 0.63/1.01  
% 0.63/1.01  --comb_res_mult                         3
% 0.63/1.01  --comb_sup_mult                         2
% 0.63/1.01  --comb_inst_mult                        10
% 0.63/1.01  
% 0.63/1.01  ------ Debug Options
% 0.63/1.01  
% 0.63/1.01  --dbg_backtrace                         false
% 0.63/1.01  --dbg_dump_prop_clauses                 false
% 0.63/1.01  --dbg_dump_prop_clauses_file            -
% 0.63/1.01  --dbg_out_stat                          false
% 0.63/1.01  ------ Parsing...
% 0.63/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.63/1.01  
% 0.63/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.63/1.01  
% 0.63/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.63/1.01  
% 0.63/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.63/1.01  ------ Proving...
% 0.63/1.01  ------ Problem Properties 
% 0.63/1.01  
% 0.63/1.01  
% 0.63/1.01  clauses                                 23
% 0.63/1.01  conjectures                             3
% 0.63/1.01  EPR                                     1
% 0.63/1.01  Horn                                    22
% 0.63/1.01  unary                                   13
% 0.63/1.01  binary                                  6
% 0.63/1.01  lits                                    43
% 0.63/1.01  lits eq                                 17
% 0.63/1.01  fd_pure                                 0
% 0.63/1.01  fd_pseudo                               0
% 0.63/1.01  fd_cond                                 2
% 0.63/1.01  fd_pseudo_cond                          1
% 0.63/1.01  AC symbols                              0
% 0.63/1.01  
% 0.63/1.01  ------ Schedule dynamic 5 is on 
% 0.63/1.01  
% 0.63/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.63/1.01  
% 0.63/1.01  
% 0.63/1.01  ------ 
% 0.63/1.01  Current options:
% 0.63/1.01  ------ 
% 0.63/1.01  
% 0.63/1.01  ------ Input Options
% 0.63/1.01  
% 0.63/1.01  --out_options                           all
% 0.63/1.01  --tptp_safe_out                         true
% 0.63/1.01  --problem_path                          ""
% 0.63/1.01  --include_path                          ""
% 0.63/1.01  --clausifier                            res/vclausify_rel
% 0.63/1.01  --clausifier_options                    --mode clausify
% 0.63/1.01  --stdin                                 false
% 0.63/1.01  --stats_out                             all
% 0.63/1.01  
% 0.63/1.01  ------ General Options
% 0.63/1.01  
% 0.63/1.01  --fof                                   false
% 0.63/1.01  --time_out_real                         305.
% 0.63/1.01  --time_out_virtual                      -1.
% 0.63/1.01  --symbol_type_check                     false
% 0.63/1.01  --clausify_out                          false
% 0.63/1.01  --sig_cnt_out                           false
% 0.63/1.01  --trig_cnt_out                          false
% 0.63/1.01  --trig_cnt_out_tolerance                1.
% 0.63/1.01  --trig_cnt_out_sk_spl                   false
% 0.63/1.01  --abstr_cl_out                          false
% 0.63/1.01  
% 0.63/1.01  ------ Global Options
% 0.63/1.01  
% 0.63/1.01  --schedule                              default
% 0.63/1.01  --add_important_lit                     false
% 0.63/1.01  --prop_solver_per_cl                    1000
% 0.63/1.01  --min_unsat_core                        false
% 0.63/1.01  --soft_assumptions                      false
% 0.63/1.01  --soft_lemma_size                       3
% 0.63/1.01  --prop_impl_unit_size                   0
% 0.63/1.01  --prop_impl_unit                        []
% 0.63/1.01  --share_sel_clauses                     true
% 0.63/1.01  --reset_solvers                         false
% 0.63/1.01  --bc_imp_inh                            [conj_cone]
% 0.63/1.01  --conj_cone_tolerance                   3.
% 0.63/1.01  --extra_neg_conj                        none
% 0.63/1.01  --large_theory_mode                     true
% 0.63/1.01  --prolific_symb_bound                   200
% 0.63/1.01  --lt_threshold                          2000
% 0.63/1.01  --clause_weak_htbl                      true
% 0.63/1.01  --gc_record_bc_elim                     false
% 0.63/1.01  
% 0.63/1.01  ------ Preprocessing Options
% 0.63/1.01  
% 0.63/1.01  --preprocessing_flag                    true
% 0.63/1.01  --time_out_prep_mult                    0.1
% 0.63/1.01  --splitting_mode                        input
% 0.63/1.01  --splitting_grd                         true
% 0.63/1.01  --splitting_cvd                         false
% 0.63/1.01  --splitting_cvd_svl                     false
% 0.63/1.01  --splitting_nvd                         32
% 0.63/1.01  --sub_typing                            true
% 0.63/1.01  --prep_gs_sim                           true
% 0.63/1.01  --prep_unflatten                        true
% 0.63/1.01  --prep_res_sim                          true
% 0.63/1.01  --prep_upred                            true
% 0.63/1.01  --prep_sem_filter                       exhaustive
% 0.63/1.01  --prep_sem_filter_out                   false
% 0.63/1.01  --pred_elim                             true
% 0.63/1.01  --res_sim_input                         true
% 0.63/1.01  --eq_ax_congr_red                       true
% 0.63/1.01  --pure_diseq_elim                       true
% 0.63/1.01  --brand_transform                       false
% 0.63/1.01  --non_eq_to_eq                          false
% 0.63/1.01  --prep_def_merge                        true
% 0.63/1.01  --prep_def_merge_prop_impl              false
% 0.63/1.01  --prep_def_merge_mbd                    true
% 0.63/1.01  --prep_def_merge_tr_red                 false
% 0.63/1.01  --prep_def_merge_tr_cl                  false
% 0.63/1.01  --smt_preprocessing                     true
% 0.63/1.01  --smt_ac_axioms                         fast
% 0.63/1.01  --preprocessed_out                      false
% 0.63/1.01  --preprocessed_stats                    false
% 0.63/1.01  
% 0.63/1.01  ------ Abstraction refinement Options
% 0.63/1.01  
% 0.63/1.01  --abstr_ref                             []
% 0.63/1.01  --abstr_ref_prep                        false
% 0.63/1.01  --abstr_ref_until_sat                   false
% 0.63/1.01  --abstr_ref_sig_restrict                funpre
% 0.63/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 0.63/1.01  --abstr_ref_under                       []
% 0.63/1.01  
% 0.63/1.01  ------ SAT Options
% 0.63/1.01  
% 0.63/1.01  --sat_mode                              false
% 0.63/1.01  --sat_fm_restart_options                ""
% 0.63/1.01  --sat_gr_def                            false
% 0.63/1.01  --sat_epr_types                         true
% 0.63/1.01  --sat_non_cyclic_types                  false
% 0.63/1.01  --sat_finite_models                     false
% 0.63/1.01  --sat_fm_lemmas                         false
% 0.63/1.01  --sat_fm_prep                           false
% 0.63/1.01  --sat_fm_uc_incr                        true
% 0.63/1.01  --sat_out_model                         small
% 0.63/1.01  --sat_out_clauses                       false
% 0.63/1.01  
% 0.63/1.01  ------ QBF Options
% 0.63/1.01  
% 0.63/1.01  --qbf_mode                              false
% 0.63/1.01  --qbf_elim_univ                         false
% 0.63/1.01  --qbf_dom_inst                          none
% 0.63/1.01  --qbf_dom_pre_inst                      false
% 0.63/1.01  --qbf_sk_in                             false
% 0.63/1.01  --qbf_pred_elim                         true
% 0.63/1.01  --qbf_split                             512
% 0.63/1.01  
% 0.63/1.01  ------ BMC1 Options
% 0.63/1.01  
% 0.63/1.01  --bmc1_incremental                      false
% 0.63/1.01  --bmc1_axioms                           reachable_all
% 0.63/1.01  --bmc1_min_bound                        0
% 0.63/1.01  --bmc1_max_bound                        -1
% 0.63/1.01  --bmc1_max_bound_default                -1
% 0.63/1.01  --bmc1_symbol_reachability              true
% 0.63/1.01  --bmc1_property_lemmas                  false
% 0.63/1.01  --bmc1_k_induction                      false
% 0.63/1.01  --bmc1_non_equiv_states                 false
% 0.63/1.01  --bmc1_deadlock                         false
% 0.63/1.01  --bmc1_ucm                              false
% 0.63/1.01  --bmc1_add_unsat_core                   none
% 0.63/1.01  --bmc1_unsat_core_children              false
% 0.63/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 0.63/1.01  --bmc1_out_stat                         full
% 0.63/1.01  --bmc1_ground_init                      false
% 0.63/1.01  --bmc1_pre_inst_next_state              false
% 0.63/1.01  --bmc1_pre_inst_state                   false
% 0.63/1.01  --bmc1_pre_inst_reach_state             false
% 0.63/1.01  --bmc1_out_unsat_core                   false
% 0.63/1.01  --bmc1_aig_witness_out                  false
% 0.63/1.01  --bmc1_verbose                          false
% 0.63/1.01  --bmc1_dump_clauses_tptp                false
% 0.63/1.01  --bmc1_dump_unsat_core_tptp             false
% 0.63/1.01  --bmc1_dump_file                        -
% 0.63/1.01  --bmc1_ucm_expand_uc_limit              128
% 0.63/1.01  --bmc1_ucm_n_expand_iterations          6
% 0.63/1.01  --bmc1_ucm_extend_mode                  1
% 0.63/1.01  --bmc1_ucm_init_mode                    2
% 0.63/1.01  --bmc1_ucm_cone_mode                    none
% 0.63/1.01  --bmc1_ucm_reduced_relation_type        0
% 0.63/1.01  --bmc1_ucm_relax_model                  4
% 0.63/1.01  --bmc1_ucm_full_tr_after_sat            true
% 0.63/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 0.63/1.01  --bmc1_ucm_layered_model                none
% 0.63/1.01  --bmc1_ucm_max_lemma_size               10
% 0.63/1.01  
% 0.63/1.01  ------ AIG Options
% 0.63/1.01  
% 0.63/1.01  --aig_mode                              false
% 0.63/1.01  
% 0.63/1.01  ------ Instantiation Options
% 0.63/1.01  
% 0.63/1.01  --instantiation_flag                    true
% 0.63/1.01  --inst_sos_flag                         false
% 0.63/1.01  --inst_sos_phase                        true
% 0.63/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.63/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.63/1.01  --inst_lit_sel_side                     none
% 0.63/1.01  --inst_solver_per_active                1400
% 0.63/1.01  --inst_solver_calls_frac                1.
% 0.63/1.01  --inst_passive_queue_type               priority_queues
% 0.63/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.63/1.01  --inst_passive_queues_freq              [25;2]
% 0.63/1.01  --inst_dismatching                      true
% 0.63/1.01  --inst_eager_unprocessed_to_passive     true
% 0.63/1.01  --inst_prop_sim_given                   true
% 0.63/1.01  --inst_prop_sim_new                     false
% 0.63/1.01  --inst_subs_new                         false
% 0.63/1.01  --inst_eq_res_simp                      false
% 0.63/1.01  --inst_subs_given                       false
% 0.63/1.01  --inst_orphan_elimination               true
% 0.63/1.01  --inst_learning_loop_flag               true
% 0.63/1.01  --inst_learning_start                   3000
% 0.63/1.01  --inst_learning_factor                  2
% 0.63/1.01  --inst_start_prop_sim_after_learn       3
% 0.63/1.01  --inst_sel_renew                        solver
% 0.63/1.01  --inst_lit_activity_flag                true
% 0.63/1.01  --inst_restr_to_given                   false
% 0.63/1.01  --inst_activity_threshold               500
% 0.63/1.01  --inst_out_proof                        true
% 0.63/1.01  
% 0.63/1.01  ------ Resolution Options
% 0.63/1.01  
% 0.63/1.01  --resolution_flag                       false
% 0.63/1.01  --res_lit_sel                           adaptive
% 0.63/1.01  --res_lit_sel_side                      none
% 0.63/1.01  --res_ordering                          kbo
% 0.63/1.01  --res_to_prop_solver                    active
% 0.63/1.01  --res_prop_simpl_new                    false
% 0.63/1.01  --res_prop_simpl_given                  true
% 0.63/1.01  --res_passive_queue_type                priority_queues
% 0.63/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.63/1.01  --res_passive_queues_freq               [15;5]
% 0.63/1.01  --res_forward_subs                      full
% 0.63/1.01  --res_backward_subs                     full
% 0.63/1.01  --res_forward_subs_resolution           true
% 0.63/1.01  --res_backward_subs_resolution          true
% 0.63/1.01  --res_orphan_elimination                true
% 0.63/1.01  --res_time_limit                        2.
% 0.63/1.01  --res_out_proof                         true
% 0.63/1.01  
% 0.63/1.01  ------ Superposition Options
% 0.63/1.01  
% 0.63/1.01  --superposition_flag                    true
% 0.63/1.01  --sup_passive_queue_type                priority_queues
% 0.63/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.63/1.01  --sup_passive_queues_freq               [8;1;4]
% 0.63/1.01  --demod_completeness_check              fast
% 0.63/1.01  --demod_use_ground                      true
% 0.63/1.01  --sup_to_prop_solver                    passive
% 0.63/1.01  --sup_prop_simpl_new                    true
% 0.63/1.01  --sup_prop_simpl_given                  true
% 0.63/1.01  --sup_fun_splitting                     false
% 0.63/1.01  --sup_smt_interval                      50000
% 0.63/1.01  
% 0.63/1.01  ------ Superposition Simplification Setup
% 0.63/1.01  
% 0.63/1.01  --sup_indices_passive                   []
% 0.63/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.63/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.63/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.63/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 0.63/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.63/1.01  --sup_full_bw                           [BwDemod]
% 0.63/1.01  --sup_immed_triv                        [TrivRules]
% 0.63/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.63/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.63/1.01  --sup_immed_bw_main                     []
% 0.63/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.63/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 0.63/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.63/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.63/1.01  
% 0.63/1.01  ------ Combination Options
% 0.63/1.01  
% 0.63/1.01  --comb_res_mult                         3
% 0.63/1.01  --comb_sup_mult                         2
% 0.63/1.01  --comb_inst_mult                        10
% 0.63/1.01  
% 0.63/1.01  ------ Debug Options
% 0.63/1.01  
% 0.63/1.01  --dbg_backtrace                         false
% 0.63/1.01  --dbg_dump_prop_clauses                 false
% 0.63/1.01  --dbg_dump_prop_clauses_file            -
% 0.63/1.01  --dbg_out_stat                          false
% 0.63/1.01  
% 0.63/1.01  
% 0.63/1.01  
% 0.63/1.01  
% 0.63/1.01  ------ Proving...
% 0.63/1.01  
% 0.63/1.01  
% 0.63/1.01  % SZS status Theorem for theBenchmark.p
% 0.63/1.01  
% 0.63/1.01   Resolution empty clause
% 0.63/1.01  
% 0.63/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 0.63/1.01  
% 0.63/1.01  fof(f16,conjecture,(
% 0.63/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f17,negated_conjecture,(
% 0.63/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.63/1.02    inference(negated_conjecture,[],[f16])).
% 0.63/1.02  
% 0.63/1.02  fof(f18,plain,(
% 0.63/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.63/1.02    inference(pure_predicate_removal,[],[f17])).
% 0.63/1.02  
% 0.63/1.02  fof(f31,plain,(
% 0.63/1.02    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 0.63/1.02    inference(ennf_transformation,[],[f18])).
% 0.63/1.02  
% 0.63/1.02  fof(f32,plain,(
% 0.63/1.02    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 0.63/1.02    inference(flattening,[],[f31])).
% 0.63/1.02  
% 0.63/1.02  fof(f37,plain,(
% 0.63/1.02    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 0.63/1.02    introduced(choice_axiom,[])).
% 0.63/1.02  
% 0.63/1.02  fof(f38,plain,(
% 0.63/1.02    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 0.63/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f37])).
% 0.63/1.02  
% 0.63/1.02  fof(f65,plain,(
% 0.63/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.63/1.02    inference(cnf_transformation,[],[f38])).
% 0.63/1.02  
% 0.63/1.02  fof(f1,axiom,(
% 0.63/1.02    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f39,plain,(
% 0.63/1.02    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.63/1.02    inference(cnf_transformation,[],[f1])).
% 0.63/1.02  
% 0.63/1.02  fof(f2,axiom,(
% 0.63/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f40,plain,(
% 0.63/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.63/1.02    inference(cnf_transformation,[],[f2])).
% 0.63/1.02  
% 0.63/1.02  fof(f3,axiom,(
% 0.63/1.02    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f41,plain,(
% 0.63/1.02    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.63/1.02    inference(cnf_transformation,[],[f3])).
% 0.63/1.02  
% 0.63/1.02  fof(f68,plain,(
% 0.63/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.63/1.02    inference(definition_unfolding,[],[f40,f41])).
% 0.63/1.02  
% 0.63/1.02  fof(f69,plain,(
% 0.63/1.02    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.63/1.02    inference(definition_unfolding,[],[f39,f68])).
% 0.63/1.02  
% 0.63/1.02  fof(f81,plain,(
% 0.63/1.02    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 0.63/1.02    inference(definition_unfolding,[],[f65,f69])).
% 0.63/1.02  
% 0.63/1.02  fof(f14,axiom,(
% 0.63/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f19,plain,(
% 0.63/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.63/1.02    inference(pure_predicate_removal,[],[f14])).
% 0.63/1.02  
% 0.63/1.02  fof(f29,plain,(
% 0.63/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.63/1.02    inference(ennf_transformation,[],[f19])).
% 0.63/1.02  
% 0.63/1.02  fof(f62,plain,(
% 0.63/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.63/1.02    inference(cnf_transformation,[],[f29])).
% 0.63/1.02  
% 0.63/1.02  fof(f8,axiom,(
% 0.63/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f22,plain,(
% 0.63/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.63/1.02    inference(ennf_transformation,[],[f8])).
% 0.63/1.02  
% 0.63/1.02  fof(f36,plain,(
% 0.63/1.02    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.63/1.02    inference(nnf_transformation,[],[f22])).
% 0.63/1.02  
% 0.63/1.02  fof(f54,plain,(
% 0.63/1.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.63/1.02    inference(cnf_transformation,[],[f36])).
% 0.63/1.02  
% 0.63/1.02  fof(f13,axiom,(
% 0.63/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f28,plain,(
% 0.63/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.63/1.02    inference(ennf_transformation,[],[f13])).
% 0.63/1.02  
% 0.63/1.02  fof(f61,plain,(
% 0.63/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.63/1.02    inference(cnf_transformation,[],[f28])).
% 0.63/1.02  
% 0.63/1.02  fof(f4,axiom,(
% 0.63/1.02    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> ~(k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3))),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f21,plain,(
% 0.63/1.02    ! [X0,X1,X2,X3] : (r1_tarski(X3,k1_enumset1(X0,X1,X2)) <=> (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3))),
% 0.63/1.02    inference(ennf_transformation,[],[f4])).
% 0.63/1.02  
% 0.63/1.02  fof(f33,plain,(
% 0.63/1.02    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & ((k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3) | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 0.63/1.02    inference(nnf_transformation,[],[f21])).
% 0.63/1.02  
% 0.63/1.02  fof(f34,plain,(
% 0.63/1.02    ! [X0,X1,X2,X3] : ((r1_tarski(X3,k1_enumset1(X0,X1,X2)) | (k1_enumset1(X0,X1,X2) != X3 & k2_tarski(X0,X2) != X3 & k2_tarski(X1,X2) != X3 & k2_tarski(X0,X1) != X3 & k1_tarski(X2) != X3 & k1_tarski(X1) != X3 & k1_tarski(X0) != X3 & k1_xboole_0 != X3)) & (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))))),
% 0.63/1.02    inference(flattening,[],[f33])).
% 0.63/1.02  
% 0.63/1.02  fof(f42,plain,(
% 0.63/1.02    ( ! [X2,X0,X3,X1] : (k1_enumset1(X0,X1,X2) = X3 | k2_tarski(X0,X2) = X3 | k2_tarski(X1,X2) = X3 | k2_tarski(X0,X1) = X3 | k1_tarski(X2) = X3 | k1_tarski(X1) = X3 | k1_tarski(X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k1_enumset1(X0,X1,X2))) )),
% 0.63/1.02    inference(cnf_transformation,[],[f34])).
% 0.63/1.02  
% 0.63/1.02  fof(f78,plain,(
% 0.63/1.02    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X0,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X2) = X3 | k2_enumset1(X1,X1,X1,X2) = X3 | k2_enumset1(X0,X0,X0,X1) = X3 | k2_enumset1(X2,X2,X2,X2) = X3 | k2_enumset1(X1,X1,X1,X1) = X3 | k2_enumset1(X0,X0,X0,X0) = X3 | k1_xboole_0 = X3 | ~r1_tarski(X3,k2_enumset1(X0,X0,X1,X2))) )),
% 0.63/1.02    inference(definition_unfolding,[],[f42,f41,f68,f68,f68,f69,f69,f69,f41])).
% 0.63/1.02  
% 0.63/1.02  fof(f12,axiom,(
% 0.63/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f26,plain,(
% 0.63/1.02    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.63/1.02    inference(ennf_transformation,[],[f12])).
% 0.63/1.02  
% 0.63/1.02  fof(f27,plain,(
% 0.63/1.02    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.63/1.02    inference(flattening,[],[f26])).
% 0.63/1.02  
% 0.63/1.02  fof(f60,plain,(
% 0.63/1.02    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.63/1.02    inference(cnf_transformation,[],[f27])).
% 0.63/1.02  
% 0.63/1.02  fof(f79,plain,(
% 0.63/1.02    ( ! [X0,X1] : (k2_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.63/1.02    inference(definition_unfolding,[],[f60,f69,f69])).
% 0.63/1.02  
% 0.63/1.02  fof(f64,plain,(
% 0.63/1.02    v1_funct_1(sK3)),
% 0.63/1.02    inference(cnf_transformation,[],[f38])).
% 0.63/1.02  
% 0.63/1.02  fof(f15,axiom,(
% 0.63/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f30,plain,(
% 0.63/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.63/1.02    inference(ennf_transformation,[],[f15])).
% 0.63/1.02  
% 0.63/1.02  fof(f63,plain,(
% 0.63/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.63/1.02    inference(cnf_transformation,[],[f30])).
% 0.63/1.02  
% 0.63/1.02  fof(f67,plain,(
% 0.63/1.02    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.63/1.02    inference(cnf_transformation,[],[f38])).
% 0.63/1.02  
% 0.63/1.02  fof(f80,plain,(
% 0.63/1.02    ~r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.63/1.02    inference(definition_unfolding,[],[f67,f69,f69])).
% 0.63/1.02  
% 0.63/1.02  fof(f9,axiom,(
% 0.63/1.02    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f23,plain,(
% 0.63/1.02    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.63/1.02    inference(ennf_transformation,[],[f9])).
% 0.63/1.02  
% 0.63/1.02  fof(f56,plain,(
% 0.63/1.02    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.63/1.02    inference(cnf_transformation,[],[f23])).
% 0.63/1.02  
% 0.63/1.02  fof(f11,axiom,(
% 0.63/1.02    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f24,plain,(
% 0.63/1.02    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.63/1.02    inference(ennf_transformation,[],[f11])).
% 0.63/1.02  
% 0.63/1.02  fof(f25,plain,(
% 0.63/1.02    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.63/1.02    inference(flattening,[],[f24])).
% 0.63/1.02  
% 0.63/1.02  fof(f58,plain,(
% 0.63/1.02    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.63/1.02    inference(cnf_transformation,[],[f25])).
% 0.63/1.02  
% 0.63/1.02  fof(f10,axiom,(
% 0.63/1.02    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f57,plain,(
% 0.63/1.02    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 0.63/1.02    inference(cnf_transformation,[],[f10])).
% 0.63/1.02  
% 0.63/1.02  fof(f5,axiom,(
% 0.63/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f51,plain,(
% 0.63/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.63/1.02    inference(cnf_transformation,[],[f5])).
% 0.63/1.02  
% 0.63/1.02  fof(f6,axiom,(
% 0.63/1.02    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.63/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.63/1.02  
% 0.63/1.02  fof(f35,plain,(
% 0.63/1.02    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.63/1.02    inference(nnf_transformation,[],[f6])).
% 0.63/1.02  
% 0.63/1.02  fof(f52,plain,(
% 0.63/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.63/1.02    inference(cnf_transformation,[],[f35])).
% 0.63/1.02  
% 0.63/1.02  cnf(c_24,negated_conjecture,
% 0.63/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
% 0.63/1.02      inference(cnf_transformation,[],[f81]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2586,plain,
% 0.63/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_20,plain,
% 0.63/1.02      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.63/1.02      inference(cnf_transformation,[],[f62]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_13,plain,
% 0.63/1.02      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 0.63/1.02      inference(cnf_transformation,[],[f54]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_333,plain,
% 0.63/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.63/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 0.63/1.02      | ~ v1_relat_1(X0) ),
% 0.63/1.02      inference(resolution,[status(thm)],[c_20,c_13]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_19,plain,
% 0.63/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 0.63/1.02      inference(cnf_transformation,[],[f61]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_337,plain,
% 0.63/1.02      ( r1_tarski(k1_relat_1(X0),X1)
% 0.63/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.63/1.02      inference(global_propositional_subsumption,[status(thm)],[c_333,c_19]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_338,plain,
% 0.63/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.63/1.02      | r1_tarski(k1_relat_1(X0),X1) ),
% 0.63/1.02      inference(renaming,[status(thm)],[c_337]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2584,plain,
% 0.63/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 0.63/1.02      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_338]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2970,plain,
% 0.63/1.02      ( r1_tarski(k1_relat_1(sK3),k2_enumset1(sK0,sK0,sK0,sK0)) = iProver_top ),
% 0.63/1.02      inference(superposition,[status(thm)],[c_2586,c_2584]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_8,plain,
% 0.63/1.02      ( ~ r1_tarski(X0,k2_enumset1(X1,X1,X2,X3))
% 0.63/1.02      | k2_enumset1(X1,X1,X2,X3) = X0
% 0.63/1.02      | k2_enumset1(X1,X1,X1,X3) = X0
% 0.63/1.02      | k2_enumset1(X2,X2,X2,X3) = X0
% 0.63/1.02      | k2_enumset1(X1,X1,X1,X2) = X0
% 0.63/1.02      | k2_enumset1(X3,X3,X3,X3) = X0
% 0.63/1.02      | k2_enumset1(X2,X2,X2,X2) = X0
% 0.63/1.02      | k2_enumset1(X1,X1,X1,X1) = X0
% 0.63/1.02      | k1_xboole_0 = X0 ),
% 0.63/1.02      inference(cnf_transformation,[],[f78]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2596,plain,
% 0.63/1.02      ( k2_enumset1(X0,X0,X1,X2) = X3
% 0.63/1.02      | k2_enumset1(X0,X0,X0,X2) = X3
% 0.63/1.02      | k2_enumset1(X1,X1,X1,X2) = X3
% 0.63/1.02      | k2_enumset1(X0,X0,X0,X1) = X3
% 0.63/1.02      | k2_enumset1(X2,X2,X2,X2) = X3
% 0.63/1.02      | k2_enumset1(X1,X1,X1,X1) = X3
% 0.63/1.02      | k2_enumset1(X0,X0,X0,X0) = X3
% 0.63/1.02      | k1_xboole_0 = X3
% 0.63/1.02      | r1_tarski(X3,k2_enumset1(X0,X0,X1,X2)) != iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_4279,plain,
% 0.63/1.02      ( k2_enumset1(sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 0.63/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 0.63/1.02      inference(superposition,[status(thm)],[c_2970,c_2596]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_18,plain,
% 0.63/1.02      ( ~ v1_funct_1(X0)
% 0.63/1.02      | ~ v1_relat_1(X0)
% 0.63/1.02      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 0.63/1.02      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 0.63/1.02      inference(cnf_transformation,[],[f79]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_25,negated_conjecture,
% 0.63/1.02      ( v1_funct_1(sK3) ),
% 0.63/1.02      inference(cnf_transformation,[],[f64]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_314,plain,
% 0.63/1.02      ( ~ v1_relat_1(X0)
% 0.63/1.02      | k2_enumset1(X1,X1,X1,X1) != k1_relat_1(X0)
% 0.63/1.02      | k2_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 0.63/1.02      | sK3 != X0 ),
% 0.63/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_25]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_315,plain,
% 0.63/1.02      ( ~ v1_relat_1(sK3)
% 0.63/1.02      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 0.63/1.02      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 0.63/1.02      inference(unflattening,[status(thm)],[c_314]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2585,plain,
% 0.63/1.02      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 0.63/1.02      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 0.63/1.02      | v1_relat_1(sK3) != iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_27,plain,
% 0.63/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_316,plain,
% 0.63/1.02      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 0.63/1.02      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 0.63/1.02      | v1_relat_1(sK3) != iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2760,plain,
% 0.63/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))
% 0.63/1.02      | v1_relat_1(sK3) ),
% 0.63/1.02      inference(instantiation,[status(thm)],[c_19]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2761,plain,
% 0.63/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 0.63/1.02      | v1_relat_1(sK3) = iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_2760]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2773,plain,
% 0.63/1.02      ( k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 0.63/1.02      | k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 0.63/1.02      inference(global_propositional_subsumption,
% 0.63/1.02                [status(thm)],
% 0.63/1.02                [c_2585,c_27,c_316,c_2761]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2774,plain,
% 0.63/1.02      ( k2_enumset1(X0,X0,X0,X0) != k1_relat_1(sK3)
% 0.63/1.02      | k2_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 0.63/1.02      inference(renaming,[status(thm)],[c_2773]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_4359,plain,
% 0.63/1.02      ( k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 0.63/1.02      | k1_relat_1(sK3) = k1_xboole_0 ),
% 0.63/1.02      inference(superposition,[status(thm)],[c_4279,c_2774]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_21,plain,
% 0.63/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.63/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 0.63/1.02      inference(cnf_transformation,[],[f63]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2588,plain,
% 0.63/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 0.63/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_3618,plain,
% 0.63/1.02      ( k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 0.63/1.02      inference(superposition,[status(thm)],[c_2586,c_2588]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_22,negated_conjecture,
% 0.63/1.02      ( ~ r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 0.63/1.02      inference(cnf_transformation,[],[f80]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2587,plain,
% 0.63/1.02      ( r1_tarski(k7_relset_1(k2_enumset1(sK0,sK0,sK0,sK0),sK1,sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_3756,plain,
% 0.63/1.02      ( r1_tarski(k9_relat_1(sK3,sK2),k2_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 0.63/1.02      inference(demodulation,[status(thm)],[c_3618,c_2587]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_4659,plain,
% 0.63/1.02      ( k1_relat_1(sK3) = k1_xboole_0
% 0.63/1.02      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 0.63/1.02      inference(superposition,[status(thm)],[c_4359,c_3756]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_14,plain,
% 0.63/1.02      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 0.63/1.02      inference(cnf_transformation,[],[f56]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2882,plain,
% 0.63/1.02      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 0.63/1.02      inference(instantiation,[status(thm)],[c_14]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_4483,plain,
% 0.63/1.02      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 0.63/1.02      inference(instantiation,[status(thm)],[c_2882]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_4484,plain,
% 0.63/1.02      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) = iProver_top
% 0.63/1.02      | v1_relat_1(sK3) != iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_4483]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_4716,plain,
% 0.63/1.02      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 0.63/1.02      inference(global_propositional_subsumption,
% 0.63/1.02                [status(thm)],
% 0.63/1.02                [c_4659,c_27,c_2761,c_4484]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_17,plain,
% 0.63/1.02      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 0.63/1.02      inference(cnf_transformation,[],[f58]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2590,plain,
% 0.63/1.02      ( k1_relat_1(X0) != k1_xboole_0
% 0.63/1.02      | k1_xboole_0 = X0
% 0.63/1.02      | v1_relat_1(X0) != iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_4729,plain,
% 0.63/1.02      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 0.63/1.02      inference(superposition,[status(thm)],[c_4716,c_2590]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2883,plain,
% 0.63/1.02      ( ~ v1_relat_1(sK3)
% 0.63/1.02      | k1_relat_1(sK3) != k1_xboole_0
% 0.63/1.02      | k1_xboole_0 = sK3 ),
% 0.63/1.02      inference(instantiation,[status(thm)],[c_17]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2082,plain,( X0 = X0 ),theory(equality) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2931,plain,
% 0.63/1.02      ( sK3 = sK3 ),
% 0.63/1.02      inference(instantiation,[status(thm)],[c_2082]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2083,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_3247,plain,
% 0.63/1.02      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 0.63/1.02      inference(instantiation,[status(thm)],[c_2083]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_3527,plain,
% 0.63/1.02      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 0.63/1.02      inference(instantiation,[status(thm)],[c_3247]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_4523,plain,
% 0.63/1.02      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 0.63/1.02      inference(instantiation,[status(thm)],[c_3527]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_4841,plain,
% 0.63/1.02      ( sK3 = k1_xboole_0 ),
% 0.63/1.02      inference(global_propositional_subsumption,
% 0.63/1.02                [status(thm)],
% 0.63/1.02                [c_4729,c_24,c_27,c_2760,c_2761,c_2883,c_2931,c_4484,c_4523,
% 0.63/1.02                 c_4659]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_4847,plain,
% 0.63/1.02      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.63/1.02      inference(demodulation,[status(thm)],[c_4841,c_3756]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_15,plain,
% 0.63/1.02      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.63/1.02      inference(cnf_transformation,[],[f57]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_4857,plain,
% 0.63/1.02      ( r1_tarski(k1_xboole_0,k2_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.63/1.02      inference(demodulation,[status(thm)],[c_4847,c_15]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_9,plain,
% 0.63/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 0.63/1.02      inference(cnf_transformation,[],[f51]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2595,plain,
% 0.63/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_11,plain,
% 0.63/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 0.63/1.02      inference(cnf_transformation,[],[f52]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2593,plain,
% 0.63/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 0.63/1.02      | r1_tarski(X0,X1) = iProver_top ),
% 0.63/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_2918,plain,
% 0.63/1.02      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 0.63/1.02      inference(superposition,[status(thm)],[c_2595,c_2593]) ).
% 0.63/1.02  
% 0.63/1.02  cnf(c_5005,plain,
% 0.63/1.02      ( $false ),
% 0.63/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_4857,c_2918]) ).
% 0.63/1.02  
% 0.63/1.02  
% 0.63/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 0.63/1.02  
% 0.63/1.02  ------                               Statistics
% 0.63/1.02  
% 0.63/1.02  ------ General
% 0.63/1.02  
% 0.63/1.02  abstr_ref_over_cycles:                  0
% 0.63/1.02  abstr_ref_under_cycles:                 0
% 0.63/1.02  gc_basic_clause_elim:                   0
% 0.63/1.02  forced_gc_time:                         0
% 0.63/1.02  parsing_time:                           0.008
% 0.63/1.02  unif_index_cands_time:                  0.
% 0.63/1.02  unif_index_add_time:                    0.
% 0.63/1.02  orderings_time:                         0.
% 0.63/1.02  out_proof_time:                         0.01
% 0.63/1.02  total_time:                             0.149
% 0.63/1.02  num_of_symbols:                         49
% 0.63/1.02  num_of_terms:                           4783
% 0.63/1.02  
% 0.63/1.02  ------ Preprocessing
% 0.63/1.02  
% 0.63/1.02  num_of_splits:                          0
% 0.63/1.02  num_of_split_atoms:                     0
% 0.63/1.02  num_of_reused_defs:                     0
% 0.63/1.02  num_eq_ax_congr_red:                    8
% 0.63/1.02  num_of_sem_filtered_clauses:            1
% 0.63/1.02  num_of_subtypes:                        0
% 0.63/1.02  monotx_restored_types:                  0
% 0.63/1.02  sat_num_of_epr_types:                   0
% 0.63/1.02  sat_num_of_non_cyclic_types:            0
% 0.63/1.02  sat_guarded_non_collapsed_types:        0
% 0.63/1.02  num_pure_diseq_elim:                    0
% 0.63/1.02  simp_replaced_by:                       0
% 0.63/1.02  res_preprocessed:                       122
% 0.63/1.02  prep_upred:                             0
% 0.63/1.02  prep_unflattend:                        97
% 0.63/1.02  smt_new_axioms:                         0
% 0.63/1.02  pred_elim_cands:                        3
% 0.63/1.02  pred_elim:                              2
% 0.63/1.02  pred_elim_cl:                           3
% 0.63/1.02  pred_elim_cycles:                       8
% 0.63/1.02  merged_defs:                            8
% 0.63/1.02  merged_defs_ncl:                        0
% 0.63/1.02  bin_hyper_res:                          8
% 0.63/1.02  prep_cycles:                            4
% 0.63/1.02  pred_elim_time:                         0.021
% 0.63/1.02  splitting_time:                         0.
% 0.63/1.02  sem_filter_time:                        0.
% 0.63/1.02  monotx_time:                            0.001
% 0.63/1.02  subtype_inf_time:                       0.
% 0.63/1.02  
% 0.63/1.02  ------ Problem properties
% 0.63/1.02  
% 0.63/1.02  clauses:                                23
% 0.63/1.02  conjectures:                            3
% 0.63/1.02  epr:                                    1
% 0.63/1.02  horn:                                   22
% 0.63/1.02  ground:                                 3
% 0.63/1.02  unary:                                  13
% 0.63/1.02  binary:                                 6
% 0.63/1.02  lits:                                   43
% 0.63/1.02  lits_eq:                                17
% 0.63/1.02  fd_pure:                                0
% 0.63/1.02  fd_pseudo:                              0
% 0.63/1.02  fd_cond:                                2
% 0.63/1.02  fd_pseudo_cond:                         1
% 0.63/1.02  ac_symbols:                             0
% 0.63/1.02  
% 0.63/1.02  ------ Propositional Solver
% 0.63/1.02  
% 0.63/1.02  prop_solver_calls:                      28
% 0.63/1.02  prop_fast_solver_calls:                 919
% 0.63/1.02  smt_solver_calls:                       0
% 0.63/1.02  smt_fast_solver_calls:                  0
% 0.63/1.02  prop_num_of_clauses:                    1187
% 0.63/1.02  prop_preprocess_simplified:             5215
% 0.63/1.02  prop_fo_subsumed:                       6
% 0.63/1.02  prop_solver_time:                       0.
% 0.63/1.02  smt_solver_time:                        0.
% 0.63/1.02  smt_fast_solver_time:                   0.
% 0.63/1.02  prop_fast_solver_time:                  0.
% 0.63/1.02  prop_unsat_core_time:                   0.
% 0.63/1.02  
% 0.63/1.02  ------ QBF
% 0.63/1.02  
% 0.63/1.02  qbf_q_res:                              0
% 0.63/1.02  qbf_num_tautologies:                    0
% 0.63/1.02  qbf_prep_cycles:                        0
% 0.63/1.02  
% 0.63/1.02  ------ BMC1
% 0.63/1.02  
% 0.63/1.02  bmc1_current_bound:                     -1
% 0.63/1.02  bmc1_last_solved_bound:                 -1
% 0.63/1.02  bmc1_unsat_core_size:                   -1
% 0.63/1.02  bmc1_unsat_core_parents_size:           -1
% 0.63/1.02  bmc1_merge_next_fun:                    0
% 0.63/1.02  bmc1_unsat_core_clauses_time:           0.
% 0.63/1.02  
% 0.63/1.02  ------ Instantiation
% 0.63/1.02  
% 0.63/1.02  inst_num_of_clauses:                    358
% 0.63/1.02  inst_num_in_passive:                    80
% 0.63/1.02  inst_num_in_active:                     226
% 0.63/1.02  inst_num_in_unprocessed:                52
% 0.63/1.02  inst_num_of_loops:                      240
% 0.63/1.02  inst_num_of_learning_restarts:          0
% 0.63/1.02  inst_num_moves_active_passive:          11
% 0.63/1.02  inst_lit_activity:                      0
% 0.63/1.02  inst_lit_activity_moves:                0
% 0.63/1.02  inst_num_tautologies:                   0
% 0.63/1.02  inst_num_prop_implied:                  0
% 0.63/1.02  inst_num_existing_simplified:           0
% 0.63/1.02  inst_num_eq_res_simplified:             0
% 0.63/1.02  inst_num_child_elim:                    0
% 0.63/1.02  inst_num_of_dismatching_blockings:      297
% 0.63/1.02  inst_num_of_non_proper_insts:           362
% 0.63/1.02  inst_num_of_duplicates:                 0
% 0.63/1.02  inst_inst_num_from_inst_to_res:         0
% 0.63/1.02  inst_dismatching_checking_time:         0.
% 0.63/1.02  
% 0.63/1.02  ------ Resolution
% 0.63/1.02  
% 0.63/1.02  res_num_of_clauses:                     0
% 0.63/1.02  res_num_in_passive:                     0
% 0.63/1.02  res_num_in_active:                      0
% 0.63/1.02  res_num_of_loops:                       126
% 0.63/1.02  res_forward_subset_subsumed:            43
% 0.63/1.02  res_backward_subset_subsumed:           0
% 0.63/1.02  res_forward_subsumed:                   2
% 0.63/1.02  res_backward_subsumed:                  0
% 0.63/1.02  res_forward_subsumption_resolution:     0
% 0.63/1.02  res_backward_subsumption_resolution:    0
% 0.63/1.02  res_clause_to_clause_subsumption:       370
% 0.63/1.02  res_orphan_elimination:                 0
% 0.63/1.02  res_tautology_del:                      72
% 0.63/1.02  res_num_eq_res_simplified:              0
% 0.63/1.02  res_num_sel_changes:                    0
% 0.63/1.02  res_moves_from_active_to_pass:          0
% 0.63/1.02  
% 0.63/1.02  ------ Superposition
% 0.63/1.02  
% 0.63/1.02  sup_time_total:                         0.
% 0.63/1.02  sup_time_generating:                    0.
% 0.63/1.02  sup_time_sim_full:                      0.
% 0.63/1.02  sup_time_sim_immed:                     0.
% 0.63/1.02  
% 0.63/1.02  sup_num_of_clauses:                     41
% 0.63/1.02  sup_num_in_active:                      30
% 0.63/1.02  sup_num_in_passive:                     11
% 0.63/1.02  sup_num_of_loops:                       47
% 0.63/1.02  sup_fw_superposition:                   33
% 0.63/1.02  sup_bw_superposition:                   54
% 0.63/1.02  sup_immediate_simplified:               19
% 0.63/1.02  sup_given_eliminated:                   0
% 0.63/1.02  comparisons_done:                       0
% 0.63/1.02  comparisons_avoided:                    6
% 0.63/1.02  
% 0.63/1.02  ------ Simplifications
% 0.63/1.02  
% 0.63/1.02  
% 0.63/1.02  sim_fw_subset_subsumed:                 3
% 0.63/1.02  sim_bw_subset_subsumed:                 12
% 0.63/1.02  sim_fw_subsumed:                        13
% 0.63/1.02  sim_bw_subsumed:                        1
% 0.63/1.02  sim_fw_subsumption_res:                 1
% 0.63/1.02  sim_bw_subsumption_res:                 0
% 0.63/1.02  sim_tautology_del:                      1
% 0.63/1.02  sim_eq_tautology_del:                   10
% 0.63/1.02  sim_eq_res_simp:                        0
% 0.63/1.02  sim_fw_demodulated:                     2
% 0.63/1.02  sim_bw_demodulated:                     13
% 0.63/1.02  sim_light_normalised:                   1
% 0.63/1.02  sim_joinable_taut:                      0
% 0.63/1.02  sim_joinable_simp:                      0
% 0.63/1.02  sim_ac_normalised:                      0
% 0.63/1.02  sim_smt_subsumption:                    0
% 0.63/1.02  
%------------------------------------------------------------------------------
