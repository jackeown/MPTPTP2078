%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:05:53 EST 2020

% Result     : Theorem 2.64s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 835 expanded)
%              Number of clauses        :   93 ( 168 expanded)
%              Number of leaves         :   27 ( 213 expanded)
%              Depth                    :   24
%              Number of atoms          :  417 (1651 expanded)
%              Number of equality atoms :  223 ( 823 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f24,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f26,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f49,plain,
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

fof(f50,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f61,f62])).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f60,f86])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f59,f87])).

fof(f89,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f58,f88])).

fof(f90,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f57,f89])).

fof(f91,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f56,f90])).

fof(f97,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f83,f91])).

fof(f15,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f44])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f63,f91,f91])).

fof(f85,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f96,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f85,f91,f91])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f79,f91,f91])).

fof(f82,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f46])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f102,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f20,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f77,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_22,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_315,plain,
    ( v4_relat_1(X0,X1)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_26])).

cnf(c_316,plain,
    ( v4_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_315])).

cnf(c_366,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | X2 != X1
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_316])).

cnf(c_367,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_789,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_14,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_52,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_368,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_291,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_26])).

cnf(c_292,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_924,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_925,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_924])).

cnf(c_1135,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_789,c_52,c_368,c_925])).

cnf(c_1136,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_1135])).

cnf(c_1143,plain,
    ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1136])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_799,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2793,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1143,c_799])).

cnf(c_24,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_272,plain,
    ( ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_273,plain,
    ( ~ v1_relat_1(sK3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_272])).

cnf(c_274,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_273])).

cnf(c_276,plain,
    ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_274])).

cnf(c_507,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_929,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_507])).

cnf(c_792,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_292])).

cnf(c_995,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_792])).

cnf(c_996,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_995])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_306,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_26])).

cnf(c_307,plain,
    ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_930,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_307])).

cnf(c_1057,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2)
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_930])).

cnf(c_1238,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1239,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1238])).

cnf(c_15,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1739,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2281,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1739])).

cnf(c_509,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_986,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1
    | k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_509])).

cnf(c_1058,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
    | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0
    | k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_986])).

cnf(c_2282,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
    | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
    | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3)
    | k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2) ),
    inference(instantiation,[status(thm)],[c_1058])).

cnf(c_3109,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2793,c_24,c_276,c_929,c_995,c_996,c_1057,c_1238,c_1239,c_2281,c_2282])).

cnf(c_798,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1831,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_798,c_995])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_803,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_18,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_336,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_18])).

cnf(c_791,plain,
    ( k7_relat_1(X0,X1) = X0
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_336])).

cnf(c_1784,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_803,c_791])).

cnf(c_1916,plain,
    ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_1831,c_1784])).

cnf(c_3114,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
    inference(demodulation,[status(thm)],[c_3109,c_1916])).

cnf(c_351,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(X0,X2) = X0
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X3))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_316])).

cnf(c_352,plain,
    ( ~ v1_relat_1(sK3)
    | k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(unflattening,[status(thm)],[c_351])).

cnf(c_790,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_352])).

cnf(c_1390,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
    | k7_relat_1(sK3,X0) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_790,c_352,c_996,c_1238])).

cnf(c_1391,plain,
    ( k7_relat_1(sK3,X0) = sK3
    | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(renaming,[status(thm)],[c_1390])).

cnf(c_1397,plain,
    ( k7_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK3 ),
    inference(equality_resolution,[status(thm)],[c_1391])).

cnf(c_4,plain,
    ( r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_17,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ v1_relat_1(X2)
    | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_257,plain,
    ( ~ v1_relat_1(X0)
    | X1 != X2
    | k7_relat_1(k7_relat_1(X0,X1),X3) = k1_xboole_0
    | k1_xboole_0 != X3 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_17])).

cnf(c_258,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_257])).

cnf(c_794,plain,
    ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_258])).

cnf(c_2096,plain,
    ( k7_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1831,c_794])).

cnf(c_2189,plain,
    ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1397,c_2096])).

cnf(c_3127,plain,
    ( sK3 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3114,c_2189])).

cnf(c_922,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(equality_resolution,[status(thm)],[c_307])).

cnf(c_795,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_950,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_922,c_795])).

cnf(c_3294,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3127,c_950])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1829,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_798])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_796,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2270,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1829,c_796])).

cnf(c_19,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_20,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1667,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_20,c_791])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_77,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2912,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1667,c_77,c_1829])).

cnf(c_2917,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2270,c_19,c_2912])).

cnf(c_3307,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3294,c_2917])).

cnf(c_802,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3573,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3307,c_802])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:33:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.64/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.64/0.98  
% 2.64/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.64/0.98  
% 2.64/0.98  ------  iProver source info
% 2.64/0.98  
% 2.64/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.64/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.64/0.98  git: non_committed_changes: false
% 2.64/0.98  git: last_make_outside_of_git: false
% 2.64/0.98  
% 2.64/0.98  ------ 
% 2.64/0.98  
% 2.64/0.98  ------ Input Options
% 2.64/0.98  
% 2.64/0.98  --out_options                           all
% 2.64/0.98  --tptp_safe_out                         true
% 2.64/0.98  --problem_path                          ""
% 2.64/0.98  --include_path                          ""
% 2.64/0.98  --clausifier                            res/vclausify_rel
% 2.64/0.98  --clausifier_options                    --mode clausify
% 2.64/0.98  --stdin                                 false
% 2.64/0.98  --stats_out                             all
% 2.64/0.98  
% 2.64/0.98  ------ General Options
% 2.64/0.98  
% 2.64/0.98  --fof                                   false
% 2.64/0.98  --time_out_real                         305.
% 2.64/0.98  --time_out_virtual                      -1.
% 2.64/0.98  --symbol_type_check                     false
% 2.64/0.98  --clausify_out                          false
% 2.64/0.98  --sig_cnt_out                           false
% 2.64/0.98  --trig_cnt_out                          false
% 2.64/0.98  --trig_cnt_out_tolerance                1.
% 2.64/0.98  --trig_cnt_out_sk_spl                   false
% 2.64/0.98  --abstr_cl_out                          false
% 2.64/0.98  
% 2.64/0.98  ------ Global Options
% 2.64/0.98  
% 2.64/0.98  --schedule                              default
% 2.64/0.98  --add_important_lit                     false
% 2.64/0.98  --prop_solver_per_cl                    1000
% 2.64/0.98  --min_unsat_core                        false
% 2.64/0.98  --soft_assumptions                      false
% 2.64/0.98  --soft_lemma_size                       3
% 2.64/0.98  --prop_impl_unit_size                   0
% 2.64/0.98  --prop_impl_unit                        []
% 2.64/0.98  --share_sel_clauses                     true
% 2.64/0.98  --reset_solvers                         false
% 2.64/0.98  --bc_imp_inh                            [conj_cone]
% 2.64/0.98  --conj_cone_tolerance                   3.
% 2.64/0.98  --extra_neg_conj                        none
% 2.64/0.98  --large_theory_mode                     true
% 2.64/0.98  --prolific_symb_bound                   200
% 2.64/0.98  --lt_threshold                          2000
% 2.64/0.98  --clause_weak_htbl                      true
% 2.64/0.98  --gc_record_bc_elim                     false
% 2.64/0.98  
% 2.64/0.98  ------ Preprocessing Options
% 2.64/0.98  
% 2.64/0.98  --preprocessing_flag                    true
% 2.64/0.98  --time_out_prep_mult                    0.1
% 2.64/0.98  --splitting_mode                        input
% 2.64/0.98  --splitting_grd                         true
% 2.64/0.98  --splitting_cvd                         false
% 2.64/0.98  --splitting_cvd_svl                     false
% 2.64/0.98  --splitting_nvd                         32
% 2.64/0.98  --sub_typing                            true
% 2.64/0.98  --prep_gs_sim                           true
% 2.64/0.98  --prep_unflatten                        true
% 2.64/0.98  --prep_res_sim                          true
% 2.64/0.98  --prep_upred                            true
% 2.64/0.98  --prep_sem_filter                       exhaustive
% 2.64/0.98  --prep_sem_filter_out                   false
% 2.64/0.98  --pred_elim                             true
% 2.64/0.98  --res_sim_input                         true
% 2.64/0.98  --eq_ax_congr_red                       true
% 2.64/0.98  --pure_diseq_elim                       true
% 2.64/0.98  --brand_transform                       false
% 2.64/0.98  --non_eq_to_eq                          false
% 2.64/0.98  --prep_def_merge                        true
% 2.64/0.98  --prep_def_merge_prop_impl              false
% 2.64/0.98  --prep_def_merge_mbd                    true
% 2.64/0.98  --prep_def_merge_tr_red                 false
% 2.64/0.98  --prep_def_merge_tr_cl                  false
% 2.64/0.98  --smt_preprocessing                     true
% 2.64/0.98  --smt_ac_axioms                         fast
% 2.64/0.98  --preprocessed_out                      false
% 2.64/0.98  --preprocessed_stats                    false
% 2.64/0.98  
% 2.64/0.98  ------ Abstraction refinement Options
% 2.64/0.98  
% 2.64/0.98  --abstr_ref                             []
% 2.64/0.98  --abstr_ref_prep                        false
% 2.64/0.98  --abstr_ref_until_sat                   false
% 2.64/0.98  --abstr_ref_sig_restrict                funpre
% 2.64/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/0.98  --abstr_ref_under                       []
% 2.64/0.98  
% 2.64/0.98  ------ SAT Options
% 2.64/0.98  
% 2.64/0.98  --sat_mode                              false
% 2.64/0.98  --sat_fm_restart_options                ""
% 2.64/0.98  --sat_gr_def                            false
% 2.64/0.98  --sat_epr_types                         true
% 2.64/0.98  --sat_non_cyclic_types                  false
% 2.64/0.98  --sat_finite_models                     false
% 2.64/0.98  --sat_fm_lemmas                         false
% 2.64/0.98  --sat_fm_prep                           false
% 2.64/0.98  --sat_fm_uc_incr                        true
% 2.64/0.98  --sat_out_model                         small
% 2.64/0.98  --sat_out_clauses                       false
% 2.64/0.98  
% 2.64/0.98  ------ QBF Options
% 2.64/0.98  
% 2.64/0.98  --qbf_mode                              false
% 2.64/0.98  --qbf_elim_univ                         false
% 2.64/0.98  --qbf_dom_inst                          none
% 2.64/0.98  --qbf_dom_pre_inst                      false
% 2.64/0.98  --qbf_sk_in                             false
% 2.64/0.98  --qbf_pred_elim                         true
% 2.64/0.98  --qbf_split                             512
% 2.64/0.98  
% 2.64/0.98  ------ BMC1 Options
% 2.64/0.98  
% 2.64/0.98  --bmc1_incremental                      false
% 2.64/0.98  --bmc1_axioms                           reachable_all
% 2.64/0.98  --bmc1_min_bound                        0
% 2.64/0.98  --bmc1_max_bound                        -1
% 2.64/0.98  --bmc1_max_bound_default                -1
% 2.64/0.98  --bmc1_symbol_reachability              true
% 2.64/0.98  --bmc1_property_lemmas                  false
% 2.64/0.98  --bmc1_k_induction                      false
% 2.64/0.98  --bmc1_non_equiv_states                 false
% 2.64/0.98  --bmc1_deadlock                         false
% 2.64/0.98  --bmc1_ucm                              false
% 2.64/0.98  --bmc1_add_unsat_core                   none
% 2.64/0.98  --bmc1_unsat_core_children              false
% 2.64/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/0.98  --bmc1_out_stat                         full
% 2.64/0.98  --bmc1_ground_init                      false
% 2.64/0.98  --bmc1_pre_inst_next_state              false
% 2.64/0.98  --bmc1_pre_inst_state                   false
% 2.64/0.98  --bmc1_pre_inst_reach_state             false
% 2.64/0.98  --bmc1_out_unsat_core                   false
% 2.64/0.98  --bmc1_aig_witness_out                  false
% 2.64/0.98  --bmc1_verbose                          false
% 2.64/0.98  --bmc1_dump_clauses_tptp                false
% 2.64/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.64/0.98  --bmc1_dump_file                        -
% 2.64/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.64/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.64/0.98  --bmc1_ucm_extend_mode                  1
% 2.64/0.98  --bmc1_ucm_init_mode                    2
% 2.64/0.98  --bmc1_ucm_cone_mode                    none
% 2.64/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.64/0.98  --bmc1_ucm_relax_model                  4
% 2.64/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.64/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/0.98  --bmc1_ucm_layered_model                none
% 2.64/0.98  --bmc1_ucm_max_lemma_size               10
% 2.64/0.98  
% 2.64/0.98  ------ AIG Options
% 2.64/0.98  
% 2.64/0.98  --aig_mode                              false
% 2.64/0.98  
% 2.64/0.98  ------ Instantiation Options
% 2.64/0.98  
% 2.64/0.98  --instantiation_flag                    true
% 2.64/0.98  --inst_sos_flag                         false
% 2.64/0.98  --inst_sos_phase                        true
% 2.64/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/0.98  --inst_lit_sel_side                     num_symb
% 2.64/0.98  --inst_solver_per_active                1400
% 2.64/0.98  --inst_solver_calls_frac                1.
% 2.64/0.98  --inst_passive_queue_type               priority_queues
% 2.64/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/0.98  --inst_passive_queues_freq              [25;2]
% 2.64/0.98  --inst_dismatching                      true
% 2.64/0.98  --inst_eager_unprocessed_to_passive     true
% 2.64/0.98  --inst_prop_sim_given                   true
% 2.64/0.98  --inst_prop_sim_new                     false
% 2.64/0.98  --inst_subs_new                         false
% 2.64/0.99  --inst_eq_res_simp                      false
% 2.64/0.99  --inst_subs_given                       false
% 2.64/0.99  --inst_orphan_elimination               true
% 2.64/0.99  --inst_learning_loop_flag               true
% 2.64/0.99  --inst_learning_start                   3000
% 2.64/0.99  --inst_learning_factor                  2
% 2.64/0.99  --inst_start_prop_sim_after_learn       3
% 2.64/0.99  --inst_sel_renew                        solver
% 2.64/0.99  --inst_lit_activity_flag                true
% 2.64/0.99  --inst_restr_to_given                   false
% 2.64/0.99  --inst_activity_threshold               500
% 2.64/0.99  --inst_out_proof                        true
% 2.64/0.99  
% 2.64/0.99  ------ Resolution Options
% 2.64/0.99  
% 2.64/0.99  --resolution_flag                       true
% 2.64/0.99  --res_lit_sel                           adaptive
% 2.64/0.99  --res_lit_sel_side                      none
% 2.64/0.99  --res_ordering                          kbo
% 2.64/0.99  --res_to_prop_solver                    active
% 2.64/0.99  --res_prop_simpl_new                    false
% 2.64/0.99  --res_prop_simpl_given                  true
% 2.64/0.99  --res_passive_queue_type                priority_queues
% 2.64/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/0.99  --res_passive_queues_freq               [15;5]
% 2.64/0.99  --res_forward_subs                      full
% 2.64/0.99  --res_backward_subs                     full
% 2.64/0.99  --res_forward_subs_resolution           true
% 2.64/0.99  --res_backward_subs_resolution          true
% 2.64/0.99  --res_orphan_elimination                true
% 2.64/0.99  --res_time_limit                        2.
% 2.64/0.99  --res_out_proof                         true
% 2.64/0.99  
% 2.64/0.99  ------ Superposition Options
% 2.64/0.99  
% 2.64/0.99  --superposition_flag                    true
% 2.64/0.99  --sup_passive_queue_type                priority_queues
% 2.64/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.64/0.99  --demod_completeness_check              fast
% 2.64/0.99  --demod_use_ground                      true
% 2.64/0.99  --sup_to_prop_solver                    passive
% 2.64/0.99  --sup_prop_simpl_new                    true
% 2.64/0.99  --sup_prop_simpl_given                  true
% 2.64/0.99  --sup_fun_splitting                     false
% 2.64/0.99  --sup_smt_interval                      50000
% 2.64/0.99  
% 2.64/0.99  ------ Superposition Simplification Setup
% 2.64/0.99  
% 2.64/0.99  --sup_indices_passive                   []
% 2.64/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.99  --sup_full_bw                           [BwDemod]
% 2.64/0.99  --sup_immed_triv                        [TrivRules]
% 2.64/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.99  --sup_immed_bw_main                     []
% 2.64/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.99  
% 2.64/0.99  ------ Combination Options
% 2.64/0.99  
% 2.64/0.99  --comb_res_mult                         3
% 2.64/0.99  --comb_sup_mult                         2
% 2.64/0.99  --comb_inst_mult                        10
% 2.64/0.99  
% 2.64/0.99  ------ Debug Options
% 2.64/0.99  
% 2.64/0.99  --dbg_backtrace                         false
% 2.64/0.99  --dbg_dump_prop_clauses                 false
% 2.64/0.99  --dbg_dump_prop_clauses_file            -
% 2.64/0.99  --dbg_out_stat                          false
% 2.64/0.99  ------ Parsing...
% 2.64/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.64/0.99  
% 2.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.64/0.99  
% 2.64/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.64/0.99  
% 2.64/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.64/0.99  ------ Proving...
% 2.64/0.99  ------ Problem Properties 
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  clauses                                 23
% 2.64/0.99  conjectures                             2
% 2.64/0.99  EPR                                     4
% 2.64/0.99  Horn                                    21
% 2.64/0.99  unary                                   11
% 2.64/0.99  binary                                  4
% 2.64/0.99  lits                                    43
% 2.64/0.99  lits eq                                 22
% 2.64/0.99  fd_pure                                 0
% 2.64/0.99  fd_pseudo                               0
% 2.64/0.99  fd_cond                                 1
% 2.64/0.99  fd_pseudo_cond                          2
% 2.64/0.99  AC symbols                              0
% 2.64/0.99  
% 2.64/0.99  ------ Schedule dynamic 5 is on 
% 2.64/0.99  
% 2.64/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  ------ 
% 2.64/0.99  Current options:
% 2.64/0.99  ------ 
% 2.64/0.99  
% 2.64/0.99  ------ Input Options
% 2.64/0.99  
% 2.64/0.99  --out_options                           all
% 2.64/0.99  --tptp_safe_out                         true
% 2.64/0.99  --problem_path                          ""
% 2.64/0.99  --include_path                          ""
% 2.64/0.99  --clausifier                            res/vclausify_rel
% 2.64/0.99  --clausifier_options                    --mode clausify
% 2.64/0.99  --stdin                                 false
% 2.64/0.99  --stats_out                             all
% 2.64/0.99  
% 2.64/0.99  ------ General Options
% 2.64/0.99  
% 2.64/0.99  --fof                                   false
% 2.64/0.99  --time_out_real                         305.
% 2.64/0.99  --time_out_virtual                      -1.
% 2.64/0.99  --symbol_type_check                     false
% 2.64/0.99  --clausify_out                          false
% 2.64/0.99  --sig_cnt_out                           false
% 2.64/0.99  --trig_cnt_out                          false
% 2.64/0.99  --trig_cnt_out_tolerance                1.
% 2.64/0.99  --trig_cnt_out_sk_spl                   false
% 2.64/0.99  --abstr_cl_out                          false
% 2.64/0.99  
% 2.64/0.99  ------ Global Options
% 2.64/0.99  
% 2.64/0.99  --schedule                              default
% 2.64/0.99  --add_important_lit                     false
% 2.64/0.99  --prop_solver_per_cl                    1000
% 2.64/0.99  --min_unsat_core                        false
% 2.64/0.99  --soft_assumptions                      false
% 2.64/0.99  --soft_lemma_size                       3
% 2.64/0.99  --prop_impl_unit_size                   0
% 2.64/0.99  --prop_impl_unit                        []
% 2.64/0.99  --share_sel_clauses                     true
% 2.64/0.99  --reset_solvers                         false
% 2.64/0.99  --bc_imp_inh                            [conj_cone]
% 2.64/0.99  --conj_cone_tolerance                   3.
% 2.64/0.99  --extra_neg_conj                        none
% 2.64/0.99  --large_theory_mode                     true
% 2.64/0.99  --prolific_symb_bound                   200
% 2.64/0.99  --lt_threshold                          2000
% 2.64/0.99  --clause_weak_htbl                      true
% 2.64/0.99  --gc_record_bc_elim                     false
% 2.64/0.99  
% 2.64/0.99  ------ Preprocessing Options
% 2.64/0.99  
% 2.64/0.99  --preprocessing_flag                    true
% 2.64/0.99  --time_out_prep_mult                    0.1
% 2.64/0.99  --splitting_mode                        input
% 2.64/0.99  --splitting_grd                         true
% 2.64/0.99  --splitting_cvd                         false
% 2.64/0.99  --splitting_cvd_svl                     false
% 2.64/0.99  --splitting_nvd                         32
% 2.64/0.99  --sub_typing                            true
% 2.64/0.99  --prep_gs_sim                           true
% 2.64/0.99  --prep_unflatten                        true
% 2.64/0.99  --prep_res_sim                          true
% 2.64/0.99  --prep_upred                            true
% 2.64/0.99  --prep_sem_filter                       exhaustive
% 2.64/0.99  --prep_sem_filter_out                   false
% 2.64/0.99  --pred_elim                             true
% 2.64/0.99  --res_sim_input                         true
% 2.64/0.99  --eq_ax_congr_red                       true
% 2.64/0.99  --pure_diseq_elim                       true
% 2.64/0.99  --brand_transform                       false
% 2.64/0.99  --non_eq_to_eq                          false
% 2.64/0.99  --prep_def_merge                        true
% 2.64/0.99  --prep_def_merge_prop_impl              false
% 2.64/0.99  --prep_def_merge_mbd                    true
% 2.64/0.99  --prep_def_merge_tr_red                 false
% 2.64/0.99  --prep_def_merge_tr_cl                  false
% 2.64/0.99  --smt_preprocessing                     true
% 2.64/0.99  --smt_ac_axioms                         fast
% 2.64/0.99  --preprocessed_out                      false
% 2.64/0.99  --preprocessed_stats                    false
% 2.64/0.99  
% 2.64/0.99  ------ Abstraction refinement Options
% 2.64/0.99  
% 2.64/0.99  --abstr_ref                             []
% 2.64/0.99  --abstr_ref_prep                        false
% 2.64/0.99  --abstr_ref_until_sat                   false
% 2.64/0.99  --abstr_ref_sig_restrict                funpre
% 2.64/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.64/0.99  --abstr_ref_under                       []
% 2.64/0.99  
% 2.64/0.99  ------ SAT Options
% 2.64/0.99  
% 2.64/0.99  --sat_mode                              false
% 2.64/0.99  --sat_fm_restart_options                ""
% 2.64/0.99  --sat_gr_def                            false
% 2.64/0.99  --sat_epr_types                         true
% 2.64/0.99  --sat_non_cyclic_types                  false
% 2.64/0.99  --sat_finite_models                     false
% 2.64/0.99  --sat_fm_lemmas                         false
% 2.64/0.99  --sat_fm_prep                           false
% 2.64/0.99  --sat_fm_uc_incr                        true
% 2.64/0.99  --sat_out_model                         small
% 2.64/0.99  --sat_out_clauses                       false
% 2.64/0.99  
% 2.64/0.99  ------ QBF Options
% 2.64/0.99  
% 2.64/0.99  --qbf_mode                              false
% 2.64/0.99  --qbf_elim_univ                         false
% 2.64/0.99  --qbf_dom_inst                          none
% 2.64/0.99  --qbf_dom_pre_inst                      false
% 2.64/0.99  --qbf_sk_in                             false
% 2.64/0.99  --qbf_pred_elim                         true
% 2.64/0.99  --qbf_split                             512
% 2.64/0.99  
% 2.64/0.99  ------ BMC1 Options
% 2.64/0.99  
% 2.64/0.99  --bmc1_incremental                      false
% 2.64/0.99  --bmc1_axioms                           reachable_all
% 2.64/0.99  --bmc1_min_bound                        0
% 2.64/0.99  --bmc1_max_bound                        -1
% 2.64/0.99  --bmc1_max_bound_default                -1
% 2.64/0.99  --bmc1_symbol_reachability              true
% 2.64/0.99  --bmc1_property_lemmas                  false
% 2.64/0.99  --bmc1_k_induction                      false
% 2.64/0.99  --bmc1_non_equiv_states                 false
% 2.64/0.99  --bmc1_deadlock                         false
% 2.64/0.99  --bmc1_ucm                              false
% 2.64/0.99  --bmc1_add_unsat_core                   none
% 2.64/0.99  --bmc1_unsat_core_children              false
% 2.64/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.64/0.99  --bmc1_out_stat                         full
% 2.64/0.99  --bmc1_ground_init                      false
% 2.64/0.99  --bmc1_pre_inst_next_state              false
% 2.64/0.99  --bmc1_pre_inst_state                   false
% 2.64/0.99  --bmc1_pre_inst_reach_state             false
% 2.64/0.99  --bmc1_out_unsat_core                   false
% 2.64/0.99  --bmc1_aig_witness_out                  false
% 2.64/0.99  --bmc1_verbose                          false
% 2.64/0.99  --bmc1_dump_clauses_tptp                false
% 2.64/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.64/0.99  --bmc1_dump_file                        -
% 2.64/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.64/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.64/0.99  --bmc1_ucm_extend_mode                  1
% 2.64/0.99  --bmc1_ucm_init_mode                    2
% 2.64/0.99  --bmc1_ucm_cone_mode                    none
% 2.64/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.64/0.99  --bmc1_ucm_relax_model                  4
% 2.64/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.64/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.64/0.99  --bmc1_ucm_layered_model                none
% 2.64/0.99  --bmc1_ucm_max_lemma_size               10
% 2.64/0.99  
% 2.64/0.99  ------ AIG Options
% 2.64/0.99  
% 2.64/0.99  --aig_mode                              false
% 2.64/0.99  
% 2.64/0.99  ------ Instantiation Options
% 2.64/0.99  
% 2.64/0.99  --instantiation_flag                    true
% 2.64/0.99  --inst_sos_flag                         false
% 2.64/0.99  --inst_sos_phase                        true
% 2.64/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.64/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.64/0.99  --inst_lit_sel_side                     none
% 2.64/0.99  --inst_solver_per_active                1400
% 2.64/0.99  --inst_solver_calls_frac                1.
% 2.64/0.99  --inst_passive_queue_type               priority_queues
% 2.64/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.64/0.99  --inst_passive_queues_freq              [25;2]
% 2.64/0.99  --inst_dismatching                      true
% 2.64/0.99  --inst_eager_unprocessed_to_passive     true
% 2.64/0.99  --inst_prop_sim_given                   true
% 2.64/0.99  --inst_prop_sim_new                     false
% 2.64/0.99  --inst_subs_new                         false
% 2.64/0.99  --inst_eq_res_simp                      false
% 2.64/0.99  --inst_subs_given                       false
% 2.64/0.99  --inst_orphan_elimination               true
% 2.64/0.99  --inst_learning_loop_flag               true
% 2.64/0.99  --inst_learning_start                   3000
% 2.64/0.99  --inst_learning_factor                  2
% 2.64/0.99  --inst_start_prop_sim_after_learn       3
% 2.64/0.99  --inst_sel_renew                        solver
% 2.64/0.99  --inst_lit_activity_flag                true
% 2.64/0.99  --inst_restr_to_given                   false
% 2.64/0.99  --inst_activity_threshold               500
% 2.64/0.99  --inst_out_proof                        true
% 2.64/0.99  
% 2.64/0.99  ------ Resolution Options
% 2.64/0.99  
% 2.64/0.99  --resolution_flag                       false
% 2.64/0.99  --res_lit_sel                           adaptive
% 2.64/0.99  --res_lit_sel_side                      none
% 2.64/0.99  --res_ordering                          kbo
% 2.64/0.99  --res_to_prop_solver                    active
% 2.64/0.99  --res_prop_simpl_new                    false
% 2.64/0.99  --res_prop_simpl_given                  true
% 2.64/0.99  --res_passive_queue_type                priority_queues
% 2.64/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.64/0.99  --res_passive_queues_freq               [15;5]
% 2.64/0.99  --res_forward_subs                      full
% 2.64/0.99  --res_backward_subs                     full
% 2.64/0.99  --res_forward_subs_resolution           true
% 2.64/0.99  --res_backward_subs_resolution          true
% 2.64/0.99  --res_orphan_elimination                true
% 2.64/0.99  --res_time_limit                        2.
% 2.64/0.99  --res_out_proof                         true
% 2.64/0.99  
% 2.64/0.99  ------ Superposition Options
% 2.64/0.99  
% 2.64/0.99  --superposition_flag                    true
% 2.64/0.99  --sup_passive_queue_type                priority_queues
% 2.64/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.64/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.64/0.99  --demod_completeness_check              fast
% 2.64/0.99  --demod_use_ground                      true
% 2.64/0.99  --sup_to_prop_solver                    passive
% 2.64/0.99  --sup_prop_simpl_new                    true
% 2.64/0.99  --sup_prop_simpl_given                  true
% 2.64/0.99  --sup_fun_splitting                     false
% 2.64/0.99  --sup_smt_interval                      50000
% 2.64/0.99  
% 2.64/0.99  ------ Superposition Simplification Setup
% 2.64/0.99  
% 2.64/0.99  --sup_indices_passive                   []
% 2.64/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.64/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.64/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.99  --sup_full_bw                           [BwDemod]
% 2.64/0.99  --sup_immed_triv                        [TrivRules]
% 2.64/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.64/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.99  --sup_immed_bw_main                     []
% 2.64/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.64/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.64/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.64/0.99  
% 2.64/0.99  ------ Combination Options
% 2.64/0.99  
% 2.64/0.99  --comb_res_mult                         3
% 2.64/0.99  --comb_sup_mult                         2
% 2.64/0.99  --comb_inst_mult                        10
% 2.64/0.99  
% 2.64/0.99  ------ Debug Options
% 2.64/0.99  
% 2.64/0.99  --dbg_backtrace                         false
% 2.64/0.99  --dbg_dump_prop_clauses                 false
% 2.64/0.99  --dbg_dump_prop_clauses_file            -
% 2.64/0.99  --dbg_out_stat                          false
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  ------ Proving...
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  % SZS status Theorem for theBenchmark.p
% 2.64/0.99  
% 2.64/0.99   Resolution empty clause
% 2.64/0.99  
% 2.64/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.64/0.99  
% 2.64/0.99  fof(f14,axiom,(
% 2.64/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f29,plain,(
% 2.64/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.64/0.99    inference(ennf_transformation,[],[f14])).
% 2.64/0.99  
% 2.64/0.99  fof(f48,plain,(
% 2.64/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.64/0.99    inference(nnf_transformation,[],[f29])).
% 2.64/0.99  
% 2.64/0.99  fof(f70,plain,(
% 2.64/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f48])).
% 2.64/0.99  
% 2.64/0.99  fof(f22,axiom,(
% 2.64/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f27,plain,(
% 2.64/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.64/0.99    inference(pure_predicate_removal,[],[f22])).
% 2.64/0.99  
% 2.64/0.99  fof(f38,plain,(
% 2.64/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/0.99    inference(ennf_transformation,[],[f27])).
% 2.64/0.99  
% 2.64/0.99  fof(f80,plain,(
% 2.64/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/0.99    inference(cnf_transformation,[],[f38])).
% 2.64/0.99  
% 2.64/0.99  fof(f24,conjecture,(
% 2.64/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f25,negated_conjecture,(
% 2.64/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.64/0.99    inference(negated_conjecture,[],[f24])).
% 2.64/0.99  
% 2.64/0.99  fof(f26,plain,(
% 2.64/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 2.64/0.99    inference(pure_predicate_removal,[],[f25])).
% 2.64/0.99  
% 2.64/0.99  fof(f40,plain,(
% 2.64/0.99    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 2.64/0.99    inference(ennf_transformation,[],[f26])).
% 2.64/0.99  
% 2.64/0.99  fof(f41,plain,(
% 2.64/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 2.64/0.99    inference(flattening,[],[f40])).
% 2.64/0.99  
% 2.64/0.99  fof(f49,plain,(
% 2.64/0.99    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 2.64/0.99    introduced(choice_axiom,[])).
% 2.64/0.99  
% 2.64/0.99  fof(f50,plain,(
% 2.64/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 2.64/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f49])).
% 2.64/0.99  
% 2.64/0.99  fof(f83,plain,(
% 2.64/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 2.64/0.99    inference(cnf_transformation,[],[f50])).
% 2.64/0.99  
% 2.64/0.99  fof(f4,axiom,(
% 2.64/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f56,plain,(
% 2.64/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f4])).
% 2.64/0.99  
% 2.64/0.99  fof(f5,axiom,(
% 2.64/0.99    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f57,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f5])).
% 2.64/0.99  
% 2.64/0.99  fof(f6,axiom,(
% 2.64/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f58,plain,(
% 2.64/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f6])).
% 2.64/0.99  
% 2.64/0.99  fof(f7,axiom,(
% 2.64/0.99    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f59,plain,(
% 2.64/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f7])).
% 2.64/0.99  
% 2.64/0.99  fof(f8,axiom,(
% 2.64/0.99    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f60,plain,(
% 2.64/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f8])).
% 2.64/0.99  
% 2.64/0.99  fof(f9,axiom,(
% 2.64/0.99    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f61,plain,(
% 2.64/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f9])).
% 2.64/0.99  
% 2.64/0.99  fof(f10,axiom,(
% 2.64/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f62,plain,(
% 2.64/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f10])).
% 2.64/0.99  
% 2.64/0.99  fof(f86,plain,(
% 2.64/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f61,f62])).
% 2.64/0.99  
% 2.64/0.99  fof(f87,plain,(
% 2.64/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f60,f86])).
% 2.64/0.99  
% 2.64/0.99  fof(f88,plain,(
% 2.64/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f59,f87])).
% 2.64/0.99  
% 2.64/0.99  fof(f89,plain,(
% 2.64/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f58,f88])).
% 2.64/0.99  
% 2.64/0.99  fof(f90,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f57,f89])).
% 2.64/0.99  
% 2.64/0.99  fof(f91,plain,(
% 2.64/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f56,f90])).
% 2.64/0.99  
% 2.64/0.99  fof(f97,plain,(
% 2.64/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 2.64/0.99    inference(definition_unfolding,[],[f83,f91])).
% 2.64/0.99  
% 2.64/0.99  fof(f15,axiom,(
% 2.64/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f72,plain,(
% 2.64/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.64/0.99    inference(cnf_transformation,[],[f15])).
% 2.64/0.99  
% 2.64/0.99  fof(f13,axiom,(
% 2.64/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f28,plain,(
% 2.64/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.64/0.99    inference(ennf_transformation,[],[f13])).
% 2.64/0.99  
% 2.64/0.99  fof(f69,plain,(
% 2.64/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f28])).
% 2.64/0.99  
% 2.64/0.99  fof(f11,axiom,(
% 2.64/0.99    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f44,plain,(
% 2.64/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.64/0.99    inference(nnf_transformation,[],[f11])).
% 2.64/0.99  
% 2.64/0.99  fof(f45,plain,(
% 2.64/0.99    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.64/0.99    inference(flattening,[],[f44])).
% 2.64/0.99  
% 2.64/0.99  fof(f63,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.64/0.99    inference(cnf_transformation,[],[f45])).
% 2.64/0.99  
% 2.64/0.99  fof(f94,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 2.64/0.99    inference(definition_unfolding,[],[f63,f91,f91])).
% 2.64/0.99  
% 2.64/0.99  fof(f85,plain,(
% 2.64/0.99    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 2.64/0.99    inference(cnf_transformation,[],[f50])).
% 2.64/0.99  
% 2.64/0.99  fof(f96,plain,(
% 2.64/0.99    ~r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 2.64/0.99    inference(definition_unfolding,[],[f85,f91,f91])).
% 2.64/0.99  
% 2.64/0.99  fof(f21,axiom,(
% 2.64/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f36,plain,(
% 2.64/0.99    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.64/0.99    inference(ennf_transformation,[],[f21])).
% 2.64/0.99  
% 2.64/0.99  fof(f37,plain,(
% 2.64/0.99    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.64/0.99    inference(flattening,[],[f36])).
% 2.64/0.99  
% 2.64/0.99  fof(f79,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f37])).
% 2.64/0.99  
% 2.64/0.99  fof(f95,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.64/0.99    inference(definition_unfolding,[],[f79,f91,f91])).
% 2.64/0.99  
% 2.64/0.99  fof(f82,plain,(
% 2.64/0.99    v1_funct_1(sK3)),
% 2.64/0.99    inference(cnf_transformation,[],[f50])).
% 2.64/0.99  
% 2.64/0.99  fof(f23,axiom,(
% 2.64/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f39,plain,(
% 2.64/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.64/0.99    inference(ennf_transformation,[],[f23])).
% 2.64/0.99  
% 2.64/0.99  fof(f81,plain,(
% 2.64/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.64/0.99    inference(cnf_transformation,[],[f39])).
% 2.64/0.99  
% 2.64/0.99  fof(f16,axiom,(
% 2.64/0.99    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f30,plain,(
% 2.64/0.99    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 2.64/0.99    inference(ennf_transformation,[],[f16])).
% 2.64/0.99  
% 2.64/0.99  fof(f73,plain,(
% 2.64/0.99    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f30])).
% 2.64/0.99  
% 2.64/0.99  fof(f1,axiom,(
% 2.64/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f42,plain,(
% 2.64/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.64/0.99    inference(nnf_transformation,[],[f1])).
% 2.64/0.99  
% 2.64/0.99  fof(f43,plain,(
% 2.64/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.64/0.99    inference(flattening,[],[f42])).
% 2.64/0.99  
% 2.64/0.99  fof(f51,plain,(
% 2.64/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.64/0.99    inference(cnf_transformation,[],[f43])).
% 2.64/0.99  
% 2.64/0.99  fof(f99,plain,(
% 2.64/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.64/0.99    inference(equality_resolution,[],[f51])).
% 2.64/0.99  
% 2.64/0.99  fof(f71,plain,(
% 2.64/0.99    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f48])).
% 2.64/0.99  
% 2.64/0.99  fof(f19,axiom,(
% 2.64/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f34,plain,(
% 2.64/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.64/0.99    inference(ennf_transformation,[],[f19])).
% 2.64/0.99  
% 2.64/0.99  fof(f35,plain,(
% 2.64/0.99    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.64/0.99    inference(flattening,[],[f34])).
% 2.64/0.99  
% 2.64/0.99  fof(f76,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f35])).
% 2.64/0.99  
% 2.64/0.99  fof(f3,axiom,(
% 2.64/0.99    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f55,plain,(
% 2.64/0.99    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f3])).
% 2.64/0.99  
% 2.64/0.99  fof(f18,axiom,(
% 2.64/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f32,plain,(
% 2.64/0.99    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 2.64/0.99    inference(ennf_transformation,[],[f18])).
% 2.64/0.99  
% 2.64/0.99  fof(f33,plain,(
% 2.64/0.99    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 2.64/0.99    inference(flattening,[],[f32])).
% 2.64/0.99  
% 2.64/0.99  fof(f75,plain,(
% 2.64/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f33])).
% 2.64/0.99  
% 2.64/0.99  fof(f12,axiom,(
% 2.64/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f46,plain,(
% 2.64/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.64/0.99    inference(nnf_transformation,[],[f12])).
% 2.64/0.99  
% 2.64/0.99  fof(f47,plain,(
% 2.64/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.64/0.99    inference(flattening,[],[f46])).
% 2.64/0.99  
% 2.64/0.99  fof(f68,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 2.64/0.99    inference(cnf_transformation,[],[f47])).
% 2.64/0.99  
% 2.64/0.99  fof(f102,plain,(
% 2.64/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 2.64/0.99    inference(equality_resolution,[],[f68])).
% 2.64/0.99  
% 2.64/0.99  fof(f17,axiom,(
% 2.64/0.99    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f31,plain,(
% 2.64/0.99    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.64/0.99    inference(ennf_transformation,[],[f17])).
% 2.64/0.99  
% 2.64/0.99  fof(f74,plain,(
% 2.64/0.99    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f31])).
% 2.64/0.99  
% 2.64/0.99  fof(f20,axiom,(
% 2.64/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f78,plain,(
% 2.64/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.64/0.99    inference(cnf_transformation,[],[f20])).
% 2.64/0.99  
% 2.64/0.99  fof(f77,plain,(
% 2.64/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.64/0.99    inference(cnf_transformation,[],[f20])).
% 2.64/0.99  
% 2.64/0.99  fof(f2,axiom,(
% 2.64/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.64/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.64/0.99  
% 2.64/0.99  fof(f54,plain,(
% 2.64/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.64/0.99    inference(cnf_transformation,[],[f2])).
% 2.64/0.99  
% 2.64/0.99  cnf(c_13,plain,
% 2.64/0.99      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.64/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_22,plain,
% 2.64/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.64/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_26,negated_conjecture,
% 2.64/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 2.64/0.99      inference(cnf_transformation,[],[f97]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_315,plain,
% 2.64/0.99      ( v4_relat_1(X0,X1)
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X2))
% 2.64/0.99      | sK3 != X0 ),
% 2.64/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_26]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_316,plain,
% 2.64/0.99      ( v4_relat_1(sK3,X0)
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/0.99      inference(unflattening,[status(thm)],[c_315]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_366,plain,
% 2.64/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 2.64/0.99      | ~ v1_relat_1(X0)
% 2.64/0.99      | X2 != X1
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X2,X3))
% 2.64/0.99      | sK3 != X0 ),
% 2.64/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_316]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_367,plain,
% 2.64/0.99      ( r1_tarski(k1_relat_1(sK3),X0)
% 2.64/0.99      | ~ v1_relat_1(sK3)
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/0.99      inference(unflattening,[status(thm)],[c_366]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_789,plain,
% 2.64/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.99      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.64/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_14,plain,
% 2.64/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_52,plain,
% 2.64/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_368,plain,
% 2.64/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.99      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.64/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_11,plain,
% 2.64/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.64/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_291,plain,
% 2.64/0.99      ( ~ v1_relat_1(X0)
% 2.64/0.99      | v1_relat_1(X1)
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
% 2.64/0.99      | sK3 != X1 ),
% 2.64/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_26]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_292,plain,
% 2.64/0.99      ( ~ v1_relat_1(X0)
% 2.64/0.99      | v1_relat_1(sK3)
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0) ),
% 2.64/0.99      inference(unflattening,[status(thm)],[c_291]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_924,plain,
% 2.64/0.99      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 2.64/0.99      | v1_relat_1(sK3)
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_292]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_925,plain,
% 2.64/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.99      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top
% 2.64/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_924]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1135,plain,
% 2.64/0.99      ( r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/0.99      inference(global_propositional_subsumption,
% 2.64/0.99                [status(thm)],
% 2.64/0.99                [c_789,c_52,c_368,c_925]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1136,plain,
% 2.64/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.99      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top ),
% 2.64/0.99      inference(renaming,[status(thm)],[c_1135]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1143,plain,
% 2.64/0.99      ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 2.64/0.99      inference(equality_resolution,[status(thm)],[c_1136]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_7,plain,
% 2.64/0.99      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 2.64/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 2.64/0.99      | k1_xboole_0 = X0 ),
% 2.64/0.99      inference(cnf_transformation,[],[f94]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_799,plain,
% 2.64/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 2.64/0.99      | k1_xboole_0 = X1
% 2.64/0.99      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_2793,plain,
% 2.64/0.99      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 2.64/0.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 2.64/0.99      inference(superposition,[status(thm)],[c_1143,c_799]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_24,negated_conjecture,
% 2.64/0.99      ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 2.64/0.99      inference(cnf_transformation,[],[f96]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_21,plain,
% 2.64/0.99      ( ~ v1_funct_1(X0)
% 2.64/0.99      | ~ v1_relat_1(X0)
% 2.64/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 2.64/0.99      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 2.64/0.99      inference(cnf_transformation,[],[f95]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_27,negated_conjecture,
% 2.64/0.99      ( v1_funct_1(sK3) ),
% 2.64/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_272,plain,
% 2.64/0.99      ( ~ v1_relat_1(X0)
% 2.64/0.99      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 2.64/0.99      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 2.64/0.99      | sK3 != X0 ),
% 2.64/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_273,plain,
% 2.64/0.99      ( ~ v1_relat_1(sK3)
% 2.64/0.99      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.64/0.99      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 2.64/0.99      inference(unflattening,[status(thm)],[c_272]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_274,plain,
% 2.64/0.99      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 2.64/0.99      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 2.64/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_273]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_276,plain,
% 2.64/0.99      ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 2.64/0.99      | k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k1_relat_1(sK3)
% 2.64/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_274]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_507,plain,( X0 = X0 ),theory(equality) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_929,plain,
% 2.64/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_507]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_792,plain,
% 2.64/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(X0)
% 2.64/0.99      | v1_relat_1(X0) != iProver_top
% 2.64/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_292]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_995,plain,
% 2.64/0.99      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 2.64/0.99      | v1_relat_1(sK3) = iProver_top ),
% 2.64/0.99      inference(equality_resolution,[status(thm)],[c_792]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_996,plain,
% 2.64/0.99      ( ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
% 2.64/0.99      | v1_relat_1(sK3) ),
% 2.64/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_995]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_23,plain,
% 2.64/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.64/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 2.64/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_306,plain,
% 2.64/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.99      | sK3 != X2 ),
% 2.64/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_26]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_307,plain,
% 2.64/0.99      ( k7_relset_1(X0,X1,sK3,X2) = k9_relat_1(sK3,X2)
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/0.99      inference(unflattening,[status(thm)],[c_306]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_930,plain,
% 2.64/0.99      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0)
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_307]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1057,plain,
% 2.64/0.99      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2) = k9_relat_1(sK3,sK2)
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_930]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1238,plain,
% 2.64/0.99      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1239,plain,
% 2.64/0.99      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_1238]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_15,plain,
% 2.64/0.99      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 2.64/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1739,plain,
% 2.64/0.99      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_2281,plain,
% 2.64/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_1739]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_509,plain,
% 2.64/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.64/0.99      theory(equality) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_986,plain,
% 2.64/0.99      ( ~ r1_tarski(X0,X1)
% 2.64/0.99      | r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.64/0.99      | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X1
% 2.64/0.99      | k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2) != X0 ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_509]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1058,plain,
% 2.64/0.99      ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.64/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),X0)
% 2.64/0.99      | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != X0
% 2.64/0.99      | k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2) ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_986]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_2282,plain,
% 2.64/0.99      ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))
% 2.64/0.99      | ~ r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3))
% 2.64/0.99      | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) != k2_relat_1(sK3)
% 2.64/0.99      | k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2) != k9_relat_1(sK3,sK2) ),
% 2.64/0.99      inference(instantiation,[status(thm)],[c_1058]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_3109,plain,
% 2.64/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.64/0.99      inference(global_propositional_subsumption,
% 2.64/0.99                [status(thm)],
% 2.64/0.99                [c_2793,c_24,c_276,c_929,c_995,c_996,c_1057,c_1238,c_1239,
% 2.64/0.99                 c_2281,c_2282]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_798,plain,
% 2.64/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1831,plain,
% 2.64/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 2.64/0.99      inference(superposition,[status(thm)],[c_798,c_995]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f99]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_803,plain,
% 2.64/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_12,plain,
% 2.64/0.99      ( v4_relat_1(X0,X1) | ~ r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 2.64/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_18,plain,
% 2.64/0.99      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.64/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_336,plain,
% 2.64/0.99      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.64/0.99      | ~ v1_relat_1(X0)
% 2.64/0.99      | k7_relat_1(X0,X1) = X0 ),
% 2.64/0.99      inference(resolution,[status(thm)],[c_12,c_18]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_791,plain,
% 2.64/0.99      ( k7_relat_1(X0,X1) = X0
% 2.64/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.64/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_336]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1784,plain,
% 2.64/0.99      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 2.64/0.99      inference(superposition,[status(thm)],[c_803,c_791]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1916,plain,
% 2.64/0.99      ( k7_relat_1(sK3,k1_relat_1(sK3)) = sK3 ),
% 2.64/0.99      inference(superposition,[status(thm)],[c_1831,c_1784]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_3114,plain,
% 2.64/0.99      ( k7_relat_1(sK3,k1_xboole_0) = sK3 ),
% 2.64/0.99      inference(demodulation,[status(thm)],[c_3109,c_1916]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_351,plain,
% 2.64/0.99      ( ~ v1_relat_1(X0)
% 2.64/0.99      | X1 != X2
% 2.64/0.99      | k7_relat_1(X0,X2) = X0
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X1,X3))
% 2.64/0.99      | sK3 != X0 ),
% 2.64/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_316]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_352,plain,
% 2.64/0.99      ( ~ v1_relat_1(sK3)
% 2.64/0.99      | k7_relat_1(sK3,X0) = sK3
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/0.99      inference(unflattening,[status(thm)],[c_351]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_790,plain,
% 2.64/0.99      ( k7_relat_1(sK3,X0) = sK3
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.99      | v1_relat_1(sK3) != iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_352]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1390,plain,
% 2.64/0.99      ( k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1))
% 2.64/0.99      | k7_relat_1(sK3,X0) = sK3 ),
% 2.64/0.99      inference(global_propositional_subsumption,
% 2.64/0.99                [status(thm)],
% 2.64/0.99                [c_790,c_352,c_996,c_1238]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1391,plain,
% 2.64/0.99      ( k7_relat_1(sK3,X0) = sK3
% 2.64/0.99      | k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 2.64/0.99      inference(renaming,[status(thm)],[c_1390]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1397,plain,
% 2.64/0.99      ( k7_relat_1(sK3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = sK3 ),
% 2.64/0.99      inference(equality_resolution,[status(thm)],[c_1391]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_4,plain,
% 2.64/0.99      ( r1_xboole_0(X0,k1_xboole_0) ),
% 2.64/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_17,plain,
% 2.64/0.99      ( ~ r1_xboole_0(X0,X1)
% 2.64/0.99      | ~ v1_relat_1(X2)
% 2.64/0.99      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ),
% 2.64/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_257,plain,
% 2.64/0.99      ( ~ v1_relat_1(X0)
% 2.64/0.99      | X1 != X2
% 2.64/0.99      | k7_relat_1(k7_relat_1(X0,X1),X3) = k1_xboole_0
% 2.64/0.99      | k1_xboole_0 != X3 ),
% 2.64/0.99      inference(resolution_lifted,[status(thm)],[c_4,c_17]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_258,plain,
% 2.64/0.99      ( ~ v1_relat_1(X0)
% 2.64/0.99      | k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0 ),
% 2.64/0.99      inference(unflattening,[status(thm)],[c_257]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_794,plain,
% 2.64/0.99      ( k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) = k1_xboole_0
% 2.64/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_258]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_2096,plain,
% 2.64/0.99      ( k7_relat_1(k7_relat_1(sK3,X0),k1_xboole_0) = k1_xboole_0 ),
% 2.64/0.99      inference(superposition,[status(thm)],[c_1831,c_794]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_2189,plain,
% 2.64/0.99      ( k7_relat_1(sK3,k1_xboole_0) = k1_xboole_0 ),
% 2.64/0.99      inference(superposition,[status(thm)],[c_1397,c_2096]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_3127,plain,
% 2.64/0.99      ( sK3 = k1_xboole_0 ),
% 2.64/0.99      inference(light_normalisation,[status(thm)],[c_3114,c_2189]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_922,plain,
% 2.64/0.99      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 2.64/0.99      inference(equality_resolution,[status(thm)],[c_307]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_795,plain,
% 2.64/0.99      ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_950,plain,
% 2.64/0.99      ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 2.64/0.99      inference(demodulation,[status(thm)],[c_922,c_795]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_3294,plain,
% 2.64/0.99      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.64/0.99      inference(demodulation,[status(thm)],[c_3127,c_950]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_8,plain,
% 2.64/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.64/0.99      inference(cnf_transformation,[],[f102]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1829,plain,
% 2.64/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.64/0.99      inference(superposition,[status(thm)],[c_8,c_798]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_16,plain,
% 2.64/0.99      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.64/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_796,plain,
% 2.64/0.99      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.64/0.99      | v1_relat_1(X0) != iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_2270,plain,
% 2.64/0.99      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 2.64/0.99      inference(superposition,[status(thm)],[c_1829,c_796]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_19,plain,
% 2.64/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.64/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_20,plain,
% 2.64/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.64/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_1667,plain,
% 2.64/0.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 2.64/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.64/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 2.64/0.99      inference(superposition,[status(thm)],[c_20,c_791]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_3,plain,
% 2.64/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 2.64/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_77,plain,
% 2.64/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_2912,plain,
% 2.64/0.99      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.64/0.99      inference(global_propositional_subsumption,
% 2.64/0.99                [status(thm)],
% 2.64/0.99                [c_1667,c_77,c_1829]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_2917,plain,
% 2.64/0.99      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.64/0.99      inference(light_normalisation,[status(thm)],[c_2270,c_19,c_2912]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_3307,plain,
% 2.64/0.99      ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.64/0.99      inference(demodulation,[status(thm)],[c_3294,c_2917]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_802,plain,
% 2.64/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.64/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.64/0.99  
% 2.64/0.99  cnf(c_3573,plain,
% 2.64/0.99      ( $false ),
% 2.64/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_3307,c_802]) ).
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.64/0.99  
% 2.64/0.99  ------                               Statistics
% 2.64/0.99  
% 2.64/0.99  ------ General
% 2.64/0.99  
% 2.64/0.99  abstr_ref_over_cycles:                  0
% 2.64/0.99  abstr_ref_under_cycles:                 0
% 2.64/0.99  gc_basic_clause_elim:                   0
% 2.64/0.99  forced_gc_time:                         0
% 2.64/0.99  parsing_time:                           0.009
% 2.64/0.99  unif_index_cands_time:                  0.
% 2.64/0.99  unif_index_add_time:                    0.
% 2.64/0.99  orderings_time:                         0.
% 2.64/0.99  out_proof_time:                         0.011
% 2.64/0.99  total_time:                             0.168
% 2.64/0.99  num_of_symbols:                         51
% 2.64/0.99  num_of_terms:                           2972
% 2.64/0.99  
% 2.64/0.99  ------ Preprocessing
% 2.64/0.99  
% 2.64/0.99  num_of_splits:                          0
% 2.64/0.99  num_of_split_atoms:                     0
% 2.64/0.99  num_of_reused_defs:                     0
% 2.64/0.99  num_eq_ax_congr_red:                    8
% 2.64/0.99  num_of_sem_filtered_clauses:            1
% 2.64/0.99  num_of_subtypes:                        0
% 2.64/0.99  monotx_restored_types:                  0
% 2.64/0.99  sat_num_of_epr_types:                   0
% 2.64/0.99  sat_num_of_non_cyclic_types:            0
% 2.64/0.99  sat_guarded_non_collapsed_types:        0
% 2.64/0.99  num_pure_diseq_elim:                    0
% 2.64/0.99  simp_replaced_by:                       0
% 2.64/0.99  res_preprocessed:                       123
% 2.64/0.99  prep_upred:                             0
% 2.64/0.99  prep_unflattend:                        10
% 2.64/0.99  smt_new_axioms:                         0
% 2.64/0.99  pred_elim_cands:                        2
% 2.64/0.99  pred_elim:                              4
% 2.64/0.99  pred_elim_cl:                           4
% 2.64/0.99  pred_elim_cycles:                       6
% 2.64/0.99  merged_defs:                            0
% 2.64/0.99  merged_defs_ncl:                        0
% 2.64/0.99  bin_hyper_res:                          0
% 2.64/0.99  prep_cycles:                            4
% 2.64/0.99  pred_elim_time:                         0.003
% 2.64/0.99  splitting_time:                         0.
% 2.64/0.99  sem_filter_time:                        0.
% 2.64/0.99  monotx_time:                            0.
% 2.64/0.99  subtype_inf_time:                       0.
% 2.64/0.99  
% 2.64/0.99  ------ Problem properties
% 2.64/0.99  
% 2.64/0.99  clauses:                                23
% 2.64/0.99  conjectures:                            2
% 2.64/0.99  epr:                                    4
% 2.64/0.99  horn:                                   21
% 2.64/0.99  ground:                                 4
% 2.64/0.99  unary:                                  11
% 2.64/0.99  binary:                                 4
% 2.64/0.99  lits:                                   43
% 2.64/0.99  lits_eq:                                22
% 2.64/0.99  fd_pure:                                0
% 2.64/0.99  fd_pseudo:                              0
% 2.64/0.99  fd_cond:                                1
% 2.64/0.99  fd_pseudo_cond:                         2
% 2.64/0.99  ac_symbols:                             0
% 2.64/0.99  
% 2.64/0.99  ------ Propositional Solver
% 2.64/0.99  
% 2.64/0.99  prop_solver_calls:                      28
% 2.64/0.99  prop_fast_solver_calls:                 660
% 2.64/0.99  smt_solver_calls:                       0
% 2.64/0.99  smt_fast_solver_calls:                  0
% 2.64/0.99  prop_num_of_clauses:                    1328
% 2.64/0.99  prop_preprocess_simplified:             4512
% 2.64/0.99  prop_fo_subsumed:                       9
% 2.64/0.99  prop_solver_time:                       0.
% 2.64/0.99  smt_solver_time:                        0.
% 2.64/0.99  smt_fast_solver_time:                   0.
% 2.64/0.99  prop_fast_solver_time:                  0.
% 2.64/0.99  prop_unsat_core_time:                   0.
% 2.64/0.99  
% 2.64/0.99  ------ QBF
% 2.64/0.99  
% 2.64/0.99  qbf_q_res:                              0
% 2.64/0.99  qbf_num_tautologies:                    0
% 2.64/0.99  qbf_prep_cycles:                        0
% 2.64/0.99  
% 2.64/0.99  ------ BMC1
% 2.64/0.99  
% 2.64/0.99  bmc1_current_bound:                     -1
% 2.64/0.99  bmc1_last_solved_bound:                 -1
% 2.64/0.99  bmc1_unsat_core_size:                   -1
% 2.64/0.99  bmc1_unsat_core_parents_size:           -1
% 2.64/0.99  bmc1_merge_next_fun:                    0
% 2.64/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.64/0.99  
% 2.64/0.99  ------ Instantiation
% 2.64/0.99  
% 2.64/0.99  inst_num_of_clauses:                    455
% 2.64/0.99  inst_num_in_passive:                    31
% 2.64/0.99  inst_num_in_active:                     283
% 2.64/0.99  inst_num_in_unprocessed:                141
% 2.64/0.99  inst_num_of_loops:                      290
% 2.64/0.99  inst_num_of_learning_restarts:          0
% 2.64/0.99  inst_num_moves_active_passive:          4
% 2.64/0.99  inst_lit_activity:                      0
% 2.64/0.99  inst_lit_activity_moves:                0
% 2.64/0.99  inst_num_tautologies:                   0
% 2.64/0.99  inst_num_prop_implied:                  0
% 2.64/0.99  inst_num_existing_simplified:           0
% 2.64/0.99  inst_num_eq_res_simplified:             0
% 2.64/0.99  inst_num_child_elim:                    0
% 2.64/0.99  inst_num_of_dismatching_blockings:      87
% 2.64/0.99  inst_num_of_non_proper_insts:           590
% 2.64/0.99  inst_num_of_duplicates:                 0
% 2.64/0.99  inst_inst_num_from_inst_to_res:         0
% 2.64/0.99  inst_dismatching_checking_time:         0.
% 2.64/0.99  
% 2.64/0.99  ------ Resolution
% 2.64/0.99  
% 2.64/0.99  res_num_of_clauses:                     0
% 2.64/0.99  res_num_in_passive:                     0
% 2.64/0.99  res_num_in_active:                      0
% 2.64/0.99  res_num_of_loops:                       127
% 2.64/0.99  res_forward_subset_subsumed:            147
% 2.64/0.99  res_backward_subset_subsumed:           0
% 2.64/0.99  res_forward_subsumed:                   0
% 2.64/0.99  res_backward_subsumed:                  0
% 2.64/0.99  res_forward_subsumption_resolution:     0
% 2.64/0.99  res_backward_subsumption_resolution:    0
% 2.64/0.99  res_clause_to_clause_subsumption:       130
% 2.64/0.99  res_orphan_elimination:                 0
% 2.64/0.99  res_tautology_del:                      35
% 2.64/0.99  res_num_eq_res_simplified:              0
% 2.64/0.99  res_num_sel_changes:                    0
% 2.64/0.99  res_moves_from_active_to_pass:          0
% 2.64/0.99  
% 2.64/0.99  ------ Superposition
% 2.64/0.99  
% 2.64/0.99  sup_time_total:                         0.
% 2.64/0.99  sup_time_generating:                    0.
% 2.64/0.99  sup_time_sim_full:                      0.
% 2.64/0.99  sup_time_sim_immed:                     0.
% 2.64/0.99  
% 2.64/0.99  sup_num_of_clauses:                     40
% 2.64/0.99  sup_num_in_active:                      28
% 2.64/0.99  sup_num_in_passive:                     12
% 2.64/0.99  sup_num_of_loops:                       56
% 2.64/0.99  sup_fw_superposition:                   45
% 2.64/0.99  sup_bw_superposition:                   16
% 2.64/0.99  sup_immediate_simplified:               37
% 2.64/0.99  sup_given_eliminated:                   0
% 2.64/0.99  comparisons_done:                       0
% 2.64/0.99  comparisons_avoided:                    0
% 2.64/0.99  
% 2.64/0.99  ------ Simplifications
% 2.64/0.99  
% 2.64/0.99  
% 2.64/0.99  sim_fw_subset_subsumed:                 7
% 2.64/0.99  sim_bw_subset_subsumed:                 1
% 2.64/0.99  sim_fw_subsumed:                        16
% 2.64/0.99  sim_bw_subsumed:                        1
% 2.64/0.99  sim_fw_subsumption_res:                 1
% 2.64/0.99  sim_bw_subsumption_res:                 0
% 2.64/0.99  sim_tautology_del:                      0
% 2.64/0.99  sim_eq_tautology_del:                   7
% 2.64/0.99  sim_eq_res_simp:                        0
% 2.64/0.99  sim_fw_demodulated:                     4
% 2.64/0.99  sim_bw_demodulated:                     29
% 2.64/0.99  sim_light_normalised:                   20
% 2.64/0.99  sim_joinable_taut:                      0
% 2.64/0.99  sim_joinable_simp:                      0
% 2.64/0.99  sim_ac_normalised:                      0
% 2.64/0.99  sim_smt_subsumption:                    0
% 2.64/0.99  
%------------------------------------------------------------------------------
