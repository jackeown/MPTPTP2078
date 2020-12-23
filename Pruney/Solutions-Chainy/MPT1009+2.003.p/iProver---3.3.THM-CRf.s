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
% DateTime   : Thu Dec  3 12:05:29 EST 2020

% Result     : Theorem 0.37s
% Output     : CNFRefutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 967 expanded)
%              Number of clauses        :   85 ( 156 expanded)
%              Number of leaves         :   28 ( 259 expanded)
%              Depth                    :   27
%              Number of atoms          :  408 (1753 expanded)
%              Number of equality atoms :  189 ( 946 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f29,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f45,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f46,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f45])).

fof(f55,plain,
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

fof(f56,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f55])).

fof(f94,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f67,f68])).

fof(f98,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f66,f97])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f65,f98])).

fof(f100,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f64,f99])).

fof(f101,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f63,f100])).

fof(f102,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f62,f101])).

fof(f108,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f94,f102])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f49])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f105,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f69,f102,f102])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f88,f102,f102])).

fof(f93,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f56])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f96,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f56])).

fof(f107,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f96,f102,f102])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
     => ( r1_tarski(k1_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(flattening,[],[f43])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(k1_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f47])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f114,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f73])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f61,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f20,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f16,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f19,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f19])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1142,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_26,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_15,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_26,c_15])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_385,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_25])).

cnf(c_386,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_385])).

cnf(c_1137,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_386])).

cnf(c_1538,plain,
    ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1137])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1152,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5929,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1538,c_1152])).

cnf(c_7034,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 = X0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5929,c_1152])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1333,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1334,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1333])).

cnf(c_23,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1147,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1146,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2130,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1142,c_1146])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1148,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2602,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2130,c_1148])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_11,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_169,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18,c_13,c_11])).

cnf(c_170,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_169])).

cnf(c_1140,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_170])).

cnf(c_3449,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2602,c_1140])).

cnf(c_24,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_362,plain,
    ( ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_32])).

cnf(c_363,plain,
    ( ~ v1_relat_1(sK3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_362])).

cnf(c_1138,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_364,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_1339,plain,
    ( k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1138,c_34,c_364,c_1334])).

cnf(c_1340,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(renaming,[status(thm)],[c_1339])).

cnf(c_7035,plain,
    ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5929,c_1340])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1145,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4017,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1142,c_1145])).

cnf(c_29,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1143,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4296,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4017,c_1143])).

cnf(c_7214,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7035,c_4296])).

cnf(c_7305,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3449,c_7214])).

cnf(c_7791,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7305,c_34,c_1334])).

cnf(c_7792,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7791])).

cnf(c_7797,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_7792])).

cnf(c_8081,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7034,c_34,c_1334,c_7797])).

cnf(c_7042,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5929,c_1142])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
    | ~ r1_tarski(k1_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
    | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_1894,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
    | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1397])).

cnf(c_1895,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1894])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1398,plain,
    ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2008,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1398])).

cnf(c_2009,plain,
    ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2008])).

cnf(c_7078,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7042,c_34,c_1895,c_2009])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1150,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7083,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7078,c_1150])).

cnf(c_8088,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8081,c_7083])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_8148,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8088,c_9])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1155,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_8456,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8148,c_1155])).

cnf(c_9555,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8456,c_4296])).

cnf(c_22,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_16,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1149,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1616,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_22,c_1149])).

cnf(c_2603,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_1616,c_1148])).

cnf(c_20,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1941,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1147,c_1155])).

cnf(c_2018,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1941,c_1616])).

cnf(c_2613,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_2603,c_20,c_2018])).

cnf(c_9599,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9555,c_2613])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1156,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_9959,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9599,c_1156])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 12:39:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 0.37/1.07  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.37/1.07  
% 0.37/1.07  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.37/1.07  
% 0.37/1.07  ------  iProver source info
% 0.37/1.07  
% 0.37/1.07  git: date: 2020-06-30 10:37:57 +0100
% 0.37/1.07  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.37/1.07  git: non_committed_changes: false
% 0.37/1.07  git: last_make_outside_of_git: false
% 0.37/1.07  
% 0.37/1.07  ------ 
% 0.37/1.07  
% 0.37/1.07  ------ Input Options
% 0.37/1.07  
% 0.37/1.07  --out_options                           all
% 0.37/1.07  --tptp_safe_out                         true
% 0.37/1.07  --problem_path                          ""
% 0.37/1.07  --include_path                          ""
% 0.37/1.07  --clausifier                            res/vclausify_rel
% 0.37/1.07  --clausifier_options                    --mode clausify
% 0.37/1.07  --stdin                                 false
% 0.37/1.07  --stats_out                             all
% 0.37/1.07  
% 0.37/1.07  ------ General Options
% 0.37/1.07  
% 0.37/1.07  --fof                                   false
% 0.37/1.07  --time_out_real                         305.
% 0.37/1.07  --time_out_virtual                      -1.
% 0.37/1.07  --symbol_type_check                     false
% 0.37/1.07  --clausify_out                          false
% 0.37/1.07  --sig_cnt_out                           false
% 0.37/1.07  --trig_cnt_out                          false
% 0.37/1.07  --trig_cnt_out_tolerance                1.
% 0.37/1.07  --trig_cnt_out_sk_spl                   false
% 0.37/1.07  --abstr_cl_out                          false
% 0.37/1.07  
% 0.37/1.07  ------ Global Options
% 0.37/1.07  
% 0.37/1.07  --schedule                              default
% 0.37/1.07  --add_important_lit                     false
% 0.37/1.07  --prop_solver_per_cl                    1000
% 0.37/1.07  --min_unsat_core                        false
% 0.37/1.07  --soft_assumptions                      false
% 0.37/1.07  --soft_lemma_size                       3
% 0.37/1.07  --prop_impl_unit_size                   0
% 0.37/1.07  --prop_impl_unit                        []
% 0.37/1.07  --share_sel_clauses                     true
% 0.37/1.07  --reset_solvers                         false
% 0.37/1.07  --bc_imp_inh                            [conj_cone]
% 0.37/1.07  --conj_cone_tolerance                   3.
% 0.37/1.07  --extra_neg_conj                        none
% 0.37/1.07  --large_theory_mode                     true
% 0.37/1.07  --prolific_symb_bound                   200
% 0.37/1.07  --lt_threshold                          2000
% 0.37/1.07  --clause_weak_htbl                      true
% 0.37/1.07  --gc_record_bc_elim                     false
% 0.37/1.07  
% 0.37/1.07  ------ Preprocessing Options
% 0.37/1.07  
% 0.37/1.07  --preprocessing_flag                    true
% 0.37/1.07  --time_out_prep_mult                    0.1
% 0.37/1.07  --splitting_mode                        input
% 0.37/1.07  --splitting_grd                         true
% 0.37/1.07  --splitting_cvd                         false
% 0.37/1.07  --splitting_cvd_svl                     false
% 0.37/1.07  --splitting_nvd                         32
% 0.37/1.07  --sub_typing                            true
% 0.37/1.07  --prep_gs_sim                           true
% 0.37/1.07  --prep_unflatten                        true
% 0.37/1.07  --prep_res_sim                          true
% 0.37/1.07  --prep_upred                            true
% 0.37/1.07  --prep_sem_filter                       exhaustive
% 0.37/1.07  --prep_sem_filter_out                   false
% 0.37/1.07  --pred_elim                             true
% 0.37/1.07  --res_sim_input                         true
% 0.37/1.07  --eq_ax_congr_red                       true
% 0.37/1.07  --pure_diseq_elim                       true
% 0.37/1.07  --brand_transform                       false
% 0.37/1.07  --non_eq_to_eq                          false
% 0.37/1.07  --prep_def_merge                        true
% 0.37/1.07  --prep_def_merge_prop_impl              false
% 0.37/1.07  --prep_def_merge_mbd                    true
% 0.37/1.07  --prep_def_merge_tr_red                 false
% 0.37/1.07  --prep_def_merge_tr_cl                  false
% 0.37/1.07  --smt_preprocessing                     true
% 0.37/1.07  --smt_ac_axioms                         fast
% 0.37/1.07  --preprocessed_out                      false
% 0.37/1.07  --preprocessed_stats                    false
% 0.37/1.07  
% 0.37/1.07  ------ Abstraction refinement Options
% 0.37/1.07  
% 0.37/1.07  --abstr_ref                             []
% 0.37/1.07  --abstr_ref_prep                        false
% 0.37/1.07  --abstr_ref_until_sat                   false
% 0.37/1.07  --abstr_ref_sig_restrict                funpre
% 0.37/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 0.37/1.07  --abstr_ref_under                       []
% 0.37/1.07  
% 0.37/1.07  ------ SAT Options
% 0.37/1.07  
% 0.37/1.07  --sat_mode                              false
% 0.37/1.07  --sat_fm_restart_options                ""
% 0.37/1.07  --sat_gr_def                            false
% 0.37/1.07  --sat_epr_types                         true
% 0.37/1.07  --sat_non_cyclic_types                  false
% 0.37/1.07  --sat_finite_models                     false
% 0.37/1.07  --sat_fm_lemmas                         false
% 0.37/1.07  --sat_fm_prep                           false
% 0.37/1.07  --sat_fm_uc_incr                        true
% 0.37/1.07  --sat_out_model                         small
% 0.37/1.07  --sat_out_clauses                       false
% 0.37/1.07  
% 0.37/1.07  ------ QBF Options
% 0.37/1.07  
% 0.37/1.07  --qbf_mode                              false
% 0.37/1.07  --qbf_elim_univ                         false
% 0.37/1.07  --qbf_dom_inst                          none
% 0.37/1.07  --qbf_dom_pre_inst                      false
% 0.37/1.07  --qbf_sk_in                             false
% 0.37/1.07  --qbf_pred_elim                         true
% 0.37/1.07  --qbf_split                             512
% 0.37/1.07  
% 0.37/1.07  ------ BMC1 Options
% 0.37/1.07  
% 0.37/1.07  --bmc1_incremental                      false
% 0.37/1.07  --bmc1_axioms                           reachable_all
% 0.37/1.07  --bmc1_min_bound                        0
% 0.37/1.07  --bmc1_max_bound                        -1
% 0.37/1.07  --bmc1_max_bound_default                -1
% 0.37/1.07  --bmc1_symbol_reachability              true
% 0.37/1.07  --bmc1_property_lemmas                  false
% 0.37/1.07  --bmc1_k_induction                      false
% 0.37/1.07  --bmc1_non_equiv_states                 false
% 0.37/1.07  --bmc1_deadlock                         false
% 0.37/1.07  --bmc1_ucm                              false
% 0.37/1.07  --bmc1_add_unsat_core                   none
% 0.37/1.07  --bmc1_unsat_core_children              false
% 0.37/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 0.37/1.07  --bmc1_out_stat                         full
% 0.37/1.07  --bmc1_ground_init                      false
% 0.37/1.07  --bmc1_pre_inst_next_state              false
% 0.37/1.07  --bmc1_pre_inst_state                   false
% 0.37/1.07  --bmc1_pre_inst_reach_state             false
% 0.37/1.07  --bmc1_out_unsat_core                   false
% 0.37/1.07  --bmc1_aig_witness_out                  false
% 0.37/1.07  --bmc1_verbose                          false
% 0.37/1.07  --bmc1_dump_clauses_tptp                false
% 0.37/1.07  --bmc1_dump_unsat_core_tptp             false
% 0.37/1.07  --bmc1_dump_file                        -
% 0.37/1.07  --bmc1_ucm_expand_uc_limit              128
% 0.37/1.07  --bmc1_ucm_n_expand_iterations          6
% 0.37/1.07  --bmc1_ucm_extend_mode                  1
% 0.37/1.07  --bmc1_ucm_init_mode                    2
% 0.37/1.07  --bmc1_ucm_cone_mode                    none
% 0.37/1.07  --bmc1_ucm_reduced_relation_type        0
% 0.37/1.07  --bmc1_ucm_relax_model                  4
% 0.37/1.07  --bmc1_ucm_full_tr_after_sat            true
% 0.37/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 0.37/1.07  --bmc1_ucm_layered_model                none
% 0.37/1.07  --bmc1_ucm_max_lemma_size               10
% 0.37/1.07  
% 0.37/1.07  ------ AIG Options
% 0.37/1.07  
% 0.37/1.07  --aig_mode                              false
% 0.37/1.07  
% 0.37/1.07  ------ Instantiation Options
% 0.37/1.07  
% 0.37/1.07  --instantiation_flag                    true
% 0.37/1.07  --inst_sos_flag                         false
% 0.37/1.07  --inst_sos_phase                        true
% 0.37/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.37/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.37/1.07  --inst_lit_sel_side                     num_symb
% 0.37/1.07  --inst_solver_per_active                1400
% 0.37/1.07  --inst_solver_calls_frac                1.
% 0.37/1.07  --inst_passive_queue_type               priority_queues
% 0.37/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.37/1.07  --inst_passive_queues_freq              [25;2]
% 0.37/1.07  --inst_dismatching                      true
% 0.37/1.07  --inst_eager_unprocessed_to_passive     true
% 0.37/1.07  --inst_prop_sim_given                   true
% 0.37/1.07  --inst_prop_sim_new                     false
% 0.37/1.07  --inst_subs_new                         false
% 0.37/1.07  --inst_eq_res_simp                      false
% 0.37/1.07  --inst_subs_given                       false
% 0.37/1.07  --inst_orphan_elimination               true
% 0.37/1.07  --inst_learning_loop_flag               true
% 0.37/1.07  --inst_learning_start                   3000
% 0.37/1.07  --inst_learning_factor                  2
% 0.37/1.07  --inst_start_prop_sim_after_learn       3
% 0.37/1.07  --inst_sel_renew                        solver
% 0.37/1.07  --inst_lit_activity_flag                true
% 0.37/1.07  --inst_restr_to_given                   false
% 0.37/1.07  --inst_activity_threshold               500
% 0.37/1.07  --inst_out_proof                        true
% 0.37/1.07  
% 0.37/1.07  ------ Resolution Options
% 0.37/1.07  
% 0.37/1.07  --resolution_flag                       true
% 0.37/1.07  --res_lit_sel                           adaptive
% 0.37/1.07  --res_lit_sel_side                      none
% 0.37/1.07  --res_ordering                          kbo
% 0.37/1.07  --res_to_prop_solver                    active
% 0.37/1.07  --res_prop_simpl_new                    false
% 0.37/1.07  --res_prop_simpl_given                  true
% 0.37/1.07  --res_passive_queue_type                priority_queues
% 0.37/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.37/1.07  --res_passive_queues_freq               [15;5]
% 0.37/1.07  --res_forward_subs                      full
% 0.37/1.07  --res_backward_subs                     full
% 0.37/1.07  --res_forward_subs_resolution           true
% 0.37/1.07  --res_backward_subs_resolution          true
% 0.37/1.07  --res_orphan_elimination                true
% 0.37/1.07  --res_time_limit                        2.
% 0.37/1.07  --res_out_proof                         true
% 0.37/1.07  
% 0.37/1.07  ------ Superposition Options
% 0.37/1.07  
% 0.37/1.07  --superposition_flag                    true
% 0.37/1.07  --sup_passive_queue_type                priority_queues
% 0.37/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.37/1.07  --sup_passive_queues_freq               [8;1;4]
% 0.37/1.07  --demod_completeness_check              fast
% 0.37/1.07  --demod_use_ground                      true
% 0.37/1.07  --sup_to_prop_solver                    passive
% 0.37/1.07  --sup_prop_simpl_new                    true
% 0.37/1.07  --sup_prop_simpl_given                  true
% 0.37/1.07  --sup_fun_splitting                     false
% 0.37/1.07  --sup_smt_interval                      50000
% 0.37/1.07  
% 0.37/1.07  ------ Superposition Simplification Setup
% 0.37/1.07  
% 0.37/1.07  --sup_indices_passive                   []
% 0.37/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 0.37/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.07  --sup_full_bw                           [BwDemod]
% 0.37/1.07  --sup_immed_triv                        [TrivRules]
% 0.37/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.07  --sup_immed_bw_main                     []
% 0.37/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 0.37/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.07  
% 0.37/1.07  ------ Combination Options
% 0.37/1.07  
% 0.37/1.07  --comb_res_mult                         3
% 0.37/1.07  --comb_sup_mult                         2
% 0.37/1.07  --comb_inst_mult                        10
% 0.37/1.07  
% 0.37/1.07  ------ Debug Options
% 0.37/1.07  
% 0.37/1.07  --dbg_backtrace                         false
% 0.37/1.07  --dbg_dump_prop_clauses                 false
% 0.37/1.07  --dbg_dump_prop_clauses_file            -
% 0.37/1.07  --dbg_out_stat                          false
% 0.37/1.07  ------ Parsing...
% 0.37/1.07  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.37/1.07  
% 0.37/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 0.37/1.07  
% 0.37/1.07  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.37/1.07  
% 0.37/1.07  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.37/1.07  ------ Proving...
% 0.37/1.07  ------ Problem Properties 
% 0.37/1.07  
% 0.37/1.07  
% 0.37/1.07  clauses                                 29
% 0.37/1.07  conjectures                             3
% 0.37/1.07  EPR                                     6
% 0.37/1.07  Horn                                    27
% 0.37/1.07  unary                                   13
% 0.37/1.07  binary                                  8
% 0.37/1.07  lits                                    53
% 0.37/1.07  lits eq                                 17
% 0.37/1.07  fd_pure                                 0
% 0.37/1.07  fd_pseudo                               0
% 0.37/1.07  fd_cond                                 2
% 0.37/1.07  fd_pseudo_cond                          2
% 0.37/1.07  AC symbols                              0
% 0.37/1.07  
% 0.37/1.07  ------ Schedule dynamic 5 is on 
% 0.37/1.07  
% 0.37/1.07  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.37/1.07  
% 0.37/1.07  
% 0.37/1.07  ------ 
% 0.37/1.07  Current options:
% 0.37/1.07  ------ 
% 0.37/1.07  
% 0.37/1.07  ------ Input Options
% 0.37/1.07  
% 0.37/1.07  --out_options                           all
% 0.37/1.07  --tptp_safe_out                         true
% 0.37/1.07  --problem_path                          ""
% 0.37/1.07  --include_path                          ""
% 0.37/1.07  --clausifier                            res/vclausify_rel
% 0.37/1.07  --clausifier_options                    --mode clausify
% 0.37/1.07  --stdin                                 false
% 0.37/1.07  --stats_out                             all
% 0.37/1.07  
% 0.37/1.07  ------ General Options
% 0.37/1.07  
% 0.37/1.07  --fof                                   false
% 0.37/1.07  --time_out_real                         305.
% 0.37/1.07  --time_out_virtual                      -1.
% 0.37/1.07  --symbol_type_check                     false
% 0.37/1.07  --clausify_out                          false
% 0.37/1.07  --sig_cnt_out                           false
% 0.37/1.07  --trig_cnt_out                          false
% 0.37/1.07  --trig_cnt_out_tolerance                1.
% 0.37/1.07  --trig_cnt_out_sk_spl                   false
% 0.37/1.07  --abstr_cl_out                          false
% 0.37/1.07  
% 0.37/1.07  ------ Global Options
% 0.37/1.07  
% 0.37/1.07  --schedule                              default
% 0.37/1.07  --add_important_lit                     false
% 0.37/1.07  --prop_solver_per_cl                    1000
% 0.37/1.07  --min_unsat_core                        false
% 0.37/1.07  --soft_assumptions                      false
% 0.37/1.07  --soft_lemma_size                       3
% 0.37/1.07  --prop_impl_unit_size                   0
% 0.37/1.07  --prop_impl_unit                        []
% 0.37/1.07  --share_sel_clauses                     true
% 0.37/1.07  --reset_solvers                         false
% 0.37/1.07  --bc_imp_inh                            [conj_cone]
% 0.37/1.07  --conj_cone_tolerance                   3.
% 0.37/1.07  --extra_neg_conj                        none
% 0.37/1.07  --large_theory_mode                     true
% 0.37/1.07  --prolific_symb_bound                   200
% 0.37/1.07  --lt_threshold                          2000
% 0.37/1.07  --clause_weak_htbl                      true
% 0.37/1.07  --gc_record_bc_elim                     false
% 0.37/1.07  
% 0.37/1.07  ------ Preprocessing Options
% 0.37/1.07  
% 0.37/1.07  --preprocessing_flag                    true
% 0.37/1.07  --time_out_prep_mult                    0.1
% 0.37/1.07  --splitting_mode                        input
% 0.37/1.07  --splitting_grd                         true
% 0.37/1.07  --splitting_cvd                         false
% 0.37/1.07  --splitting_cvd_svl                     false
% 0.37/1.07  --splitting_nvd                         32
% 0.37/1.07  --sub_typing                            true
% 0.37/1.07  --prep_gs_sim                           true
% 0.37/1.07  --prep_unflatten                        true
% 0.37/1.07  --prep_res_sim                          true
% 0.37/1.07  --prep_upred                            true
% 0.37/1.07  --prep_sem_filter                       exhaustive
% 0.37/1.07  --prep_sem_filter_out                   false
% 0.37/1.07  --pred_elim                             true
% 0.37/1.07  --res_sim_input                         true
% 0.37/1.07  --eq_ax_congr_red                       true
% 0.37/1.07  --pure_diseq_elim                       true
% 0.37/1.07  --brand_transform                       false
% 0.37/1.07  --non_eq_to_eq                          false
% 0.37/1.07  --prep_def_merge                        true
% 0.37/1.07  --prep_def_merge_prop_impl              false
% 0.37/1.07  --prep_def_merge_mbd                    true
% 0.37/1.07  --prep_def_merge_tr_red                 false
% 0.37/1.07  --prep_def_merge_tr_cl                  false
% 0.37/1.07  --smt_preprocessing                     true
% 0.37/1.07  --smt_ac_axioms                         fast
% 0.37/1.07  --preprocessed_out                      false
% 0.37/1.07  --preprocessed_stats                    false
% 0.37/1.07  
% 0.37/1.07  ------ Abstraction refinement Options
% 0.37/1.07  
% 0.37/1.07  --abstr_ref                             []
% 0.37/1.07  --abstr_ref_prep                        false
% 0.37/1.07  --abstr_ref_until_sat                   false
% 0.37/1.07  --abstr_ref_sig_restrict                funpre
% 0.37/1.07  --abstr_ref_af_restrict_to_split_sk     false
% 0.37/1.07  --abstr_ref_under                       []
% 0.37/1.07  
% 0.37/1.07  ------ SAT Options
% 0.37/1.07  
% 0.37/1.07  --sat_mode                              false
% 0.37/1.07  --sat_fm_restart_options                ""
% 0.37/1.07  --sat_gr_def                            false
% 0.37/1.07  --sat_epr_types                         true
% 0.37/1.07  --sat_non_cyclic_types                  false
% 0.37/1.07  --sat_finite_models                     false
% 0.37/1.07  --sat_fm_lemmas                         false
% 0.37/1.07  --sat_fm_prep                           false
% 0.37/1.07  --sat_fm_uc_incr                        true
% 0.37/1.07  --sat_out_model                         small
% 0.37/1.07  --sat_out_clauses                       false
% 0.37/1.07  
% 0.37/1.07  ------ QBF Options
% 0.37/1.07  
% 0.37/1.07  --qbf_mode                              false
% 0.37/1.07  --qbf_elim_univ                         false
% 0.37/1.07  --qbf_dom_inst                          none
% 0.37/1.07  --qbf_dom_pre_inst                      false
% 0.37/1.07  --qbf_sk_in                             false
% 0.37/1.07  --qbf_pred_elim                         true
% 0.37/1.07  --qbf_split                             512
% 0.37/1.07  
% 0.37/1.07  ------ BMC1 Options
% 0.37/1.07  
% 0.37/1.07  --bmc1_incremental                      false
% 0.37/1.07  --bmc1_axioms                           reachable_all
% 0.37/1.07  --bmc1_min_bound                        0
% 0.37/1.07  --bmc1_max_bound                        -1
% 0.37/1.07  --bmc1_max_bound_default                -1
% 0.37/1.07  --bmc1_symbol_reachability              true
% 0.37/1.07  --bmc1_property_lemmas                  false
% 0.37/1.07  --bmc1_k_induction                      false
% 0.37/1.07  --bmc1_non_equiv_states                 false
% 0.37/1.07  --bmc1_deadlock                         false
% 0.37/1.07  --bmc1_ucm                              false
% 0.37/1.07  --bmc1_add_unsat_core                   none
% 0.37/1.07  --bmc1_unsat_core_children              false
% 0.37/1.07  --bmc1_unsat_core_extrapolate_axioms    false
% 0.37/1.07  --bmc1_out_stat                         full
% 0.37/1.07  --bmc1_ground_init                      false
% 0.37/1.07  --bmc1_pre_inst_next_state              false
% 0.37/1.07  --bmc1_pre_inst_state                   false
% 0.37/1.07  --bmc1_pre_inst_reach_state             false
% 0.37/1.07  --bmc1_out_unsat_core                   false
% 0.37/1.07  --bmc1_aig_witness_out                  false
% 0.37/1.07  --bmc1_verbose                          false
% 0.37/1.07  --bmc1_dump_clauses_tptp                false
% 0.37/1.07  --bmc1_dump_unsat_core_tptp             false
% 0.37/1.07  --bmc1_dump_file                        -
% 0.37/1.07  --bmc1_ucm_expand_uc_limit              128
% 0.37/1.07  --bmc1_ucm_n_expand_iterations          6
% 0.37/1.07  --bmc1_ucm_extend_mode                  1
% 0.37/1.07  --bmc1_ucm_init_mode                    2
% 0.37/1.07  --bmc1_ucm_cone_mode                    none
% 0.37/1.07  --bmc1_ucm_reduced_relation_type        0
% 0.37/1.07  --bmc1_ucm_relax_model                  4
% 0.37/1.07  --bmc1_ucm_full_tr_after_sat            true
% 0.37/1.07  --bmc1_ucm_expand_neg_assumptions       false
% 0.37/1.07  --bmc1_ucm_layered_model                none
% 0.37/1.07  --bmc1_ucm_max_lemma_size               10
% 0.37/1.07  
% 0.37/1.07  ------ AIG Options
% 0.37/1.07  
% 0.37/1.07  --aig_mode                              false
% 0.37/1.07  
% 0.37/1.07  ------ Instantiation Options
% 0.37/1.07  
% 0.37/1.07  --instantiation_flag                    true
% 0.37/1.07  --inst_sos_flag                         false
% 0.37/1.07  --inst_sos_phase                        true
% 0.37/1.07  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.37/1.07  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.37/1.07  --inst_lit_sel_side                     none
% 0.37/1.07  --inst_solver_per_active                1400
% 0.37/1.07  --inst_solver_calls_frac                1.
% 0.37/1.07  --inst_passive_queue_type               priority_queues
% 0.37/1.07  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.37/1.07  --inst_passive_queues_freq              [25;2]
% 0.37/1.07  --inst_dismatching                      true
% 0.37/1.07  --inst_eager_unprocessed_to_passive     true
% 0.37/1.07  --inst_prop_sim_given                   true
% 0.37/1.07  --inst_prop_sim_new                     false
% 0.37/1.07  --inst_subs_new                         false
% 0.37/1.07  --inst_eq_res_simp                      false
% 0.37/1.07  --inst_subs_given                       false
% 0.37/1.07  --inst_orphan_elimination               true
% 0.37/1.07  --inst_learning_loop_flag               true
% 0.37/1.07  --inst_learning_start                   3000
% 0.37/1.07  --inst_learning_factor                  2
% 0.37/1.07  --inst_start_prop_sim_after_learn       3
% 0.37/1.07  --inst_sel_renew                        solver
% 0.37/1.07  --inst_lit_activity_flag                true
% 0.37/1.07  --inst_restr_to_given                   false
% 0.37/1.07  --inst_activity_threshold               500
% 0.37/1.07  --inst_out_proof                        true
% 0.37/1.07  
% 0.37/1.07  ------ Resolution Options
% 0.37/1.07  
% 0.37/1.07  --resolution_flag                       false
% 0.37/1.07  --res_lit_sel                           adaptive
% 0.37/1.07  --res_lit_sel_side                      none
% 0.37/1.07  --res_ordering                          kbo
% 0.37/1.07  --res_to_prop_solver                    active
% 0.37/1.07  --res_prop_simpl_new                    false
% 0.37/1.07  --res_prop_simpl_given                  true
% 0.37/1.07  --res_passive_queue_type                priority_queues
% 0.37/1.07  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.37/1.07  --res_passive_queues_freq               [15;5]
% 0.37/1.07  --res_forward_subs                      full
% 0.37/1.07  --res_backward_subs                     full
% 0.37/1.07  --res_forward_subs_resolution           true
% 0.37/1.07  --res_backward_subs_resolution          true
% 0.37/1.07  --res_orphan_elimination                true
% 0.37/1.07  --res_time_limit                        2.
% 0.37/1.07  --res_out_proof                         true
% 0.37/1.07  
% 0.37/1.07  ------ Superposition Options
% 0.37/1.07  
% 0.37/1.07  --superposition_flag                    true
% 0.37/1.07  --sup_passive_queue_type                priority_queues
% 0.37/1.07  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.37/1.07  --sup_passive_queues_freq               [8;1;4]
% 0.37/1.07  --demod_completeness_check              fast
% 0.37/1.07  --demod_use_ground                      true
% 0.37/1.07  --sup_to_prop_solver                    passive
% 0.37/1.07  --sup_prop_simpl_new                    true
% 0.37/1.07  --sup_prop_simpl_given                  true
% 0.37/1.07  --sup_fun_splitting                     false
% 0.37/1.07  --sup_smt_interval                      50000
% 0.37/1.07  
% 0.37/1.07  ------ Superposition Simplification Setup
% 0.37/1.07  
% 0.37/1.07  --sup_indices_passive                   []
% 0.37/1.07  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.07  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.07  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.37/1.07  --sup_full_triv                         [TrivRules;PropSubs]
% 0.37/1.07  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.07  --sup_full_bw                           [BwDemod]
% 0.37/1.07  --sup_immed_triv                        [TrivRules]
% 0.37/1.07  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.37/1.07  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.07  --sup_immed_bw_main                     []
% 0.37/1.07  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.07  --sup_input_triv                        [Unflattening;TrivRules]
% 0.37/1.07  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.37/1.07  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.37/1.07  
% 0.37/1.07  ------ Combination Options
% 0.37/1.07  
% 0.37/1.07  --comb_res_mult                         3
% 0.37/1.07  --comb_sup_mult                         2
% 0.37/1.07  --comb_inst_mult                        10
% 0.37/1.07  
% 0.37/1.07  ------ Debug Options
% 0.37/1.07  
% 0.37/1.07  --dbg_backtrace                         false
% 0.37/1.07  --dbg_dump_prop_clauses                 false
% 0.37/1.07  --dbg_dump_prop_clauses_file            -
% 0.37/1.07  --dbg_out_stat                          false
% 0.37/1.07  
% 0.37/1.07  
% 0.37/1.07  
% 0.37/1.07  
% 0.37/1.07  ------ Proving...
% 0.37/1.07  
% 0.37/1.07  
% 0.37/1.07  % SZS status Theorem for theBenchmark.p
% 0.37/1.07  
% 0.37/1.07   Resolution empty clause
% 0.37/1.07  
% 0.37/1.07  % SZS output start CNFRefutation for theBenchmark.p
% 0.37/1.07  
% 0.37/1.07  fof(f27,conjecture,(
% 0.37/1.07    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f28,negated_conjecture,(
% 0.37/1.07    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.37/1.07    inference(negated_conjecture,[],[f27])).
% 0.37/1.07  
% 0.37/1.07  fof(f29,plain,(
% 0.37/1.07    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 0.37/1.07    inference(pure_predicate_removal,[],[f28])).
% 0.37/1.07  
% 0.37/1.07  fof(f45,plain,(
% 0.37/1.07    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 0.37/1.07    inference(ennf_transformation,[],[f29])).
% 0.37/1.07  
% 0.37/1.07  fof(f46,plain,(
% 0.37/1.07    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 0.37/1.07    inference(flattening,[],[f45])).
% 0.37/1.07  
% 0.37/1.07  fof(f55,plain,(
% 0.37/1.07    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 0.37/1.07    introduced(choice_axiom,[])).
% 0.37/1.07  
% 0.37/1.07  fof(f56,plain,(
% 0.37/1.07    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 0.37/1.07    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f55])).
% 0.37/1.07  
% 0.37/1.07  fof(f94,plain,(
% 0.37/1.07    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 0.37/1.07    inference(cnf_transformation,[],[f56])).
% 0.37/1.07  
% 0.37/1.07  fof(f4,axiom,(
% 0.37/1.07    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f62,plain,(
% 0.37/1.07    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f4])).
% 0.37/1.07  
% 0.37/1.07  fof(f5,axiom,(
% 0.37/1.07    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f63,plain,(
% 0.37/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f5])).
% 0.37/1.07  
% 0.37/1.07  fof(f6,axiom,(
% 0.37/1.07    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f64,plain,(
% 0.37/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f6])).
% 0.37/1.07  
% 0.37/1.07  fof(f7,axiom,(
% 0.37/1.07    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f65,plain,(
% 0.37/1.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f7])).
% 0.37/1.07  
% 0.37/1.07  fof(f8,axiom,(
% 0.37/1.07    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f66,plain,(
% 0.37/1.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f8])).
% 0.37/1.07  
% 0.37/1.07  fof(f9,axiom,(
% 0.37/1.07    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f67,plain,(
% 0.37/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f9])).
% 0.37/1.07  
% 0.37/1.07  fof(f10,axiom,(
% 0.37/1.07    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f68,plain,(
% 0.37/1.07    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f10])).
% 0.37/1.07  
% 0.37/1.07  fof(f97,plain,(
% 0.37/1.07    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.37/1.07    inference(definition_unfolding,[],[f67,f68])).
% 0.37/1.07  
% 0.37/1.07  fof(f98,plain,(
% 0.37/1.07    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.37/1.07    inference(definition_unfolding,[],[f66,f97])).
% 0.37/1.07  
% 0.37/1.07  fof(f99,plain,(
% 0.37/1.07    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.37/1.07    inference(definition_unfolding,[],[f65,f98])).
% 0.37/1.07  
% 0.37/1.07  fof(f100,plain,(
% 0.37/1.07    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.37/1.07    inference(definition_unfolding,[],[f64,f99])).
% 0.37/1.07  
% 0.37/1.07  fof(f101,plain,(
% 0.37/1.07    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.37/1.07    inference(definition_unfolding,[],[f63,f100])).
% 0.37/1.07  
% 0.37/1.07  fof(f102,plain,(
% 0.37/1.07    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.37/1.07    inference(definition_unfolding,[],[f62,f101])).
% 0.37/1.07  
% 0.37/1.07  fof(f108,plain,(
% 0.37/1.07    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 0.37/1.07    inference(definition_unfolding,[],[f94,f102])).
% 0.37/1.07  
% 0.37/1.07  fof(f24,axiom,(
% 0.37/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f30,plain,(
% 0.37/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.37/1.07    inference(pure_predicate_removal,[],[f24])).
% 0.37/1.07  
% 0.37/1.07  fof(f41,plain,(
% 0.37/1.07    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.07    inference(ennf_transformation,[],[f30])).
% 0.37/1.07  
% 0.37/1.07  fof(f90,plain,(
% 0.37/1.07    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.07    inference(cnf_transformation,[],[f41])).
% 0.37/1.07  
% 0.37/1.07  fof(f15,axiom,(
% 0.37/1.07    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f33,plain,(
% 0.37/1.07    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.37/1.07    inference(ennf_transformation,[],[f15])).
% 0.37/1.07  
% 0.37/1.07  fof(f54,plain,(
% 0.37/1.07    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.37/1.07    inference(nnf_transformation,[],[f33])).
% 0.37/1.07  
% 0.37/1.07  fof(f78,plain,(
% 0.37/1.07    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f54])).
% 0.37/1.07  
% 0.37/1.07  fof(f23,axiom,(
% 0.37/1.07    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f40,plain,(
% 0.37/1.07    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.07    inference(ennf_transformation,[],[f23])).
% 0.37/1.07  
% 0.37/1.07  fof(f89,plain,(
% 0.37/1.07    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.07    inference(cnf_transformation,[],[f40])).
% 0.37/1.07  
% 0.37/1.07  fof(f11,axiom,(
% 0.37/1.07    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f49,plain,(
% 0.37/1.07    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.37/1.07    inference(nnf_transformation,[],[f11])).
% 0.37/1.07  
% 0.37/1.07  fof(f50,plain,(
% 0.37/1.07    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.37/1.07    inference(flattening,[],[f49])).
% 0.37/1.07  
% 0.37/1.07  fof(f69,plain,(
% 0.37/1.07    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.37/1.07    inference(cnf_transformation,[],[f50])).
% 0.37/1.07  
% 0.37/1.07  fof(f105,plain,(
% 0.37/1.07    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.37/1.07    inference(definition_unfolding,[],[f69,f102,f102])).
% 0.37/1.07  
% 0.37/1.07  fof(f21,axiom,(
% 0.37/1.07    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f37,plain,(
% 0.37/1.07    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.37/1.07    inference(ennf_transformation,[],[f21])).
% 0.37/1.07  
% 0.37/1.07  fof(f87,plain,(
% 0.37/1.07    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f37])).
% 0.37/1.07  
% 0.37/1.07  fof(f17,axiom,(
% 0.37/1.07    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f34,plain,(
% 0.37/1.07    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.37/1.07    inference(ennf_transformation,[],[f17])).
% 0.37/1.07  
% 0.37/1.07  fof(f81,plain,(
% 0.37/1.07    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f34])).
% 0.37/1.07  
% 0.37/1.07  fof(f18,axiom,(
% 0.37/1.07    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f35,plain,(
% 0.37/1.07    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.37/1.07    inference(ennf_transformation,[],[f18])).
% 0.37/1.07  
% 0.37/1.07  fof(f36,plain,(
% 0.37/1.07    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.37/1.07    inference(flattening,[],[f35])).
% 0.37/1.07  
% 0.37/1.07  fof(f83,plain,(
% 0.37/1.07    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f36])).
% 0.37/1.07  
% 0.37/1.07  fof(f14,axiom,(
% 0.37/1.07    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f32,plain,(
% 0.37/1.07    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.37/1.07    inference(ennf_transformation,[],[f14])).
% 0.37/1.07  
% 0.37/1.07  fof(f77,plain,(
% 0.37/1.07    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f32])).
% 0.37/1.07  
% 0.37/1.07  fof(f13,axiom,(
% 0.37/1.07    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f53,plain,(
% 0.37/1.07    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.37/1.07    inference(nnf_transformation,[],[f13])).
% 0.37/1.07  
% 0.37/1.07  fof(f76,plain,(
% 0.37/1.07    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f53])).
% 0.37/1.07  
% 0.37/1.07  fof(f22,axiom,(
% 0.37/1.07    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f38,plain,(
% 0.37/1.07    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.37/1.07    inference(ennf_transformation,[],[f22])).
% 0.37/1.07  
% 0.37/1.07  fof(f39,plain,(
% 0.37/1.07    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.37/1.07    inference(flattening,[],[f38])).
% 0.37/1.07  
% 0.37/1.07  fof(f88,plain,(
% 0.37/1.07    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f39])).
% 0.37/1.07  
% 0.37/1.07  fof(f106,plain,(
% 0.37/1.07    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.37/1.07    inference(definition_unfolding,[],[f88,f102,f102])).
% 0.37/1.07  
% 0.37/1.07  fof(f93,plain,(
% 0.37/1.07    v1_funct_1(sK3)),
% 0.37/1.07    inference(cnf_transformation,[],[f56])).
% 0.37/1.07  
% 0.37/1.07  fof(f25,axiom,(
% 0.37/1.07    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f42,plain,(
% 0.37/1.07    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.37/1.07    inference(ennf_transformation,[],[f25])).
% 0.37/1.07  
% 0.37/1.07  fof(f91,plain,(
% 0.37/1.07    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.37/1.07    inference(cnf_transformation,[],[f42])).
% 0.37/1.07  
% 0.37/1.07  fof(f96,plain,(
% 0.37/1.07    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 0.37/1.07    inference(cnf_transformation,[],[f56])).
% 0.37/1.07  
% 0.37/1.07  fof(f107,plain,(
% 0.37/1.07    ~r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 0.37/1.07    inference(definition_unfolding,[],[f96,f102,f102])).
% 0.37/1.07  
% 0.37/1.07  fof(f26,axiom,(
% 0.37/1.07    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) => (r1_tarski(k1_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f43,plain,(
% 0.37/1.07    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.37/1.07    inference(ennf_transformation,[],[f26])).
% 0.37/1.07  
% 0.37/1.07  fof(f44,plain,(
% 0.37/1.07    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))))),
% 0.37/1.07    inference(flattening,[],[f43])).
% 0.37/1.07  
% 0.37/1.07  fof(f92,plain,(
% 0.37/1.07    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(k1_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))) )),
% 0.37/1.07    inference(cnf_transformation,[],[f44])).
% 0.37/1.07  
% 0.37/1.07  fof(f1,axiom,(
% 0.37/1.07    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f47,plain,(
% 0.37/1.07    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.37/1.07    inference(nnf_transformation,[],[f1])).
% 0.37/1.07  
% 0.37/1.07  fof(f48,plain,(
% 0.37/1.07    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.37/1.07    inference(flattening,[],[f47])).
% 0.37/1.07  
% 0.37/1.07  fof(f58,plain,(
% 0.37/1.07    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.37/1.07    inference(cnf_transformation,[],[f48])).
% 0.37/1.07  
% 0.37/1.07  fof(f109,plain,(
% 0.37/1.07    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.37/1.07    inference(equality_resolution,[],[f58])).
% 0.37/1.07  
% 0.37/1.07  fof(f75,plain,(
% 0.37/1.07    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.37/1.07    inference(cnf_transformation,[],[f53])).
% 0.37/1.07  
% 0.37/1.07  fof(f12,axiom,(
% 0.37/1.07    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f51,plain,(
% 0.37/1.07    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.37/1.07    inference(nnf_transformation,[],[f12])).
% 0.37/1.07  
% 0.37/1.07  fof(f52,plain,(
% 0.37/1.07    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.37/1.07    inference(flattening,[],[f51])).
% 0.37/1.07  
% 0.37/1.07  fof(f73,plain,(
% 0.37/1.07    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 0.37/1.07    inference(cnf_transformation,[],[f52])).
% 0.37/1.07  
% 0.37/1.07  fof(f114,plain,(
% 0.37/1.07    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.37/1.07    inference(equality_resolution,[],[f73])).
% 0.37/1.07  
% 0.37/1.07  fof(f3,axiom,(
% 0.37/1.07    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f31,plain,(
% 0.37/1.07    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.37/1.07    inference(ennf_transformation,[],[f3])).
% 0.37/1.07  
% 0.37/1.07  fof(f61,plain,(
% 0.37/1.07    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f31])).
% 0.37/1.07  
% 0.37/1.07  fof(f20,axiom,(
% 0.37/1.07    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f86,plain,(
% 0.37/1.07    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.37/1.07    inference(cnf_transformation,[],[f20])).
% 0.37/1.07  
% 0.37/1.07  fof(f16,axiom,(
% 0.37/1.07    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f80,plain,(
% 0.37/1.07    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.37/1.07    inference(cnf_transformation,[],[f16])).
% 0.37/1.07  
% 0.37/1.07  fof(f19,axiom,(
% 0.37/1.07    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f85,plain,(
% 0.37/1.07    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.37/1.07    inference(cnf_transformation,[],[f19])).
% 0.37/1.07  
% 0.37/1.07  fof(f2,axiom,(
% 0.37/1.07    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.37/1.07    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.37/1.07  
% 0.37/1.07  fof(f60,plain,(
% 0.37/1.07    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.37/1.07    inference(cnf_transformation,[],[f2])).
% 0.37/1.07  
% 0.37/1.07  cnf(c_31,negated_conjecture,
% 0.37/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 0.37/1.07      inference(cnf_transformation,[],[f108]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1142,plain,
% 0.37/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_26,plain,
% 0.37/1.07      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.37/1.07      inference(cnf_transformation,[],[f90]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_15,plain,
% 0.37/1.07      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 0.37/1.07      inference(cnf_transformation,[],[f78]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_381,plain,
% 0.37/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.07      | r1_tarski(k1_relat_1(X0),X1)
% 0.37/1.07      | ~ v1_relat_1(X0) ),
% 0.37/1.07      inference(resolution,[status(thm)],[c_26,c_15]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_25,plain,
% 0.37/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 0.37/1.07      inference(cnf_transformation,[],[f89]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_385,plain,
% 0.37/1.07      ( r1_tarski(k1_relat_1(X0),X1)
% 0.37/1.07      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 0.37/1.07      inference(global_propositional_subsumption,[status(thm)],[c_381,c_25]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_386,plain,
% 0.37/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.07      | r1_tarski(k1_relat_1(X0),X1) ),
% 0.37/1.07      inference(renaming,[status(thm)],[c_385]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1137,plain,
% 0.37/1.07      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 0.37/1.07      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_386]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1538,plain,
% 0.37/1.07      ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_1142,c_1137]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_7,plain,
% 0.37/1.07      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 0.37/1.07      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 0.37/1.07      | k1_xboole_0 = X0 ),
% 0.37/1.07      inference(cnf_transformation,[],[f105]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1152,plain,
% 0.37/1.07      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 0.37/1.07      | k1_xboole_0 = X1
% 0.37/1.07      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_5929,plain,
% 0.37/1.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 0.37/1.07      | k1_relat_1(sK3) = k1_xboole_0 ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_1538,c_1152]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_7034,plain,
% 0.37/1.07      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = X0
% 0.37/1.07      | k1_relat_1(sK3) = k1_xboole_0
% 0.37/1.07      | k1_xboole_0 = X0
% 0.37/1.07      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_5929,c_1152]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_34,plain,
% 0.37/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1333,plain,
% 0.37/1.07      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
% 0.37/1.07      | v1_relat_1(sK3) ),
% 0.37/1.07      inference(instantiation,[status(thm)],[c_25]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1334,plain,
% 0.37/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 0.37/1.07      | v1_relat_1(sK3) = iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_1333]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_23,plain,
% 0.37/1.07      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 0.37/1.07      inference(cnf_transformation,[],[f87]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1147,plain,
% 0.37/1.07      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 0.37/1.07      | v1_relat_1(X0) != iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1146,plain,
% 0.37/1.07      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 0.37/1.07      | v1_relat_1(X0) = iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_2130,plain,
% 0.37/1.07      ( v1_relat_1(sK3) = iProver_top ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_1142,c_1146]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_17,plain,
% 0.37/1.07      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 0.37/1.07      inference(cnf_transformation,[],[f81]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1148,plain,
% 0.37/1.07      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 0.37/1.07      | v1_relat_1(X0) != iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_2602,plain,
% 0.37/1.07      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_2130,c_1148]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_18,plain,
% 0.37/1.07      ( ~ r1_tarski(X0,X1)
% 0.37/1.07      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 0.37/1.07      | ~ v1_relat_1(X0)
% 0.37/1.07      | ~ v1_relat_1(X1) ),
% 0.37/1.07      inference(cnf_transformation,[],[f83]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_13,plain,
% 0.37/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 0.37/1.07      inference(cnf_transformation,[],[f77]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_11,plain,
% 0.37/1.07      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 0.37/1.07      inference(cnf_transformation,[],[f76]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_169,plain,
% 0.37/1.07      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 0.37/1.07      | ~ r1_tarski(X0,X1)
% 0.37/1.07      | ~ v1_relat_1(X1) ),
% 0.37/1.07      inference(global_propositional_subsumption,
% 0.37/1.07                [status(thm)],
% 0.37/1.07                [c_18,c_13,c_11]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_170,plain,
% 0.37/1.07      ( ~ r1_tarski(X0,X1)
% 0.37/1.07      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 0.37/1.07      | ~ v1_relat_1(X1) ),
% 0.37/1.07      inference(renaming,[status(thm)],[c_169]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1140,plain,
% 0.37/1.07      ( r1_tarski(X0,X1) != iProver_top
% 0.37/1.07      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 0.37/1.07      | v1_relat_1(X1) != iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_170]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_3449,plain,
% 0.37/1.07      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(X1)) = iProver_top
% 0.37/1.07      | r1_tarski(k7_relat_1(sK3,X0),X1) != iProver_top
% 0.37/1.07      | v1_relat_1(X1) != iProver_top ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_2602,c_1140]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_24,plain,
% 0.37/1.07      ( ~ v1_funct_1(X0)
% 0.37/1.07      | ~ v1_relat_1(X0)
% 0.37/1.07      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 0.37/1.07      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 0.37/1.07      inference(cnf_transformation,[],[f106]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_32,negated_conjecture,
% 0.37/1.07      ( v1_funct_1(sK3) ),
% 0.37/1.07      inference(cnf_transformation,[],[f93]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_362,plain,
% 0.37/1.07      ( ~ v1_relat_1(X0)
% 0.37/1.07      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 0.37/1.07      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 0.37/1.07      | sK3 != X0 ),
% 0.37/1.07      inference(resolution_lifted,[status(thm)],[c_24,c_32]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_363,plain,
% 0.37/1.07      ( ~ v1_relat_1(sK3)
% 0.37/1.07      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 0.37/1.07      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 0.37/1.07      inference(unflattening,[status(thm)],[c_362]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1138,plain,
% 0.37/1.07      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 0.37/1.07      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 0.37/1.07      | v1_relat_1(sK3) != iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_364,plain,
% 0.37/1.07      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 0.37/1.07      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 0.37/1.07      | v1_relat_1(sK3) != iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1339,plain,
% 0.37/1.07      ( k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 0.37/1.07      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3) ),
% 0.37/1.07      inference(global_propositional_subsumption,
% 0.37/1.07                [status(thm)],
% 0.37/1.07                [c_1138,c_34,c_364,c_1334]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1340,plain,
% 0.37/1.07      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 0.37/1.07      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 0.37/1.07      inference(renaming,[status(thm)],[c_1339]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_7035,plain,
% 0.37/1.07      ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 0.37/1.07      | k1_relat_1(sK3) = k1_xboole_0 ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_5929,c_1340]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_27,plain,
% 0.37/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.07      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 0.37/1.07      inference(cnf_transformation,[],[f91]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1145,plain,
% 0.37/1.07      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 0.37/1.07      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_4017,plain,
% 0.37/1.07      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_1142,c_1145]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_29,negated_conjecture,
% 0.37/1.07      ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 0.37/1.07      inference(cnf_transformation,[],[f107]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1143,plain,
% 0.37/1.07      ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_4296,plain,
% 0.37/1.07      ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 0.37/1.07      inference(demodulation,[status(thm)],[c_4017,c_1143]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_7214,plain,
% 0.37/1.07      ( k1_relat_1(sK3) = k1_xboole_0
% 0.37/1.07      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_7035,c_4296]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_7305,plain,
% 0.37/1.07      ( k1_relat_1(sK3) = k1_xboole_0
% 0.37/1.07      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 0.37/1.07      | v1_relat_1(sK3) != iProver_top ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_3449,c_7214]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_7791,plain,
% 0.37/1.07      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 0.37/1.07      | k1_relat_1(sK3) = k1_xboole_0 ),
% 0.37/1.07      inference(global_propositional_subsumption,
% 0.37/1.07                [status(thm)],
% 0.37/1.07                [c_7305,c_34,c_1334]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_7792,plain,
% 0.37/1.07      ( k1_relat_1(sK3) = k1_xboole_0
% 0.37/1.07      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
% 0.37/1.07      inference(renaming,[status(thm)],[c_7791]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_7797,plain,
% 0.37/1.07      ( k1_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_1147,c_7792]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_8081,plain,
% 0.37/1.07      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 0.37/1.07      inference(global_propositional_subsumption,
% 0.37/1.07                [status(thm)],
% 0.37/1.07                [c_7034,c_34,c_1334,c_7797]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_7042,plain,
% 0.37/1.07      ( k1_relat_1(sK3) = k1_xboole_0
% 0.37/1.07      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_5929,c_1142]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_28,plain,
% 0.37/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.07      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X3,X2)))
% 0.37/1.07      | ~ r1_tarski(k1_relat_1(X0),X3) ),
% 0.37/1.07      inference(cnf_transformation,[],[f92]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1397,plain,
% 0.37/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 0.37/1.07      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X2)))
% 0.37/1.07      | ~ r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 0.37/1.07      inference(instantiation,[status(thm)],[c_28]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1894,plain,
% 0.37/1.07      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
% 0.37/1.07      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1)))
% 0.37/1.07      | ~ r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 0.37/1.07      inference(instantiation,[status(thm)],[c_1397]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1895,plain,
% 0.37/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 0.37/1.07      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top
% 0.37/1.07      | r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) != iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_1894]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f109]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1398,plain,
% 0.37/1.07      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X0)) ),
% 0.37/1.07      inference(instantiation,[status(thm)],[c_1]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_2008,plain,
% 0.37/1.07      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) ),
% 0.37/1.07      inference(instantiation,[status(thm)],[c_1398]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_2009,plain,
% 0.37/1.07      ( r1_tarski(k1_relat_1(sK3),k1_relat_1(sK3)) = iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_2008]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_7078,plain,
% 0.37/1.07      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK1))) = iProver_top ),
% 0.37/1.07      inference(global_propositional_subsumption,
% 0.37/1.07                [status(thm)],
% 0.37/1.07                [c_7042,c_34,c_1895,c_2009]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_12,plain,
% 0.37/1.07      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 0.37/1.07      inference(cnf_transformation,[],[f75]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1150,plain,
% 0.37/1.07      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 0.37/1.07      | r1_tarski(X0,X1) = iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_7083,plain,
% 0.37/1.07      ( r1_tarski(sK3,k2_zfmisc_1(k1_relat_1(sK3),sK1)) = iProver_top ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_7078,c_1150]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_8088,plain,
% 0.37/1.07      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top ),
% 0.37/1.07      inference(demodulation,[status(thm)],[c_8081,c_7083]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_9,plain,
% 0.37/1.07      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.37/1.07      inference(cnf_transformation,[],[f114]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_8148,plain,
% 0.37/1.07      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 0.37/1.07      inference(demodulation,[status(thm)],[c_8088,c_9]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_4,plain,
% 0.37/1.07      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 0.37/1.07      inference(cnf_transformation,[],[f61]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1155,plain,
% 0.37/1.07      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_8456,plain,
% 0.37/1.07      ( sK3 = k1_xboole_0 ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_8148,c_1155]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_9555,plain,
% 0.37/1.07      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.37/1.07      inference(demodulation,[status(thm)],[c_8456,c_4296]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_22,plain,
% 0.37/1.07      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.37/1.07      inference(cnf_transformation,[],[f86]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_16,plain,
% 0.37/1.07      ( v1_relat_1(k6_relat_1(X0)) ),
% 0.37/1.07      inference(cnf_transformation,[],[f80]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1149,plain,
% 0.37/1.07      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1616,plain,
% 0.37/1.07      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_22,c_1149]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_2603,plain,
% 0.37/1.07      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_1616,c_1148]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_20,plain,
% 0.37/1.07      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 0.37/1.07      inference(cnf_transformation,[],[f85]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1941,plain,
% 0.37/1.07      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 0.37/1.07      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 0.37/1.07      inference(superposition,[status(thm)],[c_1147,c_1155]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_2018,plain,
% 0.37/1.07      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.37/1.07      inference(global_propositional_subsumption,[status(thm)],[c_1941,c_1616]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_2613,plain,
% 0.37/1.07      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 0.37/1.07      inference(light_normalisation,[status(thm)],[c_2603,c_20,c_2018]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_9599,plain,
% 0.37/1.07      ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 0.37/1.07      inference(demodulation,[status(thm)],[c_9555,c_2613]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_3,plain,
% 0.37/1.07      ( r1_tarski(k1_xboole_0,X0) ),
% 0.37/1.07      inference(cnf_transformation,[],[f60]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_1156,plain,
% 0.37/1.07      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 0.37/1.07      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 0.37/1.07  
% 0.37/1.07  cnf(c_9959,plain,
% 0.37/1.07      ( $false ),
% 0.37/1.07      inference(forward_subsumption_resolution,[status(thm)],[c_9599,c_1156]) ).
% 0.37/1.07  
% 0.37/1.07  
% 0.37/1.07  % SZS output end CNFRefutation for theBenchmark.p
% 0.37/1.07  
% 0.37/1.07  ------                               Statistics
% 0.37/1.07  
% 0.37/1.07  ------ General
% 0.37/1.07  
% 0.37/1.07  abstr_ref_over_cycles:                  0
% 0.37/1.07  abstr_ref_under_cycles:                 0
% 0.37/1.07  gc_basic_clause_elim:                   0
% 0.37/1.07  forced_gc_time:                         0
% 0.37/1.07  parsing_time:                           0.039
% 0.37/1.07  unif_index_cands_time:                  0.
% 0.37/1.07  unif_index_add_time:                    0.
% 0.37/1.07  orderings_time:                         0.
% 0.37/1.07  out_proof_time:                         0.011
% 0.37/1.07  total_time:                             0.312
% 0.37/1.07  num_of_symbols:                         51
% 0.37/1.07  num_of_terms:                           8155
% 0.37/1.07  
% 0.37/1.07  ------ Preprocessing
% 0.37/1.07  
% 0.37/1.07  num_of_splits:                          0
% 0.37/1.07  num_of_split_atoms:                     0
% 0.37/1.07  num_of_reused_defs:                     0
% 0.37/1.07  num_eq_ax_congr_red:                    14
% 0.37/1.07  num_of_sem_filtered_clauses:            1
% 0.37/1.07  num_of_subtypes:                        0
% 0.37/1.07  monotx_restored_types:                  0
% 0.37/1.07  sat_num_of_epr_types:                   0
% 0.37/1.07  sat_num_of_non_cyclic_types:            0
% 0.37/1.07  sat_guarded_non_collapsed_types:        0
% 0.37/1.07  num_pure_diseq_elim:                    0
% 0.37/1.07  simp_replaced_by:                       0
% 0.37/1.07  res_preprocessed:                       146
% 0.37/1.07  prep_upred:                             0
% 0.37/1.07  prep_unflattend:                        1
% 0.37/1.07  smt_new_axioms:                         0
% 0.37/1.07  pred_elim_cands:                        3
% 0.37/1.07  pred_elim:                              2
% 0.37/1.07  pred_elim_cl:                           3
% 0.37/1.07  pred_elim_cycles:                       4
% 0.37/1.07  merged_defs:                            8
% 0.37/1.07  merged_defs_ncl:                        0
% 0.37/1.07  bin_hyper_res:                          9
% 0.37/1.07  prep_cycles:                            4
% 0.37/1.07  pred_elim_time:                         0.009
% 0.37/1.07  splitting_time:                         0.
% 0.37/1.07  sem_filter_time:                        0.
% 0.37/1.07  monotx_time:                            0.
% 0.37/1.07  subtype_inf_time:                       0.
% 0.37/1.07  
% 0.37/1.07  ------ Problem properties
% 0.37/1.07  
% 0.37/1.07  clauses:                                29
% 0.37/1.07  conjectures:                            3
% 0.37/1.07  epr:                                    6
% 0.37/1.07  horn:                                   27
% 0.37/1.07  ground:                                 6
% 0.37/1.07  unary:                                  13
% 0.37/1.07  binary:                                 8
% 0.37/1.07  lits:                                   53
% 0.37/1.07  lits_eq:                                17
% 0.37/1.07  fd_pure:                                0
% 0.37/1.07  fd_pseudo:                              0
% 0.37/1.07  fd_cond:                                2
% 0.37/1.07  fd_pseudo_cond:                         2
% 0.37/1.07  ac_symbols:                             0
% 0.37/1.07  
% 0.37/1.07  ------ Propositional Solver
% 0.37/1.07  
% 0.37/1.07  prop_solver_calls:                      27
% 0.37/1.07  prop_fast_solver_calls:                 910
% 0.37/1.07  smt_solver_calls:                       0
% 0.37/1.07  smt_fast_solver_calls:                  0
% 0.37/1.07  prop_num_of_clauses:                    3858
% 0.37/1.07  prop_preprocess_simplified:             9532
% 0.37/1.07  prop_fo_subsumed:                       24
% 0.37/1.07  prop_solver_time:                       0.
% 0.37/1.07  smt_solver_time:                        0.
% 0.37/1.07  smt_fast_solver_time:                   0.
% 0.37/1.07  prop_fast_solver_time:                  0.
% 0.37/1.07  prop_unsat_core_time:                   0.
% 0.37/1.07  
% 0.37/1.07  ------ QBF
% 0.37/1.07  
% 0.37/1.07  qbf_q_res:                              0
% 0.37/1.07  qbf_num_tautologies:                    0
% 0.37/1.07  qbf_prep_cycles:                        0
% 0.37/1.07  
% 0.37/1.07  ------ BMC1
% 0.37/1.07  
% 0.37/1.07  bmc1_current_bound:                     -1
% 0.37/1.07  bmc1_last_solved_bound:                 -1
% 0.37/1.07  bmc1_unsat_core_size:                   -1
% 0.37/1.07  bmc1_unsat_core_parents_size:           -1
% 0.37/1.07  bmc1_merge_next_fun:                    0
% 0.37/1.07  bmc1_unsat_core_clauses_time:           0.
% 0.37/1.07  
% 0.37/1.07  ------ Instantiation
% 0.37/1.07  
% 0.37/1.07  inst_num_of_clauses:                    1069
% 0.37/1.07  inst_num_in_passive:                    235
% 0.37/1.07  inst_num_in_active:                     541
% 0.37/1.07  inst_num_in_unprocessed:                296
% 0.37/1.07  inst_num_of_loops:                      560
% 0.37/1.07  inst_num_of_learning_restarts:          0
% 0.37/1.07  inst_num_moves_active_passive:          17
% 0.37/1.07  inst_lit_activity:                      0
% 0.37/1.07  inst_lit_activity_moves:                0
% 0.37/1.07  inst_num_tautologies:                   0
% 0.37/1.07  inst_num_prop_implied:                  0
% 0.37/1.07  inst_num_existing_simplified:           0
% 0.37/1.07  inst_num_eq_res_simplified:             0
% 0.37/1.07  inst_num_child_elim:                    0
% 0.37/1.07  inst_num_of_dismatching_blockings:      441
% 0.37/1.07  inst_num_of_non_proper_insts:           1500
% 0.37/1.07  inst_num_of_duplicates:                 0
% 0.37/1.07  inst_inst_num_from_inst_to_res:         0
% 0.37/1.07  inst_dismatching_checking_time:         0.
% 0.37/1.07  
% 0.37/1.07  ------ Resolution
% 0.37/1.07  
% 0.37/1.07  res_num_of_clauses:                     0
% 0.37/1.07  res_num_in_passive:                     0
% 0.37/1.07  res_num_in_active:                      0
% 0.37/1.07  res_num_of_loops:                       150
% 0.37/1.07  res_forward_subset_subsumed:            144
% 0.37/1.07  res_backward_subset_subsumed:           14
% 0.37/1.07  res_forward_subsumed:                   0
% 0.37/1.07  res_backward_subsumed:                  0
% 0.37/1.07  res_forward_subsumption_resolution:     0
% 0.37/1.07  res_backward_subsumption_resolution:    0
% 0.37/1.07  res_clause_to_clause_subsumption:       671
% 0.37/1.07  res_orphan_elimination:                 0
% 0.37/1.07  res_tautology_del:                      101
% 0.37/1.07  res_num_eq_res_simplified:              0
% 0.37/1.07  res_num_sel_changes:                    0
% 0.37/1.07  res_moves_from_active_to_pass:          0
% 0.37/1.07  
% 0.37/1.07  ------ Superposition
% 0.37/1.07  
% 0.37/1.07  sup_time_total:                         0.
% 0.37/1.07  sup_time_generating:                    0.
% 0.37/1.07  sup_time_sim_full:                      0.
% 0.37/1.07  sup_time_sim_immed:                     0.
% 0.37/1.07  
% 0.37/1.07  sup_num_of_clauses:                     143
% 0.37/1.07  sup_num_in_active:                      56
% 0.37/1.07  sup_num_in_passive:                     87
% 0.37/1.07  sup_num_of_loops:                       110
% 0.37/1.07  sup_fw_superposition:                   165
% 0.37/1.07  sup_bw_superposition:                   130
% 0.37/1.07  sup_immediate_simplified:               114
% 0.37/1.07  sup_given_eliminated:                   1
% 0.37/1.07  comparisons_done:                       0
% 0.37/1.07  comparisons_avoided:                    3
% 0.37/1.07  
% 0.37/1.07  ------ Simplifications
% 0.37/1.07  
% 0.37/1.07  
% 0.37/1.07  sim_fw_subset_subsumed:                 25
% 0.37/1.07  sim_bw_subset_subsumed:                 15
% 0.37/1.07  sim_fw_subsumed:                        32
% 0.37/1.07  sim_bw_subsumed:                        1
% 0.37/1.07  sim_fw_subsumption_res:                 5
% 0.37/1.07  sim_bw_subsumption_res:                 0
% 0.37/1.07  sim_tautology_del:                      16
% 0.37/1.07  sim_eq_tautology_del:                   19
% 0.37/1.07  sim_eq_res_simp:                        0
% 0.37/1.07  sim_fw_demodulated:                     31
% 0.37/1.07  sim_bw_demodulated:                     51
% 0.37/1.07  sim_light_normalised:                   40
% 0.37/1.07  sim_joinable_taut:                      0
% 0.37/1.07  sim_joinable_simp:                      0
% 0.37/1.07  sim_ac_normalised:                      0
% 0.37/1.07  sim_smt_subsumption:                    0
% 0.37/1.07  
%------------------------------------------------------------------------------
