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
% DateTime   : Thu Dec  3 12:05:56 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 982 expanded)
%              Number of clauses        :   73 ( 205 expanded)
%              Number of leaves         :   23 ( 250 expanded)
%              Depth                    :   28
%              Number of atoms          :  350 (1898 expanded)
%              Number of equality atoms :  163 ( 843 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal clause size      :    8 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f23,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
        & v1_funct_2(X3,k1_tarski(X0),X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_2(X3,k1_tarski(X0),X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f25,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f41,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f46,plain,
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

fof(f47,plain,
    ( ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f46])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f4])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f7])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f53,f54])).

fof(f80,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f52,f79])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f82,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f81])).

fof(f83,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f82])).

fof(f84,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f48,f83])).

fof(f90,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f76,f84])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f14,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f17,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f55,f84,f84])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k1_tarski(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f88,plain,(
    ! [X0,X1] :
      ( k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f72,f84,f84])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f78,plain,(
    ~ r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(definition_unfolding,[],[f78,f84,f84])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f69,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

cnf(c_16,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1228,plain,
    ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1225,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1233,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1588,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_1233])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_187,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_4])).

cnf(c_188,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_187])).

cnf(c_225,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_188])).

cnf(c_1222,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_225])).

cnf(c_2145,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1588,c_1222])).

cnf(c_25,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1382,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
    | r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1383,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
    | r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1382])).

cnf(c_1390,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_225])).

cnf(c_1532,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1390])).

cnf(c_1533,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1532])).

cnf(c_9,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1545,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1546,plain,
    ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1545])).

cnf(c_2713,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2145,c_25,c_1383,c_1533,c_1546])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1231,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2718,plain,
    ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_2713,c_1231])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_142,plain,
    ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12,c_6,c_4])).

cnf(c_143,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(renaming,[status(thm)],[c_142])).

cnf(c_1223,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_143])).

cnf(c_3043,plain,
    ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(X1)) = iProver_top
    | r1_tarski(k7_relat_1(sK3,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2718,c_1223])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_325,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_8])).

cnf(c_1220,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_325])).

cnf(c_1571,plain,
    ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_1220])).

cnf(c_1867,plain,
    ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1571,c_25,c_1383,c_1533,c_1546])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1236,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
    | k1_xboole_0 = X1
    | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2436,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1867,c_1236])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_23,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_306,plain,
    ( ~ v1_relat_1(X0)
    | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
    | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_23])).

cnf(c_307,plain,
    ( ~ v1_relat_1(sK3)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_306])).

cnf(c_1221,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_307])).

cnf(c_2778,plain,
    ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2436,c_1221])).

cnf(c_2820,plain,
    ( ~ v1_relat_1(sK3)
    | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2778])).

cnf(c_3570,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2778,c_22,c_1382,c_1532,c_1545,c_2820])).

cnf(c_3571,plain,
    ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3570])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1227,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2273,plain,
    ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
    inference(superposition,[status(thm)],[c_1225,c_1227])).

cnf(c_20,negated_conjecture,
    ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1226,plain,
    ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2638,plain,
    ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2273,c_1226])).

cnf(c_3581,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3571,c_2638])).

cnf(c_5173,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3043,c_3581])).

cnf(c_5266,plain,
    ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5173,c_25,c_1383,c_1533,c_1546])).

cnf(c_5267,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_5266])).

cnf(c_5272,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1228,c_5267])).

cnf(c_5338,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5272,c_25,c_1383,c_1533,c_1546])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1229,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5380,plain,
    ( sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5338,c_1229])).

cnf(c_5851,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5380,c_25,c_1383,c_1533,c_1546])).

cnf(c_5869,plain,
    ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5851,c_2638])).

cnf(c_11,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_5878,plain,
    ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5869,c_11])).

cnf(c_3,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1235,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1587,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1235,c_1233])).

cnf(c_6053,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5878,c_1587])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n021.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 10:23:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.36/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.36/1.00  
% 3.36/1.00  ------  iProver source info
% 3.36/1.00  
% 3.36/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.36/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.36/1.00  git: non_committed_changes: false
% 3.36/1.00  git: last_make_outside_of_git: false
% 3.36/1.00  
% 3.36/1.00  ------ 
% 3.36/1.00  
% 3.36/1.00  ------ Input Options
% 3.36/1.00  
% 3.36/1.00  --out_options                           all
% 3.36/1.00  --tptp_safe_out                         true
% 3.36/1.00  --problem_path                          ""
% 3.36/1.00  --include_path                          ""
% 3.36/1.00  --clausifier                            res/vclausify_rel
% 3.36/1.00  --clausifier_options                    --mode clausify
% 3.36/1.00  --stdin                                 false
% 3.36/1.00  --stats_out                             all
% 3.36/1.00  
% 3.36/1.00  ------ General Options
% 3.36/1.00  
% 3.36/1.00  --fof                                   false
% 3.36/1.00  --time_out_real                         305.
% 3.36/1.00  --time_out_virtual                      -1.
% 3.36/1.00  --symbol_type_check                     false
% 3.36/1.00  --clausify_out                          false
% 3.36/1.00  --sig_cnt_out                           false
% 3.36/1.00  --trig_cnt_out                          false
% 3.36/1.00  --trig_cnt_out_tolerance                1.
% 3.36/1.00  --trig_cnt_out_sk_spl                   false
% 3.36/1.00  --abstr_cl_out                          false
% 3.36/1.00  
% 3.36/1.00  ------ Global Options
% 3.36/1.00  
% 3.36/1.00  --schedule                              default
% 3.36/1.00  --add_important_lit                     false
% 3.36/1.00  --prop_solver_per_cl                    1000
% 3.36/1.00  --min_unsat_core                        false
% 3.36/1.00  --soft_assumptions                      false
% 3.36/1.00  --soft_lemma_size                       3
% 3.36/1.00  --prop_impl_unit_size                   0
% 3.36/1.00  --prop_impl_unit                        []
% 3.36/1.00  --share_sel_clauses                     true
% 3.36/1.00  --reset_solvers                         false
% 3.36/1.00  --bc_imp_inh                            [conj_cone]
% 3.36/1.00  --conj_cone_tolerance                   3.
% 3.36/1.00  --extra_neg_conj                        none
% 3.36/1.00  --large_theory_mode                     true
% 3.36/1.00  --prolific_symb_bound                   200
% 3.36/1.00  --lt_threshold                          2000
% 3.36/1.00  --clause_weak_htbl                      true
% 3.36/1.00  --gc_record_bc_elim                     false
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing Options
% 3.36/1.00  
% 3.36/1.00  --preprocessing_flag                    true
% 3.36/1.00  --time_out_prep_mult                    0.1
% 3.36/1.00  --splitting_mode                        input
% 3.36/1.00  --splitting_grd                         true
% 3.36/1.00  --splitting_cvd                         false
% 3.36/1.00  --splitting_cvd_svl                     false
% 3.36/1.00  --splitting_nvd                         32
% 3.36/1.00  --sub_typing                            true
% 3.36/1.00  --prep_gs_sim                           true
% 3.36/1.00  --prep_unflatten                        true
% 3.36/1.00  --prep_res_sim                          true
% 3.36/1.00  --prep_upred                            true
% 3.36/1.00  --prep_sem_filter                       exhaustive
% 3.36/1.00  --prep_sem_filter_out                   false
% 3.36/1.00  --pred_elim                             true
% 3.36/1.00  --res_sim_input                         true
% 3.36/1.00  --eq_ax_congr_red                       true
% 3.36/1.00  --pure_diseq_elim                       true
% 3.36/1.00  --brand_transform                       false
% 3.36/1.00  --non_eq_to_eq                          false
% 3.36/1.00  --prep_def_merge                        true
% 3.36/1.00  --prep_def_merge_prop_impl              false
% 3.36/1.00  --prep_def_merge_mbd                    true
% 3.36/1.00  --prep_def_merge_tr_red                 false
% 3.36/1.00  --prep_def_merge_tr_cl                  false
% 3.36/1.00  --smt_preprocessing                     true
% 3.36/1.00  --smt_ac_axioms                         fast
% 3.36/1.00  --preprocessed_out                      false
% 3.36/1.00  --preprocessed_stats                    false
% 3.36/1.00  
% 3.36/1.00  ------ Abstraction refinement Options
% 3.36/1.00  
% 3.36/1.00  --abstr_ref                             []
% 3.36/1.00  --abstr_ref_prep                        false
% 3.36/1.00  --abstr_ref_until_sat                   false
% 3.36/1.00  --abstr_ref_sig_restrict                funpre
% 3.36/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/1.00  --abstr_ref_under                       []
% 3.36/1.00  
% 3.36/1.00  ------ SAT Options
% 3.36/1.00  
% 3.36/1.00  --sat_mode                              false
% 3.36/1.00  --sat_fm_restart_options                ""
% 3.36/1.00  --sat_gr_def                            false
% 3.36/1.00  --sat_epr_types                         true
% 3.36/1.00  --sat_non_cyclic_types                  false
% 3.36/1.00  --sat_finite_models                     false
% 3.36/1.00  --sat_fm_lemmas                         false
% 3.36/1.00  --sat_fm_prep                           false
% 3.36/1.00  --sat_fm_uc_incr                        true
% 3.36/1.00  --sat_out_model                         small
% 3.36/1.00  --sat_out_clauses                       false
% 3.36/1.00  
% 3.36/1.00  ------ QBF Options
% 3.36/1.00  
% 3.36/1.00  --qbf_mode                              false
% 3.36/1.00  --qbf_elim_univ                         false
% 3.36/1.00  --qbf_dom_inst                          none
% 3.36/1.00  --qbf_dom_pre_inst                      false
% 3.36/1.00  --qbf_sk_in                             false
% 3.36/1.00  --qbf_pred_elim                         true
% 3.36/1.00  --qbf_split                             512
% 3.36/1.00  
% 3.36/1.00  ------ BMC1 Options
% 3.36/1.00  
% 3.36/1.00  --bmc1_incremental                      false
% 3.36/1.00  --bmc1_axioms                           reachable_all
% 3.36/1.00  --bmc1_min_bound                        0
% 3.36/1.00  --bmc1_max_bound                        -1
% 3.36/1.00  --bmc1_max_bound_default                -1
% 3.36/1.00  --bmc1_symbol_reachability              true
% 3.36/1.00  --bmc1_property_lemmas                  false
% 3.36/1.00  --bmc1_k_induction                      false
% 3.36/1.00  --bmc1_non_equiv_states                 false
% 3.36/1.00  --bmc1_deadlock                         false
% 3.36/1.00  --bmc1_ucm                              false
% 3.36/1.00  --bmc1_add_unsat_core                   none
% 3.36/1.00  --bmc1_unsat_core_children              false
% 3.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/1.00  --bmc1_out_stat                         full
% 3.36/1.00  --bmc1_ground_init                      false
% 3.36/1.00  --bmc1_pre_inst_next_state              false
% 3.36/1.00  --bmc1_pre_inst_state                   false
% 3.36/1.00  --bmc1_pre_inst_reach_state             false
% 3.36/1.00  --bmc1_out_unsat_core                   false
% 3.36/1.00  --bmc1_aig_witness_out                  false
% 3.36/1.00  --bmc1_verbose                          false
% 3.36/1.00  --bmc1_dump_clauses_tptp                false
% 3.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.36/1.00  --bmc1_dump_file                        -
% 3.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.36/1.00  --bmc1_ucm_extend_mode                  1
% 3.36/1.00  --bmc1_ucm_init_mode                    2
% 3.36/1.00  --bmc1_ucm_cone_mode                    none
% 3.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.36/1.00  --bmc1_ucm_relax_model                  4
% 3.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/1.00  --bmc1_ucm_layered_model                none
% 3.36/1.00  --bmc1_ucm_max_lemma_size               10
% 3.36/1.00  
% 3.36/1.00  ------ AIG Options
% 3.36/1.00  
% 3.36/1.00  --aig_mode                              false
% 3.36/1.00  
% 3.36/1.00  ------ Instantiation Options
% 3.36/1.00  
% 3.36/1.00  --instantiation_flag                    true
% 3.36/1.00  --inst_sos_flag                         false
% 3.36/1.00  --inst_sos_phase                        true
% 3.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel_side                     num_symb
% 3.36/1.00  --inst_solver_per_active                1400
% 3.36/1.00  --inst_solver_calls_frac                1.
% 3.36/1.00  --inst_passive_queue_type               priority_queues
% 3.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/1.00  --inst_passive_queues_freq              [25;2]
% 3.36/1.00  --inst_dismatching                      true
% 3.36/1.00  --inst_eager_unprocessed_to_passive     true
% 3.36/1.00  --inst_prop_sim_given                   true
% 3.36/1.00  --inst_prop_sim_new                     false
% 3.36/1.00  --inst_subs_new                         false
% 3.36/1.00  --inst_eq_res_simp                      false
% 3.36/1.00  --inst_subs_given                       false
% 3.36/1.00  --inst_orphan_elimination               true
% 3.36/1.00  --inst_learning_loop_flag               true
% 3.36/1.00  --inst_learning_start                   3000
% 3.36/1.00  --inst_learning_factor                  2
% 3.36/1.00  --inst_start_prop_sim_after_learn       3
% 3.36/1.00  --inst_sel_renew                        solver
% 3.36/1.00  --inst_lit_activity_flag                true
% 3.36/1.00  --inst_restr_to_given                   false
% 3.36/1.00  --inst_activity_threshold               500
% 3.36/1.00  --inst_out_proof                        true
% 3.36/1.00  
% 3.36/1.00  ------ Resolution Options
% 3.36/1.00  
% 3.36/1.00  --resolution_flag                       true
% 3.36/1.00  --res_lit_sel                           adaptive
% 3.36/1.00  --res_lit_sel_side                      none
% 3.36/1.00  --res_ordering                          kbo
% 3.36/1.00  --res_to_prop_solver                    active
% 3.36/1.00  --res_prop_simpl_new                    false
% 3.36/1.00  --res_prop_simpl_given                  true
% 3.36/1.00  --res_passive_queue_type                priority_queues
% 3.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/1.00  --res_passive_queues_freq               [15;5]
% 3.36/1.00  --res_forward_subs                      full
% 3.36/1.00  --res_backward_subs                     full
% 3.36/1.00  --res_forward_subs_resolution           true
% 3.36/1.00  --res_backward_subs_resolution          true
% 3.36/1.00  --res_orphan_elimination                true
% 3.36/1.00  --res_time_limit                        2.
% 3.36/1.00  --res_out_proof                         true
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Options
% 3.36/1.00  
% 3.36/1.00  --superposition_flag                    true
% 3.36/1.00  --sup_passive_queue_type                priority_queues
% 3.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.36/1.00  --demod_completeness_check              fast
% 3.36/1.00  --demod_use_ground                      true
% 3.36/1.00  --sup_to_prop_solver                    passive
% 3.36/1.00  --sup_prop_simpl_new                    true
% 3.36/1.00  --sup_prop_simpl_given                  true
% 3.36/1.00  --sup_fun_splitting                     false
% 3.36/1.00  --sup_smt_interval                      50000
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Simplification Setup
% 3.36/1.00  
% 3.36/1.00  --sup_indices_passive                   []
% 3.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_full_bw                           [BwDemod]
% 3.36/1.00  --sup_immed_triv                        [TrivRules]
% 3.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_immed_bw_main                     []
% 3.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  
% 3.36/1.00  ------ Combination Options
% 3.36/1.00  
% 3.36/1.00  --comb_res_mult                         3
% 3.36/1.00  --comb_sup_mult                         2
% 3.36/1.00  --comb_inst_mult                        10
% 3.36/1.00  
% 3.36/1.00  ------ Debug Options
% 3.36/1.00  
% 3.36/1.00  --dbg_backtrace                         false
% 3.36/1.00  --dbg_dump_prop_clauses                 false
% 3.36/1.00  --dbg_dump_prop_clauses_file            -
% 3.36/1.00  --dbg_out_stat                          false
% 3.36/1.00  ------ Parsing...
% 3.36/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.36/1.00  ------ Proving...
% 3.36/1.00  ------ Problem Properties 
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  clauses                                 21
% 3.36/1.00  conjectures                             3
% 3.36/1.00  EPR                                     2
% 3.36/1.00  Horn                                    20
% 3.36/1.00  unary                                   8
% 3.36/1.00  binary                                  5
% 3.36/1.00  lits                                    42
% 3.36/1.00  lits eq                                 12
% 3.36/1.00  fd_pure                                 0
% 3.36/1.00  fd_pseudo                               0
% 3.36/1.00  fd_cond                                 2
% 3.36/1.00  fd_pseudo_cond                          1
% 3.36/1.00  AC symbols                              0
% 3.36/1.00  
% 3.36/1.00  ------ Schedule dynamic 5 is on 
% 3.36/1.00  
% 3.36/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  ------ 
% 3.36/1.00  Current options:
% 3.36/1.00  ------ 
% 3.36/1.00  
% 3.36/1.00  ------ Input Options
% 3.36/1.00  
% 3.36/1.00  --out_options                           all
% 3.36/1.00  --tptp_safe_out                         true
% 3.36/1.00  --problem_path                          ""
% 3.36/1.00  --include_path                          ""
% 3.36/1.00  --clausifier                            res/vclausify_rel
% 3.36/1.00  --clausifier_options                    --mode clausify
% 3.36/1.00  --stdin                                 false
% 3.36/1.00  --stats_out                             all
% 3.36/1.00  
% 3.36/1.00  ------ General Options
% 3.36/1.00  
% 3.36/1.00  --fof                                   false
% 3.36/1.00  --time_out_real                         305.
% 3.36/1.00  --time_out_virtual                      -1.
% 3.36/1.00  --symbol_type_check                     false
% 3.36/1.00  --clausify_out                          false
% 3.36/1.00  --sig_cnt_out                           false
% 3.36/1.00  --trig_cnt_out                          false
% 3.36/1.00  --trig_cnt_out_tolerance                1.
% 3.36/1.00  --trig_cnt_out_sk_spl                   false
% 3.36/1.00  --abstr_cl_out                          false
% 3.36/1.00  
% 3.36/1.00  ------ Global Options
% 3.36/1.00  
% 3.36/1.00  --schedule                              default
% 3.36/1.00  --add_important_lit                     false
% 3.36/1.00  --prop_solver_per_cl                    1000
% 3.36/1.00  --min_unsat_core                        false
% 3.36/1.00  --soft_assumptions                      false
% 3.36/1.00  --soft_lemma_size                       3
% 3.36/1.00  --prop_impl_unit_size                   0
% 3.36/1.00  --prop_impl_unit                        []
% 3.36/1.00  --share_sel_clauses                     true
% 3.36/1.00  --reset_solvers                         false
% 3.36/1.00  --bc_imp_inh                            [conj_cone]
% 3.36/1.00  --conj_cone_tolerance                   3.
% 3.36/1.00  --extra_neg_conj                        none
% 3.36/1.00  --large_theory_mode                     true
% 3.36/1.00  --prolific_symb_bound                   200
% 3.36/1.00  --lt_threshold                          2000
% 3.36/1.00  --clause_weak_htbl                      true
% 3.36/1.00  --gc_record_bc_elim                     false
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing Options
% 3.36/1.00  
% 3.36/1.00  --preprocessing_flag                    true
% 3.36/1.00  --time_out_prep_mult                    0.1
% 3.36/1.00  --splitting_mode                        input
% 3.36/1.00  --splitting_grd                         true
% 3.36/1.00  --splitting_cvd                         false
% 3.36/1.00  --splitting_cvd_svl                     false
% 3.36/1.00  --splitting_nvd                         32
% 3.36/1.00  --sub_typing                            true
% 3.36/1.00  --prep_gs_sim                           true
% 3.36/1.00  --prep_unflatten                        true
% 3.36/1.00  --prep_res_sim                          true
% 3.36/1.00  --prep_upred                            true
% 3.36/1.00  --prep_sem_filter                       exhaustive
% 3.36/1.00  --prep_sem_filter_out                   false
% 3.36/1.00  --pred_elim                             true
% 3.36/1.00  --res_sim_input                         true
% 3.36/1.00  --eq_ax_congr_red                       true
% 3.36/1.00  --pure_diseq_elim                       true
% 3.36/1.00  --brand_transform                       false
% 3.36/1.00  --non_eq_to_eq                          false
% 3.36/1.00  --prep_def_merge                        true
% 3.36/1.00  --prep_def_merge_prop_impl              false
% 3.36/1.00  --prep_def_merge_mbd                    true
% 3.36/1.00  --prep_def_merge_tr_red                 false
% 3.36/1.00  --prep_def_merge_tr_cl                  false
% 3.36/1.00  --smt_preprocessing                     true
% 3.36/1.00  --smt_ac_axioms                         fast
% 3.36/1.00  --preprocessed_out                      false
% 3.36/1.00  --preprocessed_stats                    false
% 3.36/1.00  
% 3.36/1.00  ------ Abstraction refinement Options
% 3.36/1.00  
% 3.36/1.00  --abstr_ref                             []
% 3.36/1.00  --abstr_ref_prep                        false
% 3.36/1.00  --abstr_ref_until_sat                   false
% 3.36/1.00  --abstr_ref_sig_restrict                funpre
% 3.36/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.36/1.00  --abstr_ref_under                       []
% 3.36/1.00  
% 3.36/1.00  ------ SAT Options
% 3.36/1.00  
% 3.36/1.00  --sat_mode                              false
% 3.36/1.00  --sat_fm_restart_options                ""
% 3.36/1.00  --sat_gr_def                            false
% 3.36/1.00  --sat_epr_types                         true
% 3.36/1.00  --sat_non_cyclic_types                  false
% 3.36/1.00  --sat_finite_models                     false
% 3.36/1.00  --sat_fm_lemmas                         false
% 3.36/1.00  --sat_fm_prep                           false
% 3.36/1.00  --sat_fm_uc_incr                        true
% 3.36/1.00  --sat_out_model                         small
% 3.36/1.00  --sat_out_clauses                       false
% 3.36/1.00  
% 3.36/1.00  ------ QBF Options
% 3.36/1.00  
% 3.36/1.00  --qbf_mode                              false
% 3.36/1.00  --qbf_elim_univ                         false
% 3.36/1.00  --qbf_dom_inst                          none
% 3.36/1.00  --qbf_dom_pre_inst                      false
% 3.36/1.00  --qbf_sk_in                             false
% 3.36/1.00  --qbf_pred_elim                         true
% 3.36/1.00  --qbf_split                             512
% 3.36/1.00  
% 3.36/1.00  ------ BMC1 Options
% 3.36/1.00  
% 3.36/1.00  --bmc1_incremental                      false
% 3.36/1.00  --bmc1_axioms                           reachable_all
% 3.36/1.00  --bmc1_min_bound                        0
% 3.36/1.00  --bmc1_max_bound                        -1
% 3.36/1.00  --bmc1_max_bound_default                -1
% 3.36/1.00  --bmc1_symbol_reachability              true
% 3.36/1.00  --bmc1_property_lemmas                  false
% 3.36/1.00  --bmc1_k_induction                      false
% 3.36/1.00  --bmc1_non_equiv_states                 false
% 3.36/1.00  --bmc1_deadlock                         false
% 3.36/1.00  --bmc1_ucm                              false
% 3.36/1.00  --bmc1_add_unsat_core                   none
% 3.36/1.00  --bmc1_unsat_core_children              false
% 3.36/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.36/1.00  --bmc1_out_stat                         full
% 3.36/1.00  --bmc1_ground_init                      false
% 3.36/1.00  --bmc1_pre_inst_next_state              false
% 3.36/1.00  --bmc1_pre_inst_state                   false
% 3.36/1.00  --bmc1_pre_inst_reach_state             false
% 3.36/1.00  --bmc1_out_unsat_core                   false
% 3.36/1.00  --bmc1_aig_witness_out                  false
% 3.36/1.00  --bmc1_verbose                          false
% 3.36/1.00  --bmc1_dump_clauses_tptp                false
% 3.36/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.36/1.00  --bmc1_dump_file                        -
% 3.36/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.36/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.36/1.00  --bmc1_ucm_extend_mode                  1
% 3.36/1.00  --bmc1_ucm_init_mode                    2
% 3.36/1.00  --bmc1_ucm_cone_mode                    none
% 3.36/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.36/1.00  --bmc1_ucm_relax_model                  4
% 3.36/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.36/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.36/1.00  --bmc1_ucm_layered_model                none
% 3.36/1.00  --bmc1_ucm_max_lemma_size               10
% 3.36/1.00  
% 3.36/1.00  ------ AIG Options
% 3.36/1.00  
% 3.36/1.00  --aig_mode                              false
% 3.36/1.00  
% 3.36/1.00  ------ Instantiation Options
% 3.36/1.00  
% 3.36/1.00  --instantiation_flag                    true
% 3.36/1.00  --inst_sos_flag                         false
% 3.36/1.00  --inst_sos_phase                        true
% 3.36/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.36/1.00  --inst_lit_sel_side                     none
% 3.36/1.00  --inst_solver_per_active                1400
% 3.36/1.00  --inst_solver_calls_frac                1.
% 3.36/1.00  --inst_passive_queue_type               priority_queues
% 3.36/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.36/1.00  --inst_passive_queues_freq              [25;2]
% 3.36/1.00  --inst_dismatching                      true
% 3.36/1.00  --inst_eager_unprocessed_to_passive     true
% 3.36/1.00  --inst_prop_sim_given                   true
% 3.36/1.00  --inst_prop_sim_new                     false
% 3.36/1.00  --inst_subs_new                         false
% 3.36/1.00  --inst_eq_res_simp                      false
% 3.36/1.00  --inst_subs_given                       false
% 3.36/1.00  --inst_orphan_elimination               true
% 3.36/1.00  --inst_learning_loop_flag               true
% 3.36/1.00  --inst_learning_start                   3000
% 3.36/1.00  --inst_learning_factor                  2
% 3.36/1.00  --inst_start_prop_sim_after_learn       3
% 3.36/1.00  --inst_sel_renew                        solver
% 3.36/1.00  --inst_lit_activity_flag                true
% 3.36/1.00  --inst_restr_to_given                   false
% 3.36/1.00  --inst_activity_threshold               500
% 3.36/1.00  --inst_out_proof                        true
% 3.36/1.00  
% 3.36/1.00  ------ Resolution Options
% 3.36/1.00  
% 3.36/1.00  --resolution_flag                       false
% 3.36/1.00  --res_lit_sel                           adaptive
% 3.36/1.00  --res_lit_sel_side                      none
% 3.36/1.00  --res_ordering                          kbo
% 3.36/1.00  --res_to_prop_solver                    active
% 3.36/1.00  --res_prop_simpl_new                    false
% 3.36/1.00  --res_prop_simpl_given                  true
% 3.36/1.00  --res_passive_queue_type                priority_queues
% 3.36/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.36/1.00  --res_passive_queues_freq               [15;5]
% 3.36/1.00  --res_forward_subs                      full
% 3.36/1.00  --res_backward_subs                     full
% 3.36/1.00  --res_forward_subs_resolution           true
% 3.36/1.00  --res_backward_subs_resolution          true
% 3.36/1.00  --res_orphan_elimination                true
% 3.36/1.00  --res_time_limit                        2.
% 3.36/1.00  --res_out_proof                         true
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Options
% 3.36/1.00  
% 3.36/1.00  --superposition_flag                    true
% 3.36/1.00  --sup_passive_queue_type                priority_queues
% 3.36/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.36/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.36/1.00  --demod_completeness_check              fast
% 3.36/1.00  --demod_use_ground                      true
% 3.36/1.00  --sup_to_prop_solver                    passive
% 3.36/1.00  --sup_prop_simpl_new                    true
% 3.36/1.00  --sup_prop_simpl_given                  true
% 3.36/1.00  --sup_fun_splitting                     false
% 3.36/1.00  --sup_smt_interval                      50000
% 3.36/1.00  
% 3.36/1.00  ------ Superposition Simplification Setup
% 3.36/1.00  
% 3.36/1.00  --sup_indices_passive                   []
% 3.36/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.36/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.36/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_full_bw                           [BwDemod]
% 3.36/1.00  --sup_immed_triv                        [TrivRules]
% 3.36/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.36/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_immed_bw_main                     []
% 3.36/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.36/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.36/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.36/1.00  
% 3.36/1.00  ------ Combination Options
% 3.36/1.00  
% 3.36/1.00  --comb_res_mult                         3
% 3.36/1.00  --comb_sup_mult                         2
% 3.36/1.00  --comb_inst_mult                        10
% 3.36/1.00  
% 3.36/1.00  ------ Debug Options
% 3.36/1.00  
% 3.36/1.00  --dbg_backtrace                         false
% 3.36/1.00  --dbg_dump_prop_clauses                 false
% 3.36/1.00  --dbg_dump_prop_clauses_file            -
% 3.36/1.00  --dbg_out_stat                          false
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  ------ Proving...
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  % SZS status Theorem for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00   Resolution empty clause
% 3.36/1.00  
% 3.36/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  fof(f19,axiom,(
% 3.36/1.00    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f35,plain,(
% 3.36/1.00    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(ennf_transformation,[],[f19])).
% 3.36/1.00  
% 3.36/1.00  fof(f71,plain,(
% 3.36/1.00    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f35])).
% 3.36/1.00  
% 3.36/1.00  fof(f23,conjecture,(
% 3.36/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f24,negated_conjecture,(
% 3.36/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_2(X3,k1_tarski(X0),X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.36/1.00    inference(negated_conjecture,[],[f23])).
% 3.36/1.00  
% 3.36/1.00  fof(f25,plain,(
% 3.36/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0)))))),
% 3.36/1.00    inference(pure_predicate_removal,[],[f24])).
% 3.36/1.00  
% 3.36/1.00  fof(f40,plain,(
% 3.36/1.00    ? [X0,X1,X2,X3] : ((~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)))),
% 3.36/1.00    inference(ennf_transformation,[],[f25])).
% 3.36/1.00  
% 3.36/1.00  fof(f41,plain,(
% 3.36/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3))),
% 3.36/1.00    inference(flattening,[],[f40])).
% 3.36/1.00  
% 3.36/1.00  fof(f46,plain,(
% 3.36/1.00    ? [X0,X1,X2,X3] : (~r1_tarski(k7_relset_1(k1_tarski(X0),X1,X3,X2),k1_tarski(k1_funct_1(X3,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(X0),X1))) & v1_funct_1(X3)) => (~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3))),
% 3.36/1.00    introduced(choice_axiom,[])).
% 3.36/1.00  
% 3.36/1.00  fof(f47,plain,(
% 3.36/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1))) & v1_funct_1(sK3)),
% 3.36/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f46])).
% 3.36/1.00  
% 3.36/1.00  fof(f76,plain,(
% 3.36/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),sK1)))),
% 3.36/1.00    inference(cnf_transformation,[],[f47])).
% 3.36/1.00  
% 3.36/1.00  fof(f1,axiom,(
% 3.36/1.00    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f48,plain,(
% 3.36/1.00    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f1])).
% 3.36/1.00  
% 3.36/1.00  fof(f2,axiom,(
% 3.36/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f49,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f2])).
% 3.36/1.00  
% 3.36/1.00  fof(f3,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f50,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f3])).
% 3.36/1.00  
% 3.36/1.00  fof(f4,axiom,(
% 3.36/1.00    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f51,plain,(
% 3.36/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f4])).
% 3.36/1.00  
% 3.36/1.00  fof(f5,axiom,(
% 3.36/1.00    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f52,plain,(
% 3.36/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f5])).
% 3.36/1.00  
% 3.36/1.00  fof(f6,axiom,(
% 3.36/1.00    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f53,plain,(
% 3.36/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f6])).
% 3.36/1.00  
% 3.36/1.00  fof(f7,axiom,(
% 3.36/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f54,plain,(
% 3.36/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f7])).
% 3.36/1.00  
% 3.36/1.00  fof(f79,plain,(
% 3.36/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.36/1.00    inference(definition_unfolding,[],[f53,f54])).
% 3.36/1.00  
% 3.36/1.00  fof(f80,plain,(
% 3.36/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.36/1.00    inference(definition_unfolding,[],[f52,f79])).
% 3.36/1.00  
% 3.36/1.00  fof(f81,plain,(
% 3.36/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.36/1.00    inference(definition_unfolding,[],[f51,f80])).
% 3.36/1.00  
% 3.36/1.00  fof(f82,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.36/1.00    inference(definition_unfolding,[],[f50,f81])).
% 3.36/1.00  
% 3.36/1.00  fof(f83,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.36/1.00    inference(definition_unfolding,[],[f49,f82])).
% 3.36/1.00  
% 3.36/1.00  fof(f84,plain,(
% 3.36/1.00    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.36/1.00    inference(definition_unfolding,[],[f48,f83])).
% 3.36/1.00  
% 3.36/1.00  fof(f90,plain,(
% 3.36/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))),
% 3.36/1.00    inference(definition_unfolding,[],[f76,f84])).
% 3.36/1.00  
% 3.36/1.00  fof(f10,axiom,(
% 3.36/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f44,plain,(
% 3.36/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.36/1.00    inference(nnf_transformation,[],[f10])).
% 3.36/1.00  
% 3.36/1.00  fof(f59,plain,(
% 3.36/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f44])).
% 3.36/1.00  
% 3.36/1.00  fof(f12,axiom,(
% 3.36/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f28,plain,(
% 3.36/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.36/1.00    inference(ennf_transformation,[],[f12])).
% 3.36/1.00  
% 3.36/1.00  fof(f61,plain,(
% 3.36/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f28])).
% 3.36/1.00  
% 3.36/1.00  fof(f60,plain,(
% 3.36/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f44])).
% 3.36/1.00  
% 3.36/1.00  fof(f14,axiom,(
% 3.36/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f64,plain,(
% 3.36/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f14])).
% 3.36/1.00  
% 3.36/1.00  fof(f15,axiom,(
% 3.36/1.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f30,plain,(
% 3.36/1.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(ennf_transformation,[],[f15])).
% 3.36/1.00  
% 3.36/1.00  fof(f65,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f30])).
% 3.36/1.00  
% 3.36/1.00  fof(f17,axiom,(
% 3.36/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f31,plain,(
% 3.36/1.00    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.36/1.00    inference(ennf_transformation,[],[f17])).
% 3.36/1.00  
% 3.36/1.00  fof(f32,plain,(
% 3.36/1.00    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.36/1.00    inference(flattening,[],[f31])).
% 3.36/1.00  
% 3.36/1.00  fof(f68,plain,(
% 3.36/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f32])).
% 3.36/1.00  
% 3.36/1.00  fof(f21,axiom,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f26,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.36/1.00    inference(pure_predicate_removal,[],[f21])).
% 3.36/1.00  
% 3.36/1.00  fof(f38,plain,(
% 3.36/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(ennf_transformation,[],[f26])).
% 3.36/1.00  
% 3.36/1.00  fof(f73,plain,(
% 3.36/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f38])).
% 3.36/1.00  
% 3.36/1.00  fof(f13,axiom,(
% 3.36/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f29,plain,(
% 3.36/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(ennf_transformation,[],[f13])).
% 3.36/1.00  
% 3.36/1.00  fof(f45,plain,(
% 3.36/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(nnf_transformation,[],[f29])).
% 3.36/1.00  
% 3.36/1.00  fof(f62,plain,(
% 3.36/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f45])).
% 3.36/1.00  
% 3.36/1.00  fof(f8,axiom,(
% 3.36/1.00    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f42,plain,(
% 3.36/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.36/1.00    inference(nnf_transformation,[],[f8])).
% 3.36/1.00  
% 3.36/1.00  fof(f43,plain,(
% 3.36/1.00    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 3.36/1.00    inference(flattening,[],[f42])).
% 3.36/1.00  
% 3.36/1.00  fof(f55,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f43])).
% 3.36/1.00  
% 3.36/1.00  fof(f87,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 3.36/1.00    inference(definition_unfolding,[],[f55,f84,f84])).
% 3.36/1.00  
% 3.36/1.00  fof(f20,axiom,(
% 3.36/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1)))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f36,plain,(
% 3.36/1.00    ! [X0,X1] : ((k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.36/1.00    inference(ennf_transformation,[],[f20])).
% 3.36/1.00  
% 3.36/1.00  fof(f37,plain,(
% 3.36/1.00    ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.36/1.00    inference(flattening,[],[f36])).
% 3.36/1.00  
% 3.36/1.00  fof(f72,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k1_tarski(k1_funct_1(X1,X0)) = k2_relat_1(X1) | k1_tarski(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f37])).
% 3.36/1.00  
% 3.36/1.00  fof(f88,plain,(
% 3.36/1.00    ( ! [X0,X1] : (k6_enumset1(k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0),k1_funct_1(X1,X0)) = k2_relat_1(X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.36/1.00    inference(definition_unfolding,[],[f72,f84,f84])).
% 3.36/1.00  
% 3.36/1.00  fof(f75,plain,(
% 3.36/1.00    v1_funct_1(sK3)),
% 3.36/1.00    inference(cnf_transformation,[],[f47])).
% 3.36/1.00  
% 3.36/1.00  fof(f22,axiom,(
% 3.36/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f39,plain,(
% 3.36/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.36/1.00    inference(ennf_transformation,[],[f22])).
% 3.36/1.00  
% 3.36/1.00  fof(f74,plain,(
% 3.36/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f39])).
% 3.36/1.00  
% 3.36/1.00  fof(f78,plain,(
% 3.36/1.00    ~r1_tarski(k7_relset_1(k1_tarski(sK0),sK1,sK3,sK2),k1_tarski(k1_funct_1(sK3,sK0)))),
% 3.36/1.00    inference(cnf_transformation,[],[f47])).
% 3.36/1.00  
% 3.36/1.00  fof(f89,plain,(
% 3.36/1.00    ~r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)))),
% 3.36/1.00    inference(definition_unfolding,[],[f78,f84,f84])).
% 3.36/1.00  
% 3.36/1.00  fof(f18,axiom,(
% 3.36/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f33,plain,(
% 3.36/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.36/1.00    inference(ennf_transformation,[],[f18])).
% 3.36/1.00  
% 3.36/1.00  fof(f34,plain,(
% 3.36/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.36/1.00    inference(flattening,[],[f33])).
% 3.36/1.00  
% 3.36/1.00  fof(f69,plain,(
% 3.36/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f34])).
% 3.36/1.00  
% 3.36/1.00  fof(f16,axiom,(
% 3.36/1.00    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f66,plain,(
% 3.36/1.00    ( ! [X0] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)) )),
% 3.36/1.00    inference(cnf_transformation,[],[f16])).
% 3.36/1.00  
% 3.36/1.00  fof(f9,axiom,(
% 3.36/1.00    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.36/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.36/1.00  
% 3.36/1.00  fof(f58,plain,(
% 3.36/1.00    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.36/1.00    inference(cnf_transformation,[],[f9])).
% 3.36/1.00  
% 3.36/1.00  cnf(c_16,plain,
% 3.36/1.00      ( r1_tarski(k7_relat_1(X0,X1),X0) | ~ v1_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1228,plain,
% 3.36/1.00      ( r1_tarski(k7_relat_1(X0,X1),X0) = iProver_top
% 3.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_22,negated_conjecture,
% 3.36/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) ),
% 3.36/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1225,plain,
% 3.36/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.36/1.00      inference(cnf_transformation,[],[f59]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1233,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.36/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1588,plain,
% 3.36/1.00      ( r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1225,c_1233]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_4,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.36/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_187,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.36/1.00      inference(prop_impl,[status(thm)],[c_4]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_188,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.36/1.00      inference(renaming,[status(thm)],[c_187]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_225,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.36/1.00      inference(bin_hyper_res,[status(thm)],[c_6,c_188]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1222,plain,
% 3.36/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.36/1.00      | v1_relat_1(X1) != iProver_top
% 3.36/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_225]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2145,plain,
% 3.36/1.00      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 3.36/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1588,c_1222]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_25,plain,
% 3.36/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1382,plain,
% 3.36/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)))
% 3.36/1.00      | r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_5]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1383,plain,
% 3.36/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))) != iProver_top
% 3.36/1.00      | r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1382]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1390,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.36/1.00      | v1_relat_1(X0)
% 3.36/1.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_225]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1532,plain,
% 3.36/1.00      ( ~ r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
% 3.36/1.00      | ~ v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))
% 3.36/1.00      | v1_relat_1(sK3) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_1390]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1533,plain,
% 3.36/1.00      ( r1_tarski(sK3,k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 3.36/1.00      | v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) != iProver_top
% 3.36/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1532]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_9,plain,
% 3.36/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.36/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1545,plain,
% 3.36/1.00      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
% 3.36/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1546,plain,
% 3.36/1.00      ( v1_relat_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_1545]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2713,plain,
% 3.36/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_2145,c_25,c_1383,c_1533,c_1546]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_10,plain,
% 3.36/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.36/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1231,plain,
% 3.36/1.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2718,plain,
% 3.36/1.00      ( k2_relat_1(k7_relat_1(sK3,X0)) = k9_relat_1(sK3,X0) ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2713,c_1231]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_12,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,X1)
% 3.36/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.36/1.00      | ~ v1_relat_1(X0)
% 3.36/1.00      | ~ v1_relat_1(X1) ),
% 3.36/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_142,plain,
% 3.36/1.00      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.36/1.00      | ~ r1_tarski(X0,X1)
% 3.36/1.00      | ~ v1_relat_1(X1) ),
% 3.36/1.00      inference(global_propositional_subsumption,[status(thm)],[c_12,c_6,c_4]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_143,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,X1)
% 3.36/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.36/1.00      | ~ v1_relat_1(X1) ),
% 3.36/1.00      inference(renaming,[status(thm)],[c_142]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1223,plain,
% 3.36/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.36/1.00      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 3.36/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_143]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3043,plain,
% 3.36/1.00      ( r1_tarski(k9_relat_1(sK3,X0),k2_relat_1(X1)) = iProver_top
% 3.36/1.00      | r1_tarski(k7_relat_1(sK3,X0),X1) != iProver_top
% 3.36/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2718,c_1223]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_18,plain,
% 3.36/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.36/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_8,plain,
% 3.36/1.00      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_325,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.36/1.00      | ~ v1_relat_1(X0) ),
% 3.36/1.00      inference(resolution,[status(thm)],[c_18,c_8]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1220,plain,
% 3.36/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.36/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_325]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1571,plain,
% 3.36/1.00      ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top
% 3.36/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1225,c_1220]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1867,plain,
% 3.36/1.00      ( r1_tarski(k1_relat_1(sK3),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) = iProver_top ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_1571,c_25,c_1383,c_1533,c_1546]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2,plain,
% 3.36/1.00      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
% 3.36/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
% 3.36/1.00      | k1_xboole_0 = X0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1236,plain,
% 3.36/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = X1
% 3.36/1.00      | k1_xboole_0 = X1
% 3.36/1.00      | r1_tarski(X1,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2436,plain,
% 3.36/1.00      ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k1_relat_1(sK3)
% 3.36/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1867,c_1236]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_17,plain,
% 3.36/1.00      ( ~ v1_funct_1(X0)
% 3.36/1.00      | ~ v1_relat_1(X0)
% 3.36/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 3.36/1.00      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0) ),
% 3.36/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_23,negated_conjecture,
% 3.36/1.00      ( v1_funct_1(sK3) ),
% 3.36/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_306,plain,
% 3.36/1.00      ( ~ v1_relat_1(X0)
% 3.36/1.00      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k1_relat_1(X0)
% 3.36/1.00      | k6_enumset1(k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1),k1_funct_1(X0,X1)) = k2_relat_1(X0)
% 3.36/1.00      | sK3 != X0 ),
% 3.36/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_23]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_307,plain,
% 3.36/1.00      ( ~ v1_relat_1(sK3)
% 3.36/1.00      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.36/1.00      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3) ),
% 3.36/1.00      inference(unflattening,[status(thm)],[c_306]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1221,plain,
% 3.36/1.00      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_relat_1(sK3)
% 3.36/1.00      | k6_enumset1(k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0),k1_funct_1(sK3,X0)) = k2_relat_1(sK3)
% 3.36/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_307]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2778,plain,
% 3.36/1.00      ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.36/1.00      | k1_relat_1(sK3) = k1_xboole_0
% 3.36/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_2436,c_1221]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2820,plain,
% 3.36/1.00      ( ~ v1_relat_1(sK3)
% 3.36/1.00      | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.36/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.36/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2778]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3570,plain,
% 3.36/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.36/1.00      | k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3) ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_2778,c_22,c_1382,c_1532,c_1545,c_2820]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3571,plain,
% 3.36/1.00      ( k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0)) = k2_relat_1(sK3)
% 3.36/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.36/1.00      inference(renaming,[status(thm)],[c_3570]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_19,plain,
% 3.36/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.36/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.36/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1227,plain,
% 3.36/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.36/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2273,plain,
% 3.36/1.00      ( k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,X0) = k9_relat_1(sK3,X0) ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1225,c_1227]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_20,negated_conjecture,
% 3.36/1.00      ( ~ r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) ),
% 3.36/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1226,plain,
% 3.36/1.00      ( r1_tarski(k7_relset_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1,sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_2638,plain,
% 3.36/1.00      ( r1_tarski(k9_relat_1(sK3,sK2),k6_enumset1(k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0),k1_funct_1(sK3,sK0))) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_2273,c_1226]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3581,plain,
% 3.36/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.36/1.00      | r1_tarski(k9_relat_1(sK3,sK2),k2_relat_1(sK3)) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_3571,c_2638]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5173,plain,
% 3.36/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.36/1.00      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 3.36/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_3043,c_3581]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5266,plain,
% 3.36/1.00      ( r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top
% 3.36/1.00      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_5173,c_25,c_1383,c_1533,c_1546]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5267,plain,
% 3.36/1.00      ( k1_relat_1(sK3) = k1_xboole_0
% 3.36/1.00      | r1_tarski(k7_relat_1(sK3,sK2),sK3) != iProver_top ),
% 3.36/1.00      inference(renaming,[status(thm)],[c_5266]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5272,plain,
% 3.36/1.00      ( k1_relat_1(sK3) = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1228,c_5267]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5338,plain,
% 3.36/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_5272,c_25,c_1383,c_1533,c_1546]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_15,plain,
% 3.36/1.00      ( ~ v1_relat_1(X0) | k1_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1229,plain,
% 3.36/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.36/1.00      | k1_xboole_0 = X0
% 3.36/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5380,plain,
% 3.36/1.00      ( sK3 = k1_xboole_0 | v1_relat_1(sK3) != iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_5338,c_1229]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5851,plain,
% 3.36/1.00      ( sK3 = k1_xboole_0 ),
% 3.36/1.00      inference(global_propositional_subsumption,
% 3.36/1.00                [status(thm)],
% 3.36/1.00                [c_5380,c_25,c_1383,c_1533,c_1546]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5869,plain,
% 3.36/1.00      ( r1_tarski(k9_relat_1(k1_xboole_0,sK2),k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_5851,c_2638]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_11,plain,
% 3.36/1.00      ( k9_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.36/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_5878,plain,
% 3.36/1.00      ( r1_tarski(k1_xboole_0,k6_enumset1(k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0),k1_funct_1(k1_xboole_0,sK0))) != iProver_top ),
% 3.36/1.00      inference(demodulation,[status(thm)],[c_5869,c_11]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_3,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.36/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1235,plain,
% 3.36/1.00      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.36/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_1587,plain,
% 3.36/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.36/1.00      inference(superposition,[status(thm)],[c_1235,c_1233]) ).
% 3.36/1.00  
% 3.36/1.00  cnf(c_6053,plain,
% 3.36/1.00      ( $false ),
% 3.36/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_5878,c_1587]) ).
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.36/1.00  
% 3.36/1.00  ------                               Statistics
% 3.36/1.00  
% 3.36/1.00  ------ General
% 3.36/1.00  
% 3.36/1.00  abstr_ref_over_cycles:                  0
% 3.36/1.00  abstr_ref_under_cycles:                 0
% 3.36/1.00  gc_basic_clause_elim:                   0
% 3.36/1.00  forced_gc_time:                         0
% 3.36/1.00  parsing_time:                           0.009
% 3.36/1.00  unif_index_cands_time:                  0.
% 3.36/1.00  unif_index_add_time:                    0.
% 3.36/1.00  orderings_time:                         0.
% 3.36/1.00  out_proof_time:                         0.017
% 3.36/1.00  total_time:                             0.277
% 3.36/1.00  num_of_symbols:                         50
% 3.36/1.00  num_of_terms:                           5486
% 3.36/1.00  
% 3.36/1.00  ------ Preprocessing
% 3.36/1.00  
% 3.36/1.00  num_of_splits:                          0
% 3.36/1.00  num_of_split_atoms:                     0
% 3.36/1.00  num_of_reused_defs:                     0
% 3.36/1.00  num_eq_ax_congr_red:                    12
% 3.36/1.00  num_of_sem_filtered_clauses:            1
% 3.36/1.00  num_of_subtypes:                        0
% 3.36/1.00  monotx_restored_types:                  0
% 3.36/1.00  sat_num_of_epr_types:                   0
% 3.36/1.00  sat_num_of_non_cyclic_types:            0
% 3.36/1.00  sat_guarded_non_collapsed_types:        0
% 3.36/1.00  num_pure_diseq_elim:                    0
% 3.36/1.00  simp_replaced_by:                       0
% 3.36/1.00  res_preprocessed:                       114
% 3.36/1.00  prep_upred:                             0
% 3.36/1.00  prep_unflattend:                        17
% 3.36/1.00  smt_new_axioms:                         0
% 3.36/1.00  pred_elim_cands:                        3
% 3.36/1.00  pred_elim:                              2
% 3.36/1.00  pred_elim_cl:                           3
% 3.36/1.00  pred_elim_cycles:                       4
% 3.36/1.00  merged_defs:                            8
% 3.36/1.00  merged_defs_ncl:                        0
% 3.36/1.00  bin_hyper_res:                          9
% 3.36/1.00  prep_cycles:                            4
% 3.36/1.00  pred_elim_time:                         0.005
% 3.36/1.00  splitting_time:                         0.
% 3.36/1.00  sem_filter_time:                        0.
% 3.36/1.00  monotx_time:                            0.
% 3.36/1.00  subtype_inf_time:                       0.
% 3.36/1.00  
% 3.36/1.00  ------ Problem properties
% 3.36/1.00  
% 3.36/1.00  clauses:                                21
% 3.36/1.00  conjectures:                            3
% 3.36/1.00  epr:                                    2
% 3.36/1.00  horn:                                   20
% 3.36/1.00  ground:                                 3
% 3.36/1.00  unary:                                  8
% 3.36/1.00  binary:                                 5
% 3.36/1.00  lits:                                   42
% 3.36/1.00  lits_eq:                                12
% 3.36/1.00  fd_pure:                                0
% 3.36/1.00  fd_pseudo:                              0
% 3.36/1.00  fd_cond:                                2
% 3.36/1.00  fd_pseudo_cond:                         1
% 3.36/1.00  ac_symbols:                             0
% 3.36/1.00  
% 3.36/1.00  ------ Propositional Solver
% 3.36/1.00  
% 3.36/1.00  prop_solver_calls:                      30
% 3.36/1.00  prop_fast_solver_calls:                 769
% 3.36/1.00  smt_solver_calls:                       0
% 3.36/1.00  smt_fast_solver_calls:                  0
% 3.36/1.00  prop_num_of_clauses:                    2357
% 3.36/1.00  prop_preprocess_simplified:             5589
% 3.36/1.00  prop_fo_subsumed:                       19
% 3.36/1.00  prop_solver_time:                       0.
% 3.36/1.00  smt_solver_time:                        0.
% 3.36/1.00  smt_fast_solver_time:                   0.
% 3.36/1.00  prop_fast_solver_time:                  0.
% 3.36/1.00  prop_unsat_core_time:                   0.
% 3.36/1.00  
% 3.36/1.00  ------ QBF
% 3.36/1.00  
% 3.36/1.00  qbf_q_res:                              0
% 3.36/1.00  qbf_num_tautologies:                    0
% 3.36/1.00  qbf_prep_cycles:                        0
% 3.36/1.00  
% 3.36/1.00  ------ BMC1
% 3.36/1.00  
% 3.36/1.00  bmc1_current_bound:                     -1
% 3.36/1.00  bmc1_last_solved_bound:                 -1
% 3.36/1.00  bmc1_unsat_core_size:                   -1
% 3.36/1.00  bmc1_unsat_core_parents_size:           -1
% 3.36/1.00  bmc1_merge_next_fun:                    0
% 3.36/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.36/1.00  
% 3.36/1.00  ------ Instantiation
% 3.36/1.00  
% 3.36/1.00  inst_num_of_clauses:                    633
% 3.36/1.00  inst_num_in_passive:                    231
% 3.36/1.00  inst_num_in_active:                     354
% 3.36/1.00  inst_num_in_unprocessed:                48
% 3.36/1.00  inst_num_of_loops:                      380
% 3.36/1.00  inst_num_of_learning_restarts:          0
% 3.36/1.00  inst_num_moves_active_passive:          22
% 3.36/1.00  inst_lit_activity:                      0
% 3.36/1.00  inst_lit_activity_moves:                0
% 3.36/1.00  inst_num_tautologies:                   0
% 3.36/1.00  inst_num_prop_implied:                  0
% 3.36/1.00  inst_num_existing_simplified:           0
% 3.36/1.00  inst_num_eq_res_simplified:             0
% 3.36/1.00  inst_num_child_elim:                    0
% 3.36/1.00  inst_num_of_dismatching_blockings:      154
% 3.36/1.00  inst_num_of_non_proper_insts:           604
% 3.36/1.00  inst_num_of_duplicates:                 0
% 3.36/1.00  inst_inst_num_from_inst_to_res:         0
% 3.36/1.00  inst_dismatching_checking_time:         0.
% 3.36/1.00  
% 3.36/1.00  ------ Resolution
% 3.36/1.00  
% 3.36/1.00  res_num_of_clauses:                     0
% 3.36/1.00  res_num_in_passive:                     0
% 3.36/1.00  res_num_in_active:                      0
% 3.36/1.00  res_num_of_loops:                       118
% 3.36/1.00  res_forward_subset_subsumed:            78
% 3.36/1.00  res_backward_subset_subsumed:           2
% 3.36/1.00  res_forward_subsumed:                   0
% 3.36/1.00  res_backward_subsumed:                  0
% 3.36/1.00  res_forward_subsumption_resolution:     0
% 3.36/1.00  res_backward_subsumption_resolution:    0
% 3.36/1.00  res_clause_to_clause_subsumption:       259
% 3.36/1.00  res_orphan_elimination:                 0
% 3.36/1.00  res_tautology_del:                      116
% 3.36/1.00  res_num_eq_res_simplified:              0
% 3.36/1.00  res_num_sel_changes:                    0
% 3.36/1.00  res_moves_from_active_to_pass:          0
% 3.36/1.00  
% 3.36/1.00  ------ Superposition
% 3.36/1.00  
% 3.36/1.00  sup_time_total:                         0.
% 3.36/1.00  sup_time_generating:                    0.
% 3.36/1.00  sup_time_sim_full:                      0.
% 3.36/1.00  sup_time_sim_immed:                     0.
% 3.36/1.00  
% 3.36/1.00  sup_num_of_clauses:                     89
% 3.36/1.00  sup_num_in_active:                      35
% 3.36/1.00  sup_num_in_passive:                     54
% 3.36/1.00  sup_num_of_loops:                       74
% 3.36/1.00  sup_fw_superposition:                   75
% 3.36/1.00  sup_bw_superposition:                   105
% 3.36/1.00  sup_immediate_simplified:               53
% 3.36/1.00  sup_given_eliminated:                   0
% 3.36/1.00  comparisons_done:                       0
% 3.36/1.00  comparisons_avoided:                    27
% 3.36/1.00  
% 3.36/1.00  ------ Simplifications
% 3.36/1.00  
% 3.36/1.00  
% 3.36/1.00  sim_fw_subset_subsumed:                 10
% 3.36/1.00  sim_bw_subset_subsumed:                 20
% 3.36/1.00  sim_fw_subsumed:                        29
% 3.36/1.00  sim_bw_subsumed:                        2
% 3.36/1.00  sim_fw_subsumption_res:                 1
% 3.36/1.00  sim_bw_subsumption_res:                 0
% 3.36/1.00  sim_tautology_del:                      8
% 3.36/1.00  sim_eq_tautology_del:                   12
% 3.36/1.00  sim_eq_res_simp:                        1
% 3.36/1.00  sim_fw_demodulated:                     6
% 3.36/1.00  sim_bw_demodulated:                     33
% 3.36/1.00  sim_light_normalised:                   7
% 3.36/1.00  sim_joinable_taut:                      0
% 3.36/1.00  sim_joinable_simp:                      0
% 3.36/1.00  sim_ac_normalised:                      0
% 3.36/1.00  sim_smt_subsumption:                    0
% 3.36/1.00  
%------------------------------------------------------------------------------
