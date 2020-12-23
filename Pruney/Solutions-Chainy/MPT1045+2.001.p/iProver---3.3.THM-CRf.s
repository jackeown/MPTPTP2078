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
% DateTime   : Thu Dec  3 12:08:49 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  193 (2661 expanded)
%              Number of clauses        :   93 ( 574 expanded)
%              Number of leaves         :   30 ( 632 expanded)
%              Depth                    :   27
%              Number of atoms          :  468 (8786 expanded)
%              Number of equality atoms :  232 (4379 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   12 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f90,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f81,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f17,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k1_xboole_0 = X1
         => k1_xboole_0 = X0 )
       => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1))
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1))
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f53])).

fof(f94,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f54])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v1_partfun1(X2,X0)
      <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_partfun1(X2,X0)
          | k1_tarski(X2) != k5_partfun1(X0,X1,X2) )
        & ( k1_tarski(X2) = k5_partfun1(X0,X1,X2)
          | ~ v1_partfun1(X2,X0) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) = k5_partfun1(X0,X1,X2)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f98,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f98])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f99])).

fof(f101,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f66,f100])).

fof(f102,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f65,f101])).

fof(f105,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f64,f102])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k5_partfun1(X0,X1,X2)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f87,f105])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k3_partfun1(X2,X0,X1) = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k3_partfun1(X2,X0,X1) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f111,plain,(
    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) ),
    inference(definition_unfolding,[],[f97,f105])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f96,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f115,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f59,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0)
        | X0 = X1 )
      & ( X0 != X1
        | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f74,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f19,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f103,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f78,f102])).

fof(f104,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f60,f103])).

fof(f107,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ) ),
    inference(definition_unfolding,[],[f74,f104,f105,f105,f105])).

fof(f116,plain,(
    ! [X1] : k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(equality_resolution,[],[f107])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f18,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f108,plain,(
    ! [X0] : k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f77,f105])).

cnf(c_17,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_26,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_353,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_xboole_0(X2)
    | X3 != X0
    | X4 != X2
    | k1_relat_1(X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_26])).

cnf(c_354,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(unflattening,[status(thm)],[c_353])).

cnf(c_25,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_356,plain,
    ( v1_partfun1(X0,k1_relat_1(X0))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_354,c_25])).

cnf(c_2430,plain,
    ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_356])).

cnf(c_2733,plain,
    ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_2430])).

cnf(c_18,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2734,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2733,c_18])).

cnf(c_19,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_60,plain,
    ( v1_funct_1(X0) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_62,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_5,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_81,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_90,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2628,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_2630,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2628])).

cnf(c_13,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2629,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2632,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2629])).

cnf(c_4454,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2734,c_62,c_81,c_90,c_2630,c_2632])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_376,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK1 != X2
    | sK0 != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_377,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_379,plain,
    ( v1_partfun1(sK2,sK0)
    | v1_xboole_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_377,c_33,c_31])).

cnf(c_2429,plain,
    ( v1_partfun1(sK2,sK0) = iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_2432,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_partfun1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_2435,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_partfun1(X1,X2,X0)
    | v1_partfun1(X0,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4215,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
    | v1_partfun1(sK2,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_2435])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2685,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_funct_1(sK2)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_partfun1(sK0,X0,sK2) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_2812,plain,
    ( ~ v1_partfun1(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) ),
    inference(instantiation,[status(thm)],[c_2685])).

cnf(c_2813,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
    | v1_partfun1(sK2,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2812])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k3_partfun1(X0,X1,X2) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2433,plain,
    ( k3_partfun1(X0,X1,X2) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3144,plain,
    ( k3_partfun1(sK2,sK0,sK1) = sK2
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_2433])).

cnf(c_2659,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | k3_partfun1(sK2,sK0,sK1) = sK2 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_3289,plain,
    ( k3_partfun1(sK2,sK0,sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3144,c_33,c_31,c_2659])).

cnf(c_29,negated_conjecture,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3292,plain,
    ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_partfun1(sK0,sK1,sK2) ),
    inference(demodulation,[status(thm)],[c_3289,c_29])).

cnf(c_4581,plain,
    ( v1_partfun1(sK2,sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4215,c_34,c_36,c_2813,c_3292])).

cnf(c_4586,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2429,c_4581])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2446,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4674,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4586,c_2446])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2439,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3214,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2432,c_2439])).

cnf(c_4684,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4674,c_3214])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_4687,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4674,c_30])).

cnf(c_4688,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_4687])).

cnf(c_4695,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4684,c_4688])).

cnf(c_9,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_4697,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4695,c_9])).

cnf(c_2443,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2445,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3555,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2443,c_2445])).

cnf(c_5075,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4697,c_3555])).

cnf(c_4837,plain,
    ( v1_partfun1(sK2,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4688,c_4581])).

cnf(c_5218,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5075,c_4837])).

cnf(c_5347,plain,
    ( v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4454,c_5218])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2442,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5479,plain,
    ( X0 = X1
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5347,c_2442])).

cnf(c_5485,plain,
    ( X0 = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5479,c_5347])).

cnf(c_12,plain,
    ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_7,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_14,plain,
    ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2560,plain,
    ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12,c_7,c_14])).

cnf(c_5653,plain,
    ( k1_xboole_0 != X0 ),
    inference(demodulation,[status(thm)],[c_5485,c_2560])).

cnf(c_4456,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4454])).

cnf(c_3722,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_3725,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3722])).

cnf(c_1908,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_3494,plain,
    ( ~ v1_partfun1(X0,X1)
    | v1_partfun1(sK2,sK0)
    | sK0 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_3496,plain,
    ( v1_partfun1(sK2,sK0)
    | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
    | sK0 != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3494])).

cnf(c_3248,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_3249,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3248])).

cnf(c_3251,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3249])).

cnf(c_5740,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(grounding,[status(thm)],[c_5653:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_5741,plain,
    ( v1_partfun1(k1_xboole_0,k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(grounding,[status(thm)],[c_4456:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_5742,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(grounding,[status(thm)],[c_1:[bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5740,c_4697,c_4688,c_5741,c_3725,c_3496,c_3292,c_3251,c_2812,c_5742,c_31,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:41:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.65/0.98  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.65/0.98  
% 2.65/0.98  ------  iProver source info
% 2.65/0.98  
% 2.65/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.65/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.65/0.98  git: non_committed_changes: false
% 2.65/0.98  git: last_make_outside_of_git: false
% 2.65/0.98  
% 2.65/0.98  ------ 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options
% 2.65/0.98  
% 2.65/0.98  --out_options                           all
% 2.65/0.98  --tptp_safe_out                         true
% 2.65/0.98  --problem_path                          ""
% 2.65/0.98  --include_path                          ""
% 2.65/0.98  --clausifier                            res/vclausify_rel
% 2.65/0.98  --clausifier_options                    --mode clausify
% 2.65/0.98  --stdin                                 false
% 2.65/0.98  --stats_out                             all
% 2.65/0.98  
% 2.65/0.98  ------ General Options
% 2.65/0.98  
% 2.65/0.98  --fof                                   false
% 2.65/0.98  --time_out_real                         305.
% 2.65/0.98  --time_out_virtual                      -1.
% 2.65/0.98  --symbol_type_check                     false
% 2.65/0.98  --clausify_out                          false
% 2.65/0.98  --sig_cnt_out                           false
% 2.65/0.98  --trig_cnt_out                          false
% 2.65/0.98  --trig_cnt_out_tolerance                1.
% 2.65/0.98  --trig_cnt_out_sk_spl                   false
% 2.65/0.98  --abstr_cl_out                          false
% 2.65/0.98  
% 2.65/0.98  ------ Global Options
% 2.65/0.98  
% 2.65/0.98  --schedule                              default
% 2.65/0.98  --add_important_lit                     false
% 2.65/0.98  --prop_solver_per_cl                    1000
% 2.65/0.98  --min_unsat_core                        false
% 2.65/0.98  --soft_assumptions                      false
% 2.65/0.98  --soft_lemma_size                       3
% 2.65/0.98  --prop_impl_unit_size                   0
% 2.65/0.98  --prop_impl_unit                        []
% 2.65/0.98  --share_sel_clauses                     true
% 2.65/0.98  --reset_solvers                         false
% 2.65/0.98  --bc_imp_inh                            [conj_cone]
% 2.65/0.98  --conj_cone_tolerance                   3.
% 2.65/0.98  --extra_neg_conj                        none
% 2.65/0.98  --large_theory_mode                     true
% 2.65/0.98  --prolific_symb_bound                   200
% 2.65/0.98  --lt_threshold                          2000
% 2.65/0.98  --clause_weak_htbl                      true
% 2.65/0.98  --gc_record_bc_elim                     false
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing Options
% 2.65/0.98  
% 2.65/0.98  --preprocessing_flag                    true
% 2.65/0.98  --time_out_prep_mult                    0.1
% 2.65/0.98  --splitting_mode                        input
% 2.65/0.98  --splitting_grd                         true
% 2.65/0.98  --splitting_cvd                         false
% 2.65/0.98  --splitting_cvd_svl                     false
% 2.65/0.98  --splitting_nvd                         32
% 2.65/0.98  --sub_typing                            true
% 2.65/0.98  --prep_gs_sim                           true
% 2.65/0.98  --prep_unflatten                        true
% 2.65/0.98  --prep_res_sim                          true
% 2.65/0.98  --prep_upred                            true
% 2.65/0.98  --prep_sem_filter                       exhaustive
% 2.65/0.98  --prep_sem_filter_out                   false
% 2.65/0.98  --pred_elim                             true
% 2.65/0.98  --res_sim_input                         true
% 2.65/0.98  --eq_ax_congr_red                       true
% 2.65/0.98  --pure_diseq_elim                       true
% 2.65/0.98  --brand_transform                       false
% 2.65/0.98  --non_eq_to_eq                          false
% 2.65/0.98  --prep_def_merge                        true
% 2.65/0.98  --prep_def_merge_prop_impl              false
% 2.65/0.98  --prep_def_merge_mbd                    true
% 2.65/0.98  --prep_def_merge_tr_red                 false
% 2.65/0.98  --prep_def_merge_tr_cl                  false
% 2.65/0.98  --smt_preprocessing                     true
% 2.65/0.98  --smt_ac_axioms                         fast
% 2.65/0.98  --preprocessed_out                      false
% 2.65/0.98  --preprocessed_stats                    false
% 2.65/0.98  
% 2.65/0.98  ------ Abstraction refinement Options
% 2.65/0.98  
% 2.65/0.98  --abstr_ref                             []
% 2.65/0.98  --abstr_ref_prep                        false
% 2.65/0.98  --abstr_ref_until_sat                   false
% 2.65/0.98  --abstr_ref_sig_restrict                funpre
% 2.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.98  --abstr_ref_under                       []
% 2.65/0.98  
% 2.65/0.98  ------ SAT Options
% 2.65/0.98  
% 2.65/0.98  --sat_mode                              false
% 2.65/0.98  --sat_fm_restart_options                ""
% 2.65/0.98  --sat_gr_def                            false
% 2.65/0.98  --sat_epr_types                         true
% 2.65/0.98  --sat_non_cyclic_types                  false
% 2.65/0.98  --sat_finite_models                     false
% 2.65/0.98  --sat_fm_lemmas                         false
% 2.65/0.98  --sat_fm_prep                           false
% 2.65/0.98  --sat_fm_uc_incr                        true
% 2.65/0.98  --sat_out_model                         small
% 2.65/0.98  --sat_out_clauses                       false
% 2.65/0.98  
% 2.65/0.98  ------ QBF Options
% 2.65/0.98  
% 2.65/0.98  --qbf_mode                              false
% 2.65/0.98  --qbf_elim_univ                         false
% 2.65/0.98  --qbf_dom_inst                          none
% 2.65/0.98  --qbf_dom_pre_inst                      false
% 2.65/0.98  --qbf_sk_in                             false
% 2.65/0.98  --qbf_pred_elim                         true
% 2.65/0.98  --qbf_split                             512
% 2.65/0.98  
% 2.65/0.98  ------ BMC1 Options
% 2.65/0.98  
% 2.65/0.98  --bmc1_incremental                      false
% 2.65/0.98  --bmc1_axioms                           reachable_all
% 2.65/0.98  --bmc1_min_bound                        0
% 2.65/0.98  --bmc1_max_bound                        -1
% 2.65/0.98  --bmc1_max_bound_default                -1
% 2.65/0.98  --bmc1_symbol_reachability              true
% 2.65/0.98  --bmc1_property_lemmas                  false
% 2.65/0.98  --bmc1_k_induction                      false
% 2.65/0.98  --bmc1_non_equiv_states                 false
% 2.65/0.98  --bmc1_deadlock                         false
% 2.65/0.98  --bmc1_ucm                              false
% 2.65/0.98  --bmc1_add_unsat_core                   none
% 2.65/0.98  --bmc1_unsat_core_children              false
% 2.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.98  --bmc1_out_stat                         full
% 2.65/0.98  --bmc1_ground_init                      false
% 2.65/0.98  --bmc1_pre_inst_next_state              false
% 2.65/0.98  --bmc1_pre_inst_state                   false
% 2.65/0.98  --bmc1_pre_inst_reach_state             false
% 2.65/0.98  --bmc1_out_unsat_core                   false
% 2.65/0.98  --bmc1_aig_witness_out                  false
% 2.65/0.98  --bmc1_verbose                          false
% 2.65/0.98  --bmc1_dump_clauses_tptp                false
% 2.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.98  --bmc1_dump_file                        -
% 2.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.98  --bmc1_ucm_extend_mode                  1
% 2.65/0.98  --bmc1_ucm_init_mode                    2
% 2.65/0.98  --bmc1_ucm_cone_mode                    none
% 2.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.98  --bmc1_ucm_relax_model                  4
% 2.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.98  --bmc1_ucm_layered_model                none
% 2.65/0.98  --bmc1_ucm_max_lemma_size               10
% 2.65/0.98  
% 2.65/0.98  ------ AIG Options
% 2.65/0.98  
% 2.65/0.98  --aig_mode                              false
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation Options
% 2.65/0.98  
% 2.65/0.98  --instantiation_flag                    true
% 2.65/0.98  --inst_sos_flag                         false
% 2.65/0.98  --inst_sos_phase                        true
% 2.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel_side                     num_symb
% 2.65/0.98  --inst_solver_per_active                1400
% 2.65/0.98  --inst_solver_calls_frac                1.
% 2.65/0.98  --inst_passive_queue_type               priority_queues
% 2.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.98  --inst_passive_queues_freq              [25;2]
% 2.65/0.98  --inst_dismatching                      true
% 2.65/0.98  --inst_eager_unprocessed_to_passive     true
% 2.65/0.98  --inst_prop_sim_given                   true
% 2.65/0.98  --inst_prop_sim_new                     false
% 2.65/0.98  --inst_subs_new                         false
% 2.65/0.98  --inst_eq_res_simp                      false
% 2.65/0.98  --inst_subs_given                       false
% 2.65/0.98  --inst_orphan_elimination               true
% 2.65/0.98  --inst_learning_loop_flag               true
% 2.65/0.98  --inst_learning_start                   3000
% 2.65/0.98  --inst_learning_factor                  2
% 2.65/0.98  --inst_start_prop_sim_after_learn       3
% 2.65/0.98  --inst_sel_renew                        solver
% 2.65/0.98  --inst_lit_activity_flag                true
% 2.65/0.98  --inst_restr_to_given                   false
% 2.65/0.98  --inst_activity_threshold               500
% 2.65/0.98  --inst_out_proof                        true
% 2.65/0.98  
% 2.65/0.98  ------ Resolution Options
% 2.65/0.98  
% 2.65/0.98  --resolution_flag                       true
% 2.65/0.98  --res_lit_sel                           adaptive
% 2.65/0.98  --res_lit_sel_side                      none
% 2.65/0.98  --res_ordering                          kbo
% 2.65/0.98  --res_to_prop_solver                    active
% 2.65/0.98  --res_prop_simpl_new                    false
% 2.65/0.98  --res_prop_simpl_given                  true
% 2.65/0.98  --res_passive_queue_type                priority_queues
% 2.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.98  --res_passive_queues_freq               [15;5]
% 2.65/0.98  --res_forward_subs                      full
% 2.65/0.98  --res_backward_subs                     full
% 2.65/0.98  --res_forward_subs_resolution           true
% 2.65/0.98  --res_backward_subs_resolution          true
% 2.65/0.98  --res_orphan_elimination                true
% 2.65/0.98  --res_time_limit                        2.
% 2.65/0.98  --res_out_proof                         true
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Options
% 2.65/0.98  
% 2.65/0.98  --superposition_flag                    true
% 2.65/0.98  --sup_passive_queue_type                priority_queues
% 2.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.98  --demod_completeness_check              fast
% 2.65/0.98  --demod_use_ground                      true
% 2.65/0.98  --sup_to_prop_solver                    passive
% 2.65/0.98  --sup_prop_simpl_new                    true
% 2.65/0.98  --sup_prop_simpl_given                  true
% 2.65/0.98  --sup_fun_splitting                     false
% 2.65/0.98  --sup_smt_interval                      50000
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Simplification Setup
% 2.65/0.98  
% 2.65/0.98  --sup_indices_passive                   []
% 2.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_full_bw                           [BwDemod]
% 2.65/0.98  --sup_immed_triv                        [TrivRules]
% 2.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_immed_bw_main                     []
% 2.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  
% 2.65/0.98  ------ Combination Options
% 2.65/0.98  
% 2.65/0.98  --comb_res_mult                         3
% 2.65/0.98  --comb_sup_mult                         2
% 2.65/0.98  --comb_inst_mult                        10
% 2.65/0.98  
% 2.65/0.98  ------ Debug Options
% 2.65/0.98  
% 2.65/0.98  --dbg_backtrace                         false
% 2.65/0.98  --dbg_dump_prop_clauses                 false
% 2.65/0.98  --dbg_dump_prop_clauses_file            -
% 2.65/0.98  --dbg_out_stat                          false
% 2.65/0.98  ------ Parsing...
% 2.65/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.65/0.98  ------ Proving...
% 2.65/0.98  ------ Problem Properties 
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  clauses                                 30
% 2.65/0.98  conjectures                             4
% 2.65/0.98  EPR                                     10
% 2.65/0.98  Horn                                    26
% 2.65/0.98  unary                                   14
% 2.65/0.98  binary                                  8
% 2.65/0.98  lits                                    59
% 2.65/0.98  lits eq                                 21
% 2.65/0.98  fd_pure                                 0
% 2.65/0.98  fd_pseudo                               0
% 2.65/0.98  fd_cond                                 2
% 2.65/0.98  fd_pseudo_cond                          3
% 2.65/0.98  AC symbols                              0
% 2.65/0.98  
% 2.65/0.98  ------ Schedule dynamic 5 is on 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  ------ 
% 2.65/0.98  Current options:
% 2.65/0.98  ------ 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options
% 2.65/0.98  
% 2.65/0.98  --out_options                           all
% 2.65/0.98  --tptp_safe_out                         true
% 2.65/0.98  --problem_path                          ""
% 2.65/0.98  --include_path                          ""
% 2.65/0.98  --clausifier                            res/vclausify_rel
% 2.65/0.98  --clausifier_options                    --mode clausify
% 2.65/0.98  --stdin                                 false
% 2.65/0.98  --stats_out                             all
% 2.65/0.98  
% 2.65/0.98  ------ General Options
% 2.65/0.98  
% 2.65/0.98  --fof                                   false
% 2.65/0.98  --time_out_real                         305.
% 2.65/0.98  --time_out_virtual                      -1.
% 2.65/0.98  --symbol_type_check                     false
% 2.65/0.98  --clausify_out                          false
% 2.65/0.98  --sig_cnt_out                           false
% 2.65/0.98  --trig_cnt_out                          false
% 2.65/0.98  --trig_cnt_out_tolerance                1.
% 2.65/0.98  --trig_cnt_out_sk_spl                   false
% 2.65/0.98  --abstr_cl_out                          false
% 2.65/0.98  
% 2.65/0.98  ------ Global Options
% 2.65/0.98  
% 2.65/0.98  --schedule                              default
% 2.65/0.98  --add_important_lit                     false
% 2.65/0.98  --prop_solver_per_cl                    1000
% 2.65/0.98  --min_unsat_core                        false
% 2.65/0.98  --soft_assumptions                      false
% 2.65/0.98  --soft_lemma_size                       3
% 2.65/0.98  --prop_impl_unit_size                   0
% 2.65/0.98  --prop_impl_unit                        []
% 2.65/0.98  --share_sel_clauses                     true
% 2.65/0.98  --reset_solvers                         false
% 2.65/0.98  --bc_imp_inh                            [conj_cone]
% 2.65/0.98  --conj_cone_tolerance                   3.
% 2.65/0.98  --extra_neg_conj                        none
% 2.65/0.98  --large_theory_mode                     true
% 2.65/0.98  --prolific_symb_bound                   200
% 2.65/0.98  --lt_threshold                          2000
% 2.65/0.98  --clause_weak_htbl                      true
% 2.65/0.98  --gc_record_bc_elim                     false
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing Options
% 2.65/0.98  
% 2.65/0.98  --preprocessing_flag                    true
% 2.65/0.98  --time_out_prep_mult                    0.1
% 2.65/0.98  --splitting_mode                        input
% 2.65/0.98  --splitting_grd                         true
% 2.65/0.98  --splitting_cvd                         false
% 2.65/0.98  --splitting_cvd_svl                     false
% 2.65/0.98  --splitting_nvd                         32
% 2.65/0.98  --sub_typing                            true
% 2.65/0.98  --prep_gs_sim                           true
% 2.65/0.98  --prep_unflatten                        true
% 2.65/0.98  --prep_res_sim                          true
% 2.65/0.98  --prep_upred                            true
% 2.65/0.98  --prep_sem_filter                       exhaustive
% 2.65/0.98  --prep_sem_filter_out                   false
% 2.65/0.98  --pred_elim                             true
% 2.65/0.98  --res_sim_input                         true
% 2.65/0.98  --eq_ax_congr_red                       true
% 2.65/0.98  --pure_diseq_elim                       true
% 2.65/0.98  --brand_transform                       false
% 2.65/0.98  --non_eq_to_eq                          false
% 2.65/0.98  --prep_def_merge                        true
% 2.65/0.98  --prep_def_merge_prop_impl              false
% 2.65/0.98  --prep_def_merge_mbd                    true
% 2.65/0.98  --prep_def_merge_tr_red                 false
% 2.65/0.98  --prep_def_merge_tr_cl                  false
% 2.65/0.98  --smt_preprocessing                     true
% 2.65/0.98  --smt_ac_axioms                         fast
% 2.65/0.98  --preprocessed_out                      false
% 2.65/0.98  --preprocessed_stats                    false
% 2.65/0.98  
% 2.65/0.98  ------ Abstraction refinement Options
% 2.65/0.98  
% 2.65/0.98  --abstr_ref                             []
% 2.65/0.98  --abstr_ref_prep                        false
% 2.65/0.98  --abstr_ref_until_sat                   false
% 2.65/0.98  --abstr_ref_sig_restrict                funpre
% 2.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.98  --abstr_ref_under                       []
% 2.65/0.98  
% 2.65/0.98  ------ SAT Options
% 2.65/0.98  
% 2.65/0.98  --sat_mode                              false
% 2.65/0.98  --sat_fm_restart_options                ""
% 2.65/0.98  --sat_gr_def                            false
% 2.65/0.98  --sat_epr_types                         true
% 2.65/0.98  --sat_non_cyclic_types                  false
% 2.65/0.98  --sat_finite_models                     false
% 2.65/0.98  --sat_fm_lemmas                         false
% 2.65/0.98  --sat_fm_prep                           false
% 2.65/0.98  --sat_fm_uc_incr                        true
% 2.65/0.98  --sat_out_model                         small
% 2.65/0.98  --sat_out_clauses                       false
% 2.65/0.98  
% 2.65/0.98  ------ QBF Options
% 2.65/0.98  
% 2.65/0.98  --qbf_mode                              false
% 2.65/0.98  --qbf_elim_univ                         false
% 2.65/0.98  --qbf_dom_inst                          none
% 2.65/0.98  --qbf_dom_pre_inst                      false
% 2.65/0.98  --qbf_sk_in                             false
% 2.65/0.98  --qbf_pred_elim                         true
% 2.65/0.98  --qbf_split                             512
% 2.65/0.98  
% 2.65/0.98  ------ BMC1 Options
% 2.65/0.98  
% 2.65/0.98  --bmc1_incremental                      false
% 2.65/0.98  --bmc1_axioms                           reachable_all
% 2.65/0.98  --bmc1_min_bound                        0
% 2.65/0.98  --bmc1_max_bound                        -1
% 2.65/0.98  --bmc1_max_bound_default                -1
% 2.65/0.98  --bmc1_symbol_reachability              true
% 2.65/0.98  --bmc1_property_lemmas                  false
% 2.65/0.98  --bmc1_k_induction                      false
% 2.65/0.98  --bmc1_non_equiv_states                 false
% 2.65/0.98  --bmc1_deadlock                         false
% 2.65/0.98  --bmc1_ucm                              false
% 2.65/0.98  --bmc1_add_unsat_core                   none
% 2.65/0.98  --bmc1_unsat_core_children              false
% 2.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.98  --bmc1_out_stat                         full
% 2.65/0.98  --bmc1_ground_init                      false
% 2.65/0.98  --bmc1_pre_inst_next_state              false
% 2.65/0.98  --bmc1_pre_inst_state                   false
% 2.65/0.98  --bmc1_pre_inst_reach_state             false
% 2.65/0.98  --bmc1_out_unsat_core                   false
% 2.65/0.98  --bmc1_aig_witness_out                  false
% 2.65/0.98  --bmc1_verbose                          false
% 2.65/0.98  --bmc1_dump_clauses_tptp                false
% 2.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.98  --bmc1_dump_file                        -
% 2.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.98  --bmc1_ucm_extend_mode                  1
% 2.65/0.98  --bmc1_ucm_init_mode                    2
% 2.65/0.98  --bmc1_ucm_cone_mode                    none
% 2.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.98  --bmc1_ucm_relax_model                  4
% 2.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.98  --bmc1_ucm_layered_model                none
% 2.65/0.98  --bmc1_ucm_max_lemma_size               10
% 2.65/0.98  
% 2.65/0.98  ------ AIG Options
% 2.65/0.98  
% 2.65/0.98  --aig_mode                              false
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation Options
% 2.65/0.98  
% 2.65/0.98  --instantiation_flag                    true
% 2.65/0.98  --inst_sos_flag                         false
% 2.65/0.98  --inst_sos_phase                        true
% 2.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel_side                     none
% 2.65/0.98  --inst_solver_per_active                1400
% 2.65/0.98  --inst_solver_calls_frac                1.
% 2.65/0.98  --inst_passive_queue_type               priority_queues
% 2.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.98  --inst_passive_queues_freq              [25;2]
% 2.65/0.98  --inst_dismatching                      true
% 2.65/0.98  --inst_eager_unprocessed_to_passive     true
% 2.65/0.98  --inst_prop_sim_given                   true
% 2.65/0.98  --inst_prop_sim_new                     false
% 2.65/0.98  --inst_subs_new                         false
% 2.65/0.98  --inst_eq_res_simp                      false
% 2.65/0.98  --inst_subs_given                       false
% 2.65/0.98  --inst_orphan_elimination               true
% 2.65/0.98  --inst_learning_loop_flag               true
% 2.65/0.98  --inst_learning_start                   3000
% 2.65/0.98  --inst_learning_factor                  2
% 2.65/0.98  --inst_start_prop_sim_after_learn       3
% 2.65/0.98  --inst_sel_renew                        solver
% 2.65/0.98  --inst_lit_activity_flag                true
% 2.65/0.98  --inst_restr_to_given                   false
% 2.65/0.98  --inst_activity_threshold               500
% 2.65/0.98  --inst_out_proof                        true
% 2.65/0.98  
% 2.65/0.98  ------ Resolution Options
% 2.65/0.98  
% 2.65/0.98  --resolution_flag                       false
% 2.65/0.98  --res_lit_sel                           adaptive
% 2.65/0.98  --res_lit_sel_side                      none
% 2.65/0.98  --res_ordering                          kbo
% 2.65/0.98  --res_to_prop_solver                    active
% 2.65/0.98  --res_prop_simpl_new                    false
% 2.65/0.98  --res_prop_simpl_given                  true
% 2.65/0.98  --res_passive_queue_type                priority_queues
% 2.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.98  --res_passive_queues_freq               [15;5]
% 2.65/0.98  --res_forward_subs                      full
% 2.65/0.98  --res_backward_subs                     full
% 2.65/0.98  --res_forward_subs_resolution           true
% 2.65/0.98  --res_backward_subs_resolution          true
% 2.65/0.98  --res_orphan_elimination                true
% 2.65/0.98  --res_time_limit                        2.
% 2.65/0.98  --res_out_proof                         true
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Options
% 2.65/0.98  
% 2.65/0.98  --superposition_flag                    true
% 2.65/0.98  --sup_passive_queue_type                priority_queues
% 2.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.98  --demod_completeness_check              fast
% 2.65/0.98  --demod_use_ground                      true
% 2.65/0.98  --sup_to_prop_solver                    passive
% 2.65/0.98  --sup_prop_simpl_new                    true
% 2.65/0.98  --sup_prop_simpl_given                  true
% 2.65/0.98  --sup_fun_splitting                     false
% 2.65/0.98  --sup_smt_interval                      50000
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Simplification Setup
% 2.65/0.98  
% 2.65/0.98  --sup_indices_passive                   []
% 2.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_full_bw                           [BwDemod]
% 2.65/0.98  --sup_immed_triv                        [TrivRules]
% 2.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_immed_bw_main                     []
% 2.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  
% 2.65/0.98  ------ Combination Options
% 2.65/0.98  
% 2.65/0.98  --comb_res_mult                         3
% 2.65/0.98  --comb_sup_mult                         2
% 2.65/0.98  --comb_inst_mult                        10
% 2.65/0.98  
% 2.65/0.98  ------ Debug Options
% 2.65/0.98  
% 2.65/0.98  --dbg_backtrace                         false
% 2.65/0.98  --dbg_dump_prop_clauses                 false
% 2.65/0.98  --dbg_dump_prop_clauses_file            -
% 2.65/0.98  --dbg_out_stat                          false
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  ------ Proving...
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  % SZS status Theorem for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  fof(f22,axiom,(
% 2.65/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f82,plain,(
% 2.65/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 2.65/0.98    inference(cnf_transformation,[],[f22])).
% 2.65/0.98  
% 2.65/0.98  fof(f25,axiom,(
% 2.65/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f36,plain,(
% 2.65/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.65/0.98    inference(ennf_transformation,[],[f25])).
% 2.65/0.98  
% 2.65/0.98  fof(f37,plain,(
% 2.65/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.65/0.98    inference(flattening,[],[f36])).
% 2.65/0.98  
% 2.65/0.98  fof(f86,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f37])).
% 2.65/0.98  
% 2.65/0.98  fof(f27,axiom,(
% 2.65/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f40,plain,(
% 2.65/0.98    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.65/0.98    inference(ennf_transformation,[],[f27])).
% 2.65/0.98  
% 2.65/0.98  fof(f41,plain,(
% 2.65/0.98    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.65/0.98    inference(flattening,[],[f40])).
% 2.65/0.98  
% 2.65/0.98  fof(f90,plain,(
% 2.65/0.98    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f41])).
% 2.65/0.98  
% 2.65/0.98  fof(f91,plain,(
% 2.65/0.98    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f41])).
% 2.65/0.98  
% 2.65/0.98  fof(f81,plain,(
% 2.65/0.98    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.65/0.98    inference(cnf_transformation,[],[f22])).
% 2.65/0.98  
% 2.65/0.98  fof(f23,axiom,(
% 2.65/0.98    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f34,plain,(
% 2.65/0.98    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.65/0.98    inference(ennf_transformation,[],[f23])).
% 2.65/0.98  
% 2.65/0.98  fof(f83,plain,(
% 2.65/0.98    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f34])).
% 2.65/0.98  
% 2.65/0.98  fof(f5,axiom,(
% 2.65/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f61,plain,(
% 2.65/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f5])).
% 2.65/0.98  
% 2.65/0.98  fof(f1,axiom,(
% 2.65/0.98    v1_xboole_0(k1_xboole_0)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f55,plain,(
% 2.65/0.98    v1_xboole_0(k1_xboole_0)),
% 2.65/0.98    inference(cnf_transformation,[],[f1])).
% 2.65/0.98  
% 2.65/0.98  fof(f24,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f35,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(ennf_transformation,[],[f24])).
% 2.65/0.98  
% 2.65/0.98  fof(f84,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f35])).
% 2.65/0.98  
% 2.65/0.98  fof(f17,axiom,(
% 2.65/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f76,plain,(
% 2.65/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f17])).
% 2.65/0.98  
% 2.65/0.98  fof(f29,conjecture,(
% 2.65/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f30,negated_conjecture,(
% 2.65/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => k1_tarski(X2) = k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1))))),
% 2.65/0.98    inference(negated_conjecture,[],[f29])).
% 2.65/0.98  
% 2.65/0.98  fof(f44,plain,(
% 2.65/0.98    ? [X0,X1,X2] : ((k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.65/0.98    inference(ennf_transformation,[],[f30])).
% 2.65/0.98  
% 2.65/0.98  fof(f45,plain,(
% 2.65/0.98    ? [X0,X1,X2] : (k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.65/0.98    inference(flattening,[],[f44])).
% 2.65/0.98  
% 2.65/0.98  fof(f53,plain,(
% 2.65/0.98    ? [X0,X1,X2] : (k1_tarski(X2) != k5_partfun1(X0,X1,k3_partfun1(X2,X0,X1)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.65/0.98    introduced(choice_axiom,[])).
% 2.65/0.98  
% 2.65/0.98  fof(f54,plain,(
% 2.65/0.98    k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f45,f53])).
% 2.65/0.98  
% 2.65/0.98  fof(f94,plain,(
% 2.65/0.98    v1_funct_2(sK2,sK0,sK1)),
% 2.65/0.98    inference(cnf_transformation,[],[f54])).
% 2.65/0.98  
% 2.65/0.98  fof(f93,plain,(
% 2.65/0.98    v1_funct_1(sK2)),
% 2.65/0.98    inference(cnf_transformation,[],[f54])).
% 2.65/0.98  
% 2.65/0.98  fof(f95,plain,(
% 2.65/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.65/0.98    inference(cnf_transformation,[],[f54])).
% 2.65/0.98  
% 2.65/0.98  fof(f26,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2)))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f38,plain,(
% 2.65/0.98    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.65/0.98    inference(ennf_transformation,[],[f26])).
% 2.65/0.98  
% 2.65/0.98  fof(f39,plain,(
% 2.65/0.98    ! [X0,X1,X2] : ((v1_partfun1(X2,X0) <=> k1_tarski(X2) = k5_partfun1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.65/0.98    inference(flattening,[],[f38])).
% 2.65/0.98  
% 2.65/0.98  fof(f52,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | k1_tarski(X2) != k5_partfun1(X0,X1,X2)) & (k1_tarski(X2) = k5_partfun1(X0,X1,X2) | ~v1_partfun1(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.65/0.98    inference(nnf_transformation,[],[f39])).
% 2.65/0.98  
% 2.65/0.98  fof(f87,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k1_tarski(X2) = k5_partfun1(X0,X1,X2) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f52])).
% 2.65/0.98  
% 2.65/0.98  fof(f8,axiom,(
% 2.65/0.98    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f64,plain,(
% 2.65/0.98    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f8])).
% 2.65/0.98  
% 2.65/0.98  fof(f9,axiom,(
% 2.65/0.98    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f65,plain,(
% 2.65/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f9])).
% 2.65/0.98  
% 2.65/0.98  fof(f10,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f66,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f10])).
% 2.65/0.98  
% 2.65/0.98  fof(f11,axiom,(
% 2.65/0.98    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f67,plain,(
% 2.65/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f11])).
% 2.65/0.98  
% 2.65/0.98  fof(f12,axiom,(
% 2.65/0.98    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f68,plain,(
% 2.65/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f12])).
% 2.65/0.98  
% 2.65/0.98  fof(f13,axiom,(
% 2.65/0.98    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f69,plain,(
% 2.65/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f13])).
% 2.65/0.98  
% 2.65/0.98  fof(f14,axiom,(
% 2.65/0.98    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f70,plain,(
% 2.65/0.98    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f14])).
% 2.65/0.98  
% 2.65/0.98  fof(f98,plain,(
% 2.65/0.98    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.65/0.98    inference(definition_unfolding,[],[f69,f70])).
% 2.65/0.98  
% 2.65/0.98  fof(f99,plain,(
% 2.65/0.98    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.65/0.98    inference(definition_unfolding,[],[f68,f98])).
% 2.65/0.98  
% 2.65/0.98  fof(f100,plain,(
% 2.65/0.98    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.65/0.98    inference(definition_unfolding,[],[f67,f99])).
% 2.65/0.98  
% 2.65/0.98  fof(f101,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.65/0.98    inference(definition_unfolding,[],[f66,f100])).
% 2.65/0.98  
% 2.65/0.98  fof(f102,plain,(
% 2.65/0.98    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.65/0.98    inference(definition_unfolding,[],[f65,f101])).
% 2.65/0.98  
% 2.65/0.98  fof(f105,plain,(
% 2.65/0.98    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.65/0.98    inference(definition_unfolding,[],[f64,f102])).
% 2.65/0.98  
% 2.65/0.98  fof(f110,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k5_partfun1(X0,X1,X2) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.65/0.98    inference(definition_unfolding,[],[f87,f105])).
% 2.65/0.98  
% 2.65/0.98  fof(f28,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k3_partfun1(X2,X0,X1) = X2)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f42,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.65/0.98    inference(ennf_transformation,[],[f28])).
% 2.65/0.98  
% 2.65/0.98  fof(f43,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.65/0.98    inference(flattening,[],[f42])).
% 2.65/0.98  
% 2.65/0.98  fof(f92,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k3_partfun1(X2,X0,X1) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f43])).
% 2.65/0.98  
% 2.65/0.98  fof(f97,plain,(
% 2.65/0.98    k1_tarski(sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1))),
% 2.65/0.98    inference(cnf_transformation,[],[f54])).
% 2.65/0.98  
% 2.65/0.98  fof(f111,plain,(
% 2.65/0.98    k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1))),
% 2.65/0.98    inference(definition_unfolding,[],[f97,f105])).
% 2.65/0.98  
% 2.65/0.98  fof(f2,axiom,(
% 2.65/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f32,plain,(
% 2.65/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.65/0.98    inference(ennf_transformation,[],[f2])).
% 2.65/0.98  
% 2.65/0.98  fof(f56,plain,(
% 2.65/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f32])).
% 2.65/0.98  
% 2.65/0.98  fof(f20,axiom,(
% 2.65/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f51,plain,(
% 2.65/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.65/0.98    inference(nnf_transformation,[],[f20])).
% 2.65/0.98  
% 2.65/0.98  fof(f79,plain,(
% 2.65/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f51])).
% 2.65/0.98  
% 2.65/0.98  fof(f96,plain,(
% 2.65/0.98    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.65/0.98    inference(cnf_transformation,[],[f54])).
% 2.65/0.98  
% 2.65/0.98  fof(f15,axiom,(
% 2.65/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f48,plain,(
% 2.65/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.65/0.98    inference(nnf_transformation,[],[f15])).
% 2.65/0.98  
% 2.65/0.98  fof(f49,plain,(
% 2.65/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.65/0.98    inference(flattening,[],[f48])).
% 2.65/0.98  
% 2.65/0.98  fof(f72,plain,(
% 2.65/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.65/0.98    inference(cnf_transformation,[],[f49])).
% 2.65/0.98  
% 2.65/0.98  fof(f115,plain,(
% 2.65/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.65/0.98    inference(equality_resolution,[],[f72])).
% 2.65/0.98  
% 2.65/0.98  fof(f3,axiom,(
% 2.65/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f46,plain,(
% 2.65/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.65/0.98    inference(nnf_transformation,[],[f3])).
% 2.65/0.98  
% 2.65/0.98  fof(f47,plain,(
% 2.65/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.65/0.98    inference(flattening,[],[f46])).
% 2.65/0.98  
% 2.65/0.98  fof(f59,plain,(
% 2.65/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f47])).
% 2.65/0.98  
% 2.65/0.98  fof(f6,axiom,(
% 2.65/0.98    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f33,plain,(
% 2.65/0.98    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 2.65/0.98    inference(ennf_transformation,[],[f6])).
% 2.65/0.98  
% 2.65/0.98  fof(f62,plain,(
% 2.65/0.98    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f33])).
% 2.65/0.98  
% 2.65/0.98  fof(f16,axiom,(
% 2.65/0.98    ! [X0,X1] : (k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) <=> X0 != X1)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f50,plain,(
% 2.65/0.98    ! [X0,X1] : ((k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k1_tarski(X0) | X0 = X1) & (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)))),
% 2.65/0.98    inference(nnf_transformation,[],[f16])).
% 2.65/0.98  
% 2.65/0.98  fof(f74,plain,(
% 2.65/0.98    ( ! [X0,X1] : (X0 != X1 | k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) != k1_tarski(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f50])).
% 2.65/0.98  
% 2.65/0.98  fof(f4,axiom,(
% 2.65/0.98    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f60,plain,(
% 2.65/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f4])).
% 2.65/0.98  
% 2.65/0.98  fof(f19,axiom,(
% 2.65/0.98    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f78,plain,(
% 2.65/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f19])).
% 2.65/0.98  
% 2.65/0.98  fof(f103,plain,(
% 2.65/0.98    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.65/0.98    inference(definition_unfolding,[],[f78,f102])).
% 2.65/0.98  
% 2.65/0.98  fof(f104,plain,(
% 2.65/0.98    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.65/0.98    inference(definition_unfolding,[],[f60,f103])).
% 2.65/0.98  
% 2.65/0.98  fof(f107,plain,(
% 2.65/0.98    ( ! [X0,X1] : (X0 != X1 | k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.65/0.98    inference(definition_unfolding,[],[f74,f104,f105,f105,f105])).
% 2.65/0.98  
% 2.65/0.98  fof(f116,plain,(
% 2.65/0.98    ( ! [X1] : (k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k1_setfam_1(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 2.65/0.98    inference(equality_resolution,[],[f107])).
% 2.65/0.98  
% 2.65/0.98  fof(f7,axiom,(
% 2.65/0.98    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f63,plain,(
% 2.65/0.98    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f7])).
% 2.65/0.98  
% 2.65/0.98  fof(f18,axiom,(
% 2.65/0.98    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 2.65/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f77,plain,(
% 2.65/0.98    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 2.65/0.98    inference(cnf_transformation,[],[f18])).
% 2.65/0.98  
% 2.65/0.98  fof(f108,plain,(
% 2.65/0.98    ( ! [X0] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.65/0.98    inference(definition_unfolding,[],[f77,f105])).
% 2.65/0.98  
% 2.65/0.98  cnf(c_17,plain,
% 2.65/0.98      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_21,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.65/0.98      | v1_partfun1(X0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | v1_xboole_0(X2) ),
% 2.65/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_26,plain,
% 2.65/0.98      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.65/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.65/0.98      | ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_353,plain,
% 2.65/0.98      ( v1_partfun1(X0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ r1_tarski(k2_relat_1(X3),X4)
% 2.65/0.98      | ~ v1_relat_1(X3)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X3)
% 2.65/0.98      | v1_xboole_0(X2)
% 2.65/0.98      | X3 != X0
% 2.65/0.98      | X4 != X2
% 2.65/0.98      | k1_relat_1(X3) != X1 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_26]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_354,plain,
% 2.65/0.98      ( v1_partfun1(X0,k1_relat_1(X0))
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.65/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.65/0.98      | ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | v1_xboole_0(X1) ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_353]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_25,plain,
% 2.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.65/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.65/0.98      | ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_356,plain,
% 2.65/0.98      ( v1_partfun1(X0,k1_relat_1(X0))
% 2.65/0.98      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.65/0.98      | ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | v1_xboole_0(X1) ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_354,c_25]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2430,plain,
% 2.65/0.98      ( v1_partfun1(X0,k1_relat_1(X0)) = iProver_top
% 2.65/0.98      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 2.65/0.98      | v1_relat_1(X0) != iProver_top
% 2.65/0.98      | v1_funct_1(X0) != iProver_top
% 2.65/0.98      | v1_xboole_0(X1) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_356]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2733,plain,
% 2.65/0.98      ( v1_partfun1(k1_xboole_0,k1_relat_1(k1_xboole_0)) = iProver_top
% 2.65/0.98      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.65/0.98      | v1_relat_1(k1_xboole_0) != iProver_top
% 2.65/0.98      | v1_funct_1(k1_xboole_0) != iProver_top
% 2.65/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_17,c_2430]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_18,plain,
% 2.65/0.98      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2734,plain,
% 2.65/0.98      ( v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top
% 2.65/0.98      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 2.65/0.98      | v1_relat_1(k1_xboole_0) != iProver_top
% 2.65/0.98      | v1_funct_1(k1_xboole_0) != iProver_top
% 2.65/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_2733,c_18]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_19,plain,
% 2.65/0.98      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_60,plain,
% 2.65/0.98      ( v1_funct_1(X0) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_62,plain,
% 2.65/0.98      ( v1_funct_1(k1_xboole_0) = iProver_top
% 2.65/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_60]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5,plain,
% 2.65/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_81,plain,
% 2.65/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_0,plain,
% 2.65/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_90,plain,
% 2.65/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_20,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | v1_relat_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2628,plain,
% 2.65/0.98      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.65/0.98      | v1_relat_1(k1_xboole_0) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_20]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2630,plain,
% 2.65/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.65/0.98      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2628]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_13,plain,
% 2.65/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.65/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2629,plain,
% 2.65/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2632,plain,
% 2.65/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2629]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4454,plain,
% 2.65/0.98      ( v1_partfun1(k1_xboole_0,k1_xboole_0) = iProver_top
% 2.65/0.98      | v1_xboole_0(X0) = iProver_top ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_2734,c_62,c_81,c_90,c_2630,c_2632]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_32,negated_conjecture,
% 2.65/0.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.65/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_376,plain,
% 2.65/0.98      ( v1_partfun1(X0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | v1_xboole_0(X2)
% 2.65/0.98      | sK1 != X2
% 2.65/0.98      | sK0 != X1
% 2.65/0.98      | sK2 != X0 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_377,plain,
% 2.65/0.98      ( v1_partfun1(sK2,sK0)
% 2.65/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.65/0.98      | ~ v1_funct_1(sK2)
% 2.65/0.98      | v1_xboole_0(sK1) ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_376]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_33,negated_conjecture,
% 2.65/0.98      ( v1_funct_1(sK2) ),
% 2.65/0.98      inference(cnf_transformation,[],[f93]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_31,negated_conjecture,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.65/0.98      inference(cnf_transformation,[],[f95]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_379,plain,
% 2.65/0.98      ( v1_partfun1(sK2,sK0) | v1_xboole_0(sK1) ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_377,c_33,c_31]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2429,plain,
% 2.65/0.98      ( v1_partfun1(sK2,sK0) = iProver_top
% 2.65/0.98      | v1_xboole_0(sK1) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2432,plain,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_24,plain,
% 2.65/0.98      ( ~ v1_partfun1(X0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_partfun1(X1,X2,X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f110]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2435,plain,
% 2.65/0.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k5_partfun1(X1,X2,X0)
% 2.65/0.98      | v1_partfun1(X0,X1) != iProver_top
% 2.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.65/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4215,plain,
% 2.65/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
% 2.65/0.98      | v1_partfun1(sK2,sK0) != iProver_top
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_2432,c_2435]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_34,plain,
% 2.65/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_36,plain,
% 2.65/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2685,plain,
% 2.65/0.98      ( ~ v1_partfun1(sK2,sK0)
% 2.65/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 2.65/0.98      | ~ v1_funct_1(sK2)
% 2.65/0.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_partfun1(sK0,X0,sK2) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_24]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2812,plain,
% 2.65/0.98      ( ~ v1_partfun1(sK2,sK0)
% 2.65/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.65/0.98      | ~ v1_funct_1(sK2)
% 2.65/0.98      | k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_2685]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2813,plain,
% 2.65/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) = k5_partfun1(sK0,sK1,sK2)
% 2.65/0.98      | v1_partfun1(sK2,sK0) != iProver_top
% 2.65/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.65/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2812]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_28,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k3_partfun1(X0,X1,X2) = X0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2433,plain,
% 2.65/0.98      ( k3_partfun1(X0,X1,X2) = X0
% 2.65/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.65/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3144,plain,
% 2.65/0.98      ( k3_partfun1(sK2,sK0,sK1) = sK2 | v1_funct_1(sK2) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_2432,c_2433]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2659,plain,
% 2.65/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.65/0.98      | ~ v1_funct_1(sK2)
% 2.65/0.98      | k3_partfun1(sK2,sK0,sK1) = sK2 ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_28]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3289,plain,
% 2.65/0.98      ( k3_partfun1(sK2,sK0,sK1) = sK2 ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_3144,c_33,c_31,c_2659]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_29,negated_conjecture,
% 2.65/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_partfun1(sK0,sK1,k3_partfun1(sK2,sK0,sK1)) ),
% 2.65/0.98      inference(cnf_transformation,[],[f111]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3292,plain,
% 2.65/0.98      ( k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) != k5_partfun1(sK0,sK1,sK2) ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_3289,c_29]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4581,plain,
% 2.65/0.98      ( v1_partfun1(sK2,sK0) != iProver_top ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_4215,c_34,c_36,c_2813,c_3292]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4586,plain,
% 2.65/0.98      ( v1_xboole_0(sK1) = iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_2429,c_4581]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1,plain,
% 2.65/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2446,plain,
% 2.65/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4674,plain,
% 2.65/0.98      ( sK1 = k1_xboole_0 ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_4586,c_2446]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_16,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.65/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2439,plain,
% 2.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.65/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3214,plain,
% 2.65/0.98      ( r1_tarski(sK2,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_2432,c_2439]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4684,plain,
% 2.65/0.98      ( r1_tarski(sK2,k2_zfmisc_1(sK0,k1_xboole_0)) = iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_4674,c_3214]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_30,negated_conjecture,
% 2.65/0.98      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f96]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4687,plain,
% 2.65/0.98      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_4674,c_30]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4688,plain,
% 2.65/0.98      ( sK0 = k1_xboole_0 ),
% 2.65/0.98      inference(equality_resolution_simp,[status(thm)],[c_4687]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4695,plain,
% 2.65/0.98      ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_4684,c_4688]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_9,plain,
% 2.65/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f115]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4697,plain,
% 2.65/0.98      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_4695,c_9]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2443,plain,
% 2.65/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2,plain,
% 2.65/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.65/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2445,plain,
% 2.65/0.98      ( X0 = X1
% 2.65/0.98      | r1_tarski(X0,X1) != iProver_top
% 2.65/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3555,plain,
% 2.65/0.98      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_2443,c_2445]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5075,plain,
% 2.65/0.98      ( sK2 = k1_xboole_0 ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_4697,c_3555]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4837,plain,
% 2.65/0.98      ( v1_partfun1(sK2,k1_xboole_0) != iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_4688,c_4581]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5218,plain,
% 2.65/0.98      ( v1_partfun1(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_5075,c_4837]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5347,plain,
% 2.65/0.98      ( v1_xboole_0(X0) = iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_4454,c_5218]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_6,plain,
% 2.65/0.98      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2442,plain,
% 2.65/0.98      ( X0 = X1
% 2.65/0.98      | v1_xboole_0(X1) != iProver_top
% 2.65/0.98      | v1_xboole_0(X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5479,plain,
% 2.65/0.98      ( X0 = X1 | v1_xboole_0(X0) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_5347,c_2442]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5485,plain,
% 2.65/0.98      ( X0 = X1 ),
% 2.65/0.98      inference(forward_subsumption_resolution,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_5479,c_5347]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_12,plain,
% 2.65/0.98      ( k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_setfam_1(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) != k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f116]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_7,plain,
% 2.65/0.98      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_14,plain,
% 2.65/0.98      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f108]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2560,plain,
% 2.65/0.98      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k1_xboole_0 ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_12,c_7,c_14]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5653,plain,
% 2.65/0.98      ( k1_xboole_0 != X0 ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_5485,c_2560]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4456,plain,
% 2.65/0.98      ( v1_partfun1(k1_xboole_0,k1_xboole_0) | v1_xboole_0(X0) ),
% 2.65/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_4454]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3722,plain,
% 2.65/0.98      ( r1_tarski(k1_xboole_0,sK2) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3725,plain,
% 2.65/0.98      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_3722]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1908,plain,
% 2.65/0.98      ( ~ v1_partfun1(X0,X1) | v1_partfun1(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.65/0.98      theory(equality) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3494,plain,
% 2.65/0.98      ( ~ v1_partfun1(X0,X1)
% 2.65/0.98      | v1_partfun1(sK2,sK0)
% 2.65/0.98      | sK0 != X1
% 2.65/0.98      | sK2 != X0 ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_1908]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3496,plain,
% 2.65/0.98      ( v1_partfun1(sK2,sK0)
% 2.65/0.98      | ~ v1_partfun1(k1_xboole_0,k1_xboole_0)
% 2.65/0.98      | sK0 != k1_xboole_0
% 2.65/0.98      | sK2 != k1_xboole_0 ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_3494]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3248,plain,
% 2.65/0.98      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3249,plain,
% 2.65/0.98      ( sK2 = X0
% 2.65/0.98      | r1_tarski(X0,sK2) != iProver_top
% 2.65/0.98      | r1_tarski(sK2,X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_3248]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3251,plain,
% 2.65/0.98      ( sK2 = k1_xboole_0
% 2.65/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 2.65/0.98      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_3249]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5740,plain,
% 2.65/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 2.65/0.98      inference(grounding,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_5653:[bind(X0,$fot(k1_xboole_0))]]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5741,plain,
% 2.65/0.98      ( v1_partfun1(k1_xboole_0,k1_xboole_0) | v1_xboole_0(k1_xboole_0) ),
% 2.65/0.98      inference(grounding,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_4456:[bind(X0,$fot(k1_xboole_0))]]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5742,plain,
% 2.65/0.98      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.65/0.98      inference(grounding,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_1:[bind(X0,$fot(k1_xboole_0))]]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(contradiction,plain,
% 2.65/0.98      ( $false ),
% 2.65/0.98      inference(minisat,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_5740,c_4697,c_4688,c_5741,c_3725,c_3496,c_3292,c_3251,
% 2.65/0.98                 c_2812,c_5742,c_31,c_33]) ).
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  ------                               Statistics
% 2.65/0.98  
% 2.65/0.98  ------ General
% 2.65/0.98  
% 2.65/0.98  abstr_ref_over_cycles:                  0
% 2.65/0.98  abstr_ref_under_cycles:                 0
% 2.65/0.98  gc_basic_clause_elim:                   0
% 2.65/0.98  forced_gc_time:                         0
% 2.65/0.98  parsing_time:                           0.008
% 2.65/0.98  unif_index_cands_time:                  0.
% 2.65/0.98  unif_index_add_time:                    0.
% 2.65/0.98  orderings_time:                         0.
% 2.65/0.98  out_proof_time:                         0.01
% 2.65/0.98  total_time:                             0.148
% 2.65/0.98  num_of_symbols:                         51
% 2.65/0.98  num_of_terms:                           3706
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing
% 2.65/0.98  
% 2.65/0.98  num_of_splits:                          0
% 2.65/0.98  num_of_split_atoms:                     0
% 2.65/0.98  num_of_reused_defs:                     0
% 2.65/0.98  num_eq_ax_congr_red:                    8
% 2.65/0.98  num_of_sem_filtered_clauses:            1
% 2.65/0.98  num_of_subtypes:                        0
% 2.65/0.98  monotx_restored_types:                  0
% 2.65/0.98  sat_num_of_epr_types:                   0
% 2.65/0.98  sat_num_of_non_cyclic_types:            0
% 2.65/0.98  sat_guarded_non_collapsed_types:        0
% 2.65/0.98  num_pure_diseq_elim:                    0
% 2.65/0.98  simp_replaced_by:                       0
% 2.65/0.98  res_preprocessed:                       154
% 2.65/0.98  prep_upred:                             0
% 2.65/0.98  prep_unflattend:                        62
% 2.65/0.98  smt_new_axioms:                         0
% 2.65/0.98  pred_elim_cands:                        6
% 2.65/0.98  pred_elim:                              1
% 2.65/0.98  pred_elim_cl:                           1
% 2.65/0.98  pred_elim_cycles:                       10
% 2.65/0.98  merged_defs:                            8
% 2.65/0.98  merged_defs_ncl:                        0
% 2.65/0.98  bin_hyper_res:                          8
% 2.65/0.98  prep_cycles:                            4
% 2.65/0.98  pred_elim_time:                         0.016
% 2.65/0.98  splitting_time:                         0.
% 2.65/0.98  sem_filter_time:                        0.
% 2.65/0.98  monotx_time:                            0.
% 2.65/0.98  subtype_inf_time:                       0.
% 2.65/0.98  
% 2.65/0.98  ------ Problem properties
% 2.65/0.98  
% 2.65/0.98  clauses:                                30
% 2.65/0.98  conjectures:                            4
% 2.65/0.98  epr:                                    10
% 2.65/0.98  horn:                                   26
% 2.65/0.98  ground:                                 8
% 2.65/0.98  unary:                                  14
% 2.65/0.98  binary:                                 8
% 2.65/0.99  lits:                                   59
% 2.65/0.99  lits_eq:                                21
% 2.65/0.99  fd_pure:                                0
% 2.65/0.99  fd_pseudo:                              0
% 2.65/0.99  fd_cond:                                2
% 2.65/0.99  fd_pseudo_cond:                         3
% 2.65/0.99  ac_symbols:                             0
% 2.65/0.99  
% 2.65/0.99  ------ Propositional Solver
% 2.65/0.99  
% 2.65/0.99  prop_solver_calls:                      28
% 2.65/0.99  prop_fast_solver_calls:                 1158
% 2.65/0.99  smt_solver_calls:                       0
% 2.65/0.99  smt_fast_solver_calls:                  0
% 2.65/0.99  prop_num_of_clauses:                    1628
% 2.65/0.99  prop_preprocess_simplified:             5903
% 2.65/0.99  prop_fo_subsumed:                       31
% 2.65/0.99  prop_solver_time:                       0.
% 2.65/0.99  smt_solver_time:                        0.
% 2.65/0.99  smt_fast_solver_time:                   0.
% 2.65/0.99  prop_fast_solver_time:                  0.
% 2.65/0.99  prop_unsat_core_time:                   0.
% 2.65/0.99  
% 2.65/0.99  ------ QBF
% 2.65/0.99  
% 2.65/0.99  qbf_q_res:                              0
% 2.65/0.99  qbf_num_tautologies:                    0
% 2.65/0.99  qbf_prep_cycles:                        0
% 2.65/0.99  
% 2.65/0.99  ------ BMC1
% 2.65/0.99  
% 2.65/0.99  bmc1_current_bound:                     -1
% 2.65/0.99  bmc1_last_solved_bound:                 -1
% 2.65/0.99  bmc1_unsat_core_size:                   -1
% 2.65/0.99  bmc1_unsat_core_parents_size:           -1
% 2.65/0.99  bmc1_merge_next_fun:                    0
% 2.65/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.65/0.99  
% 2.65/0.99  ------ Instantiation
% 2.65/0.99  
% 2.65/0.99  inst_num_of_clauses:                    510
% 2.65/0.99  inst_num_in_passive:                    153
% 2.65/0.99  inst_num_in_active:                     246
% 2.65/0.99  inst_num_in_unprocessed:                112
% 2.65/0.99  inst_num_of_loops:                      340
% 2.65/0.99  inst_num_of_learning_restarts:          0
% 2.65/0.99  inst_num_moves_active_passive:          91
% 2.65/0.99  inst_lit_activity:                      0
% 2.65/0.99  inst_lit_activity_moves:                0
% 2.65/0.99  inst_num_tautologies:                   0
% 2.65/0.99  inst_num_prop_implied:                  0
% 2.65/0.99  inst_num_existing_simplified:           0
% 2.65/0.99  inst_num_eq_res_simplified:             0
% 2.65/0.99  inst_num_child_elim:                    0
% 2.65/0.99  inst_num_of_dismatching_blockings:      155
% 2.65/0.99  inst_num_of_non_proper_insts:           540
% 2.65/0.99  inst_num_of_duplicates:                 0
% 2.65/0.99  inst_inst_num_from_inst_to_res:         0
% 2.65/0.99  inst_dismatching_checking_time:         0.
% 2.65/0.99  
% 2.65/0.99  ------ Resolution
% 2.65/0.99  
% 2.65/0.99  res_num_of_clauses:                     0
% 2.65/0.99  res_num_in_passive:                     0
% 2.65/0.99  res_num_in_active:                      0
% 2.65/0.99  res_num_of_loops:                       158
% 2.65/0.99  res_forward_subset_subsumed:            57
% 2.65/0.99  res_backward_subset_subsumed:           2
% 2.65/0.99  res_forward_subsumed:                   0
% 2.65/0.99  res_backward_subsumed:                  0
% 2.65/0.99  res_forward_subsumption_resolution:     1
% 2.65/0.99  res_backward_subsumption_resolution:    0
% 2.65/0.99  res_clause_to_clause_subsumption:       310
% 2.65/0.99  res_orphan_elimination:                 0
% 2.65/0.99  res_tautology_del:                      63
% 2.65/0.99  res_num_eq_res_simplified:              0
% 2.65/0.99  res_num_sel_changes:                    0
% 2.65/0.99  res_moves_from_active_to_pass:          0
% 2.65/0.99  
% 2.65/0.99  ------ Superposition
% 2.65/0.99  
% 2.65/0.99  sup_time_total:                         0.
% 2.65/0.99  sup_time_generating:                    0.
% 2.65/0.99  sup_time_sim_full:                      0.
% 2.65/0.99  sup_time_sim_immed:                     0.
% 2.65/0.99  
% 2.65/0.99  sup_num_of_clauses:                     38
% 2.65/0.99  sup_num_in_active:                      24
% 2.65/0.99  sup_num_in_passive:                     14
% 2.65/0.99  sup_num_of_loops:                       67
% 2.65/0.99  sup_fw_superposition:                   63
% 2.65/0.99  sup_bw_superposition:                   25
% 2.65/0.99  sup_immediate_simplified:               26
% 2.65/0.99  sup_given_eliminated:                   2
% 2.65/0.99  comparisons_done:                       0
% 2.65/0.99  comparisons_avoided:                    2
% 2.65/0.99  
% 2.65/0.99  ------ Simplifications
% 2.65/0.99  
% 2.65/0.99  
% 2.65/0.99  sim_fw_subset_subsumed:                 5
% 2.65/0.99  sim_bw_subset_subsumed:                 6
% 2.65/0.99  sim_fw_subsumed:                        14
% 2.65/0.99  sim_bw_subsumed:                        4
% 2.65/0.99  sim_fw_subsumption_res:                 2
% 2.65/0.99  sim_bw_subsumption_res:                 2
% 2.65/0.99  sim_tautology_del:                      3
% 2.65/0.99  sim_eq_tautology_del:                   5
% 2.65/0.99  sim_eq_res_simp:                        1
% 2.65/0.99  sim_fw_demodulated:                     8
% 2.65/0.99  sim_bw_demodulated:                     39
% 2.65/0.99  sim_light_normalised:                   11
% 2.65/0.99  sim_joinable_taut:                      0
% 2.65/0.99  sim_joinable_simp:                      0
% 2.65/0.99  sim_ac_normalised:                      0
% 2.65/0.99  sim_smt_subsumption:                    0
% 2.65/0.99  
%------------------------------------------------------------------------------
