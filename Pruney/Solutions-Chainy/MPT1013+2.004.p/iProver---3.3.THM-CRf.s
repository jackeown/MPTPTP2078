%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:44 EST 2020

% Result     : Theorem 10.84s
% Output     : CNFRefutation 10.84s
% Verified   : 
% Statistics : Number of formulae       :  133 (1172 expanded)
%              Number of clauses        :   75 ( 399 expanded)
%              Number of leaves         :   16 ( 270 expanded)
%              Depth                    :   22
%              Number of atoms          :  323 (4226 expanded)
%              Number of equality atoms :  185 (2453 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   10 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v4_relat_1(X1,X0)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
         => ( ( k2_relset_1(X0,X0,X2) = X0
              & k2_relset_1(X0,X0,X1) = X0 )
           => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
           => ( ( k2_relset_1(X0,X0,X2) = X0
                & k2_relset_1(X0,X0,X1) = X0 )
             => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ),
    inference(flattening,[],[f40])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
          & k2_relset_1(X0,X0,X2) = X0
          & k2_relset_1(X0,X0,X1) = X0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
     => ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,sK2,X1)) != X0
        & k2_relset_1(X0,X0,sK2) = X0
        & k2_relset_1(X0,X0,X1) = X0
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0
            & k2_relset_1(X0,X0,X2) = X0
            & k2_relset_1(X0,X0,X1) = X0
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) )
   => ( ? [X2] :
          ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1)) != sK0
          & k2_relset_1(sK0,sK0,X2) = sK0
          & k2_relset_1(sK0,sK0,sK1) = sK0
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0
    & k2_relset_1(sK0,sK0,sK2) = sK0
    & k2_relset_1(sK0,sK0,sK1) = sK0
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f50,f49])).

fof(f79,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v4_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f81,plain,(
    k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f51])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f82,plain,(
    k2_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(cnf_transformation,[],[f51])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f38])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1091,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_16,plain,
    ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1098,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_10,plain,
    ( v4_relat_1(X0,X1)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1093,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4463,plain,
    ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1098,c_1093])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1077,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | v4_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1094,plain,
    ( v4_relat_1(X0,X1) != iProver_top
    | v4_relat_1(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3961,plain,
    ( v4_relat_1(k2_zfmisc_1(sK0,sK0),X0) != iProver_top
    | v4_relat_1(sK1,X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_1094])).

cnf(c_18736,plain,
    ( v4_relat_1(sK1,k1_relat_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4463,c_3961])).

cnf(c_19051,plain,
    ( sK0 = k1_xboole_0
    | v4_relat_1(sK1,sK0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16,c_18736])).

cnf(c_19636,plain,
    ( sK0 = k1_xboole_0
    | v4_relat_1(sK1,sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1091,c_19051])).

cnf(c_17,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1088,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_31628,plain,
    ( k7_relat_1(sK1,sK0) = sK1
    | sK0 = k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_19636,c_1088])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1082,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2011,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_1082])).

cnf(c_44814,plain,
    ( sK0 = k1_xboole_0
    | k7_relat_1(sK1,sK0) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_31628,c_2011])).

cnf(c_44815,plain,
    ( k7_relat_1(sK1,sK0) = sK1
    | sK0 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_44814])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1090,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2549,plain,
    ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(superposition,[status(thm)],[c_2011,c_1090])).

cnf(c_44818,plain,
    ( k9_relat_1(sK1,sK0) = k2_relat_1(sK1)
    | sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_44815,c_2549])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1080,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3243,plain,
    ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1077,c_1080])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3246,plain,
    ( k2_relat_1(sK1) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3243,c_29])).

cnf(c_44819,plain,
    ( k9_relat_1(sK1,sK0) = sK0
    | sK0 = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_44818,c_3246])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1078,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1081,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3241,plain,
    ( k2_relset_1(X0,X1,k4_relset_1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k4_relset_1(X0,X2,X3,X1,X4,X5))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1081,c_1080])).

cnf(c_10071,plain,
    ( k2_relset_1(X0,sK0,k4_relset_1(X0,X1,sK0,sK0,X2,sK1)) = k2_relat_1(k4_relset_1(X0,X1,sK0,sK0,X2,sK1))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_3241])).

cnf(c_11025,plain,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_1078,c_10071])).

cnf(c_2010,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1078,c_1082])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1089,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4512,plain,
    ( k9_relat_1(sK1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2011,c_1089])).

cnf(c_4764,plain,
    ( k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_2010,c_4512])).

cnf(c_3242,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1078,c_1080])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK0,sK2) = sK0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3247,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3242,c_28])).

cnf(c_4767,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_4764,c_3247])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1079,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5463,plain,
    ( k4_relset_1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_1079])).

cnf(c_6094,plain,
    ( k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(superposition,[status(thm)],[c_1078,c_5463])).

cnf(c_11034,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,sK0) ),
    inference(light_normalisation,[status(thm)],[c_11025,c_4767,c_6094])).

cnf(c_27,negated_conjecture,
    ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_6295,plain,
    ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) != sK0 ),
    inference(demodulation,[status(thm)],[c_6094,c_27])).

cnf(c_11233,plain,
    ( k9_relat_1(sK1,sK0) != sK0 ),
    inference(demodulation,[status(thm)],[c_11034,c_6295])).

cnf(c_45138,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_44819,c_11233])).

cnf(c_18735,plain,
    ( k7_relat_1(X0,k1_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4463,c_1088])).

cnf(c_39668,plain,
    ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
    inference(superposition,[status(thm)],[c_2011,c_18735])).

cnf(c_39902,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_39668,c_2549])).

cnf(c_39903,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_39902,c_3246])).

cnf(c_45178,plain,
    ( k9_relat_1(sK1,k1_relat_1(sK1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45138,c_39903])).

cnf(c_21,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1084,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3255,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3246,c_1084])).

cnf(c_3459,plain,
    ( sK0 != k1_xboole_0
    | k1_relat_1(sK1) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3255,c_2011])).

cnf(c_3460,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3459])).

cnf(c_45472,plain,
    ( k1_relat_1(sK1) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45138,c_3460])).

cnf(c_45489,plain,
    ( k1_relat_1(sK1) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_45472])).

cnf(c_45551,plain,
    ( k9_relat_1(sK1,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45178,c_45489])).

cnf(c_45403,plain,
    ( k9_relat_1(sK1,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45138,c_11233])).

cnf(c_45559,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_45551,c_45403])).

cnf(c_45574,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_45559])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:46:41 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 10.84/2.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.84/2.04  
% 10.84/2.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 10.84/2.04  
% 10.84/2.04  ------  iProver source info
% 10.84/2.04  
% 10.84/2.04  git: date: 2020-06-30 10:37:57 +0100
% 10.84/2.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 10.84/2.04  git: non_committed_changes: false
% 10.84/2.04  git: last_make_outside_of_git: false
% 10.84/2.04  
% 10.84/2.04  ------ 
% 10.84/2.04  
% 10.84/2.04  ------ Input Options
% 10.84/2.04  
% 10.84/2.04  --out_options                           all
% 10.84/2.04  --tptp_safe_out                         true
% 10.84/2.04  --problem_path                          ""
% 10.84/2.04  --include_path                          ""
% 10.84/2.04  --clausifier                            res/vclausify_rel
% 10.84/2.04  --clausifier_options                    ""
% 10.84/2.04  --stdin                                 false
% 10.84/2.04  --stats_out                             all
% 10.84/2.04  
% 10.84/2.04  ------ General Options
% 10.84/2.04  
% 10.84/2.04  --fof                                   false
% 10.84/2.04  --time_out_real                         305.
% 10.84/2.04  --time_out_virtual                      -1.
% 10.84/2.04  --symbol_type_check                     false
% 10.84/2.04  --clausify_out                          false
% 10.84/2.04  --sig_cnt_out                           false
% 10.84/2.04  --trig_cnt_out                          false
% 10.84/2.04  --trig_cnt_out_tolerance                1.
% 10.84/2.04  --trig_cnt_out_sk_spl                   false
% 10.84/2.04  --abstr_cl_out                          false
% 10.84/2.04  
% 10.84/2.04  ------ Global Options
% 10.84/2.04  
% 10.84/2.04  --schedule                              default
% 10.84/2.04  --add_important_lit                     false
% 10.84/2.04  --prop_solver_per_cl                    1000
% 10.84/2.04  --min_unsat_core                        false
% 10.84/2.04  --soft_assumptions                      false
% 10.84/2.04  --soft_lemma_size                       3
% 10.84/2.04  --prop_impl_unit_size                   0
% 10.84/2.04  --prop_impl_unit                        []
% 10.84/2.04  --share_sel_clauses                     true
% 10.84/2.04  --reset_solvers                         false
% 10.84/2.04  --bc_imp_inh                            [conj_cone]
% 10.84/2.04  --conj_cone_tolerance                   3.
% 10.84/2.04  --extra_neg_conj                        none
% 10.84/2.04  --large_theory_mode                     true
% 10.84/2.04  --prolific_symb_bound                   200
% 10.84/2.04  --lt_threshold                          2000
% 10.84/2.04  --clause_weak_htbl                      true
% 10.84/2.04  --gc_record_bc_elim                     false
% 10.84/2.04  
% 10.84/2.04  ------ Preprocessing Options
% 10.84/2.04  
% 10.84/2.04  --preprocessing_flag                    true
% 10.84/2.04  --time_out_prep_mult                    0.1
% 10.84/2.04  --splitting_mode                        input
% 10.84/2.04  --splitting_grd                         true
% 10.84/2.04  --splitting_cvd                         false
% 10.84/2.04  --splitting_cvd_svl                     false
% 10.84/2.04  --splitting_nvd                         32
% 10.84/2.04  --sub_typing                            true
% 10.84/2.04  --prep_gs_sim                           true
% 10.84/2.04  --prep_unflatten                        true
% 10.84/2.04  --prep_res_sim                          true
% 10.84/2.04  --prep_upred                            true
% 10.84/2.04  --prep_sem_filter                       exhaustive
% 10.84/2.04  --prep_sem_filter_out                   false
% 10.84/2.04  --pred_elim                             true
% 10.84/2.04  --res_sim_input                         true
% 10.84/2.04  --eq_ax_congr_red                       true
% 10.84/2.04  --pure_diseq_elim                       true
% 10.84/2.04  --brand_transform                       false
% 10.84/2.04  --non_eq_to_eq                          false
% 10.84/2.04  --prep_def_merge                        true
% 10.84/2.04  --prep_def_merge_prop_impl              false
% 10.84/2.04  --prep_def_merge_mbd                    true
% 10.84/2.04  --prep_def_merge_tr_red                 false
% 10.84/2.04  --prep_def_merge_tr_cl                  false
% 10.84/2.04  --smt_preprocessing                     true
% 10.84/2.04  --smt_ac_axioms                         fast
% 10.84/2.04  --preprocessed_out                      false
% 10.84/2.04  --preprocessed_stats                    false
% 10.84/2.04  
% 10.84/2.04  ------ Abstraction refinement Options
% 10.84/2.04  
% 10.84/2.04  --abstr_ref                             []
% 10.84/2.04  --abstr_ref_prep                        false
% 10.84/2.04  --abstr_ref_until_sat                   false
% 10.84/2.04  --abstr_ref_sig_restrict                funpre
% 10.84/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 10.84/2.04  --abstr_ref_under                       []
% 10.84/2.04  
% 10.84/2.04  ------ SAT Options
% 10.84/2.04  
% 10.84/2.04  --sat_mode                              false
% 10.84/2.04  --sat_fm_restart_options                ""
% 10.84/2.04  --sat_gr_def                            false
% 10.84/2.04  --sat_epr_types                         true
% 10.84/2.04  --sat_non_cyclic_types                  false
% 10.84/2.04  --sat_finite_models                     false
% 10.84/2.04  --sat_fm_lemmas                         false
% 10.84/2.04  --sat_fm_prep                           false
% 10.84/2.04  --sat_fm_uc_incr                        true
% 10.84/2.04  --sat_out_model                         small
% 10.84/2.04  --sat_out_clauses                       false
% 10.84/2.04  
% 10.84/2.04  ------ QBF Options
% 10.84/2.04  
% 10.84/2.04  --qbf_mode                              false
% 10.84/2.04  --qbf_elim_univ                         false
% 10.84/2.04  --qbf_dom_inst                          none
% 10.84/2.04  --qbf_dom_pre_inst                      false
% 10.84/2.04  --qbf_sk_in                             false
% 10.84/2.04  --qbf_pred_elim                         true
% 10.84/2.04  --qbf_split                             512
% 10.84/2.04  
% 10.84/2.04  ------ BMC1 Options
% 10.84/2.04  
% 10.84/2.04  --bmc1_incremental                      false
% 10.84/2.04  --bmc1_axioms                           reachable_all
% 10.84/2.04  --bmc1_min_bound                        0
% 10.84/2.04  --bmc1_max_bound                        -1
% 10.84/2.04  --bmc1_max_bound_default                -1
% 10.84/2.04  --bmc1_symbol_reachability              true
% 10.84/2.04  --bmc1_property_lemmas                  false
% 10.84/2.04  --bmc1_k_induction                      false
% 10.84/2.04  --bmc1_non_equiv_states                 false
% 10.84/2.04  --bmc1_deadlock                         false
% 10.84/2.04  --bmc1_ucm                              false
% 10.84/2.04  --bmc1_add_unsat_core                   none
% 10.84/2.04  --bmc1_unsat_core_children              false
% 10.84/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 10.84/2.04  --bmc1_out_stat                         full
% 10.84/2.04  --bmc1_ground_init                      false
% 10.84/2.04  --bmc1_pre_inst_next_state              false
% 10.84/2.04  --bmc1_pre_inst_state                   false
% 10.84/2.04  --bmc1_pre_inst_reach_state             false
% 10.84/2.04  --bmc1_out_unsat_core                   false
% 10.84/2.04  --bmc1_aig_witness_out                  false
% 10.84/2.04  --bmc1_verbose                          false
% 10.84/2.04  --bmc1_dump_clauses_tptp                false
% 10.84/2.04  --bmc1_dump_unsat_core_tptp             false
% 10.84/2.04  --bmc1_dump_file                        -
% 10.84/2.04  --bmc1_ucm_expand_uc_limit              128
% 10.84/2.04  --bmc1_ucm_n_expand_iterations          6
% 10.84/2.04  --bmc1_ucm_extend_mode                  1
% 10.84/2.04  --bmc1_ucm_init_mode                    2
% 10.84/2.04  --bmc1_ucm_cone_mode                    none
% 10.84/2.04  --bmc1_ucm_reduced_relation_type        0
% 10.84/2.04  --bmc1_ucm_relax_model                  4
% 10.84/2.04  --bmc1_ucm_full_tr_after_sat            true
% 10.84/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 10.84/2.04  --bmc1_ucm_layered_model                none
% 10.84/2.04  --bmc1_ucm_max_lemma_size               10
% 10.84/2.04  
% 10.84/2.04  ------ AIG Options
% 10.84/2.04  
% 10.84/2.04  --aig_mode                              false
% 10.84/2.04  
% 10.84/2.04  ------ Instantiation Options
% 10.84/2.04  
% 10.84/2.04  --instantiation_flag                    true
% 10.84/2.04  --inst_sos_flag                         true
% 10.84/2.04  --inst_sos_phase                        true
% 10.84/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.84/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.84/2.04  --inst_lit_sel_side                     num_symb
% 10.84/2.04  --inst_solver_per_active                1400
% 10.84/2.04  --inst_solver_calls_frac                1.
% 10.84/2.04  --inst_passive_queue_type               priority_queues
% 10.84/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.84/2.04  --inst_passive_queues_freq              [25;2]
% 10.84/2.04  --inst_dismatching                      true
% 10.84/2.04  --inst_eager_unprocessed_to_passive     true
% 10.84/2.04  --inst_prop_sim_given                   true
% 10.84/2.04  --inst_prop_sim_new                     false
% 10.84/2.04  --inst_subs_new                         false
% 10.84/2.04  --inst_eq_res_simp                      false
% 10.84/2.04  --inst_subs_given                       false
% 10.84/2.04  --inst_orphan_elimination               true
% 10.84/2.04  --inst_learning_loop_flag               true
% 10.84/2.04  --inst_learning_start                   3000
% 10.84/2.04  --inst_learning_factor                  2
% 10.84/2.04  --inst_start_prop_sim_after_learn       3
% 10.84/2.04  --inst_sel_renew                        solver
% 10.84/2.04  --inst_lit_activity_flag                true
% 10.84/2.04  --inst_restr_to_given                   false
% 10.84/2.04  --inst_activity_threshold               500
% 10.84/2.04  --inst_out_proof                        true
% 10.84/2.04  
% 10.84/2.04  ------ Resolution Options
% 10.84/2.04  
% 10.84/2.04  --resolution_flag                       true
% 10.84/2.04  --res_lit_sel                           adaptive
% 10.84/2.04  --res_lit_sel_side                      none
% 10.84/2.04  --res_ordering                          kbo
% 10.84/2.04  --res_to_prop_solver                    active
% 10.84/2.04  --res_prop_simpl_new                    false
% 10.84/2.04  --res_prop_simpl_given                  true
% 10.84/2.04  --res_passive_queue_type                priority_queues
% 10.84/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.84/2.04  --res_passive_queues_freq               [15;5]
% 10.84/2.04  --res_forward_subs                      full
% 10.84/2.04  --res_backward_subs                     full
% 10.84/2.04  --res_forward_subs_resolution           true
% 10.84/2.04  --res_backward_subs_resolution          true
% 10.84/2.04  --res_orphan_elimination                true
% 10.84/2.04  --res_time_limit                        2.
% 10.84/2.04  --res_out_proof                         true
% 10.84/2.04  
% 10.84/2.04  ------ Superposition Options
% 10.84/2.04  
% 10.84/2.04  --superposition_flag                    true
% 10.84/2.04  --sup_passive_queue_type                priority_queues
% 10.84/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.84/2.04  --sup_passive_queues_freq               [8;1;4]
% 10.84/2.04  --demod_completeness_check              fast
% 10.84/2.04  --demod_use_ground                      true
% 10.84/2.04  --sup_to_prop_solver                    passive
% 10.84/2.04  --sup_prop_simpl_new                    true
% 10.84/2.04  --sup_prop_simpl_given                  true
% 10.84/2.04  --sup_fun_splitting                     true
% 10.84/2.04  --sup_smt_interval                      50000
% 10.84/2.04  
% 10.84/2.04  ------ Superposition Simplification Setup
% 10.84/2.04  
% 10.84/2.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 10.84/2.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 10.84/2.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 10.84/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 10.84/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 10.84/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 10.84/2.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 10.84/2.04  --sup_immed_triv                        [TrivRules]
% 10.84/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.84/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 10.84/2.04  --sup_immed_bw_main                     []
% 10.84/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 10.84/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 10.84/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 10.84/2.04  --sup_input_bw                          []
% 10.84/2.04  
% 10.84/2.04  ------ Combination Options
% 10.84/2.04  
% 10.84/2.04  --comb_res_mult                         3
% 10.84/2.04  --comb_sup_mult                         2
% 10.84/2.04  --comb_inst_mult                        10
% 10.84/2.04  
% 10.84/2.04  ------ Debug Options
% 10.84/2.04  
% 10.84/2.04  --dbg_backtrace                         false
% 10.84/2.04  --dbg_dump_prop_clauses                 false
% 10.84/2.04  --dbg_dump_prop_clauses_file            -
% 10.84/2.04  --dbg_out_stat                          false
% 10.84/2.04  ------ Parsing...
% 10.84/2.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 10.84/2.04  
% 10.84/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe_e  sf_s  rm: 1 0s  sf_e  pe_s  pe_e 
% 10.84/2.04  
% 10.84/2.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 10.84/2.04  
% 10.84/2.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 10.84/2.04  ------ Proving...
% 10.84/2.04  ------ Problem Properties 
% 10.84/2.04  
% 10.84/2.04  
% 10.84/2.04  clauses                                 31
% 10.84/2.04  conjectures                             5
% 10.84/2.04  EPR                                     2
% 10.84/2.04  Horn                                    28
% 10.84/2.04  unary                                   10
% 10.84/2.04  binary                                  8
% 10.84/2.04  lits                                    66
% 10.84/2.04  lits eq                                 26
% 10.84/2.04  fd_pure                                 0
% 10.84/2.04  fd_pseudo                               0
% 10.84/2.04  fd_cond                                 1
% 10.84/2.04  fd_pseudo_cond                          1
% 10.84/2.04  AC symbols                              0
% 10.84/2.04  
% 10.84/2.04  ------ Schedule dynamic 5 is on 
% 10.84/2.04  
% 10.84/2.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 10.84/2.04  
% 10.84/2.04  
% 10.84/2.04  ------ 
% 10.84/2.04  Current options:
% 10.84/2.04  ------ 
% 10.84/2.04  
% 10.84/2.04  ------ Input Options
% 10.84/2.04  
% 10.84/2.04  --out_options                           all
% 10.84/2.04  --tptp_safe_out                         true
% 10.84/2.04  --problem_path                          ""
% 10.84/2.04  --include_path                          ""
% 10.84/2.04  --clausifier                            res/vclausify_rel
% 10.84/2.04  --clausifier_options                    ""
% 10.84/2.04  --stdin                                 false
% 10.84/2.04  --stats_out                             all
% 10.84/2.04  
% 10.84/2.04  ------ General Options
% 10.84/2.04  
% 10.84/2.04  --fof                                   false
% 10.84/2.04  --time_out_real                         305.
% 10.84/2.04  --time_out_virtual                      -1.
% 10.84/2.04  --symbol_type_check                     false
% 10.84/2.04  --clausify_out                          false
% 10.84/2.04  --sig_cnt_out                           false
% 10.84/2.04  --trig_cnt_out                          false
% 10.84/2.04  --trig_cnt_out_tolerance                1.
% 10.84/2.04  --trig_cnt_out_sk_spl                   false
% 10.84/2.04  --abstr_cl_out                          false
% 10.84/2.04  
% 10.84/2.04  ------ Global Options
% 10.84/2.04  
% 10.84/2.04  --schedule                              default
% 10.84/2.04  --add_important_lit                     false
% 10.84/2.04  --prop_solver_per_cl                    1000
% 10.84/2.04  --min_unsat_core                        false
% 10.84/2.04  --soft_assumptions                      false
% 10.84/2.04  --soft_lemma_size                       3
% 10.84/2.04  --prop_impl_unit_size                   0
% 10.84/2.04  --prop_impl_unit                        []
% 10.84/2.04  --share_sel_clauses                     true
% 10.84/2.04  --reset_solvers                         false
% 10.84/2.04  --bc_imp_inh                            [conj_cone]
% 10.84/2.04  --conj_cone_tolerance                   3.
% 10.84/2.04  --extra_neg_conj                        none
% 10.84/2.04  --large_theory_mode                     true
% 10.84/2.04  --prolific_symb_bound                   200
% 10.84/2.04  --lt_threshold                          2000
% 10.84/2.04  --clause_weak_htbl                      true
% 10.84/2.04  --gc_record_bc_elim                     false
% 10.84/2.04  
% 10.84/2.04  ------ Preprocessing Options
% 10.84/2.04  
% 10.84/2.04  --preprocessing_flag                    true
% 10.84/2.04  --time_out_prep_mult                    0.1
% 10.84/2.04  --splitting_mode                        input
% 10.84/2.04  --splitting_grd                         true
% 10.84/2.04  --splitting_cvd                         false
% 10.84/2.04  --splitting_cvd_svl                     false
% 10.84/2.04  --splitting_nvd                         32
% 10.84/2.04  --sub_typing                            true
% 10.84/2.04  --prep_gs_sim                           true
% 10.84/2.04  --prep_unflatten                        true
% 10.84/2.04  --prep_res_sim                          true
% 10.84/2.04  --prep_upred                            true
% 10.84/2.04  --prep_sem_filter                       exhaustive
% 10.84/2.04  --prep_sem_filter_out                   false
% 10.84/2.04  --pred_elim                             true
% 10.84/2.04  --res_sim_input                         true
% 10.84/2.04  --eq_ax_congr_red                       true
% 10.84/2.04  --pure_diseq_elim                       true
% 10.84/2.04  --brand_transform                       false
% 10.84/2.04  --non_eq_to_eq                          false
% 10.84/2.04  --prep_def_merge                        true
% 10.84/2.04  --prep_def_merge_prop_impl              false
% 10.84/2.04  --prep_def_merge_mbd                    true
% 10.84/2.04  --prep_def_merge_tr_red                 false
% 10.84/2.04  --prep_def_merge_tr_cl                  false
% 10.84/2.04  --smt_preprocessing                     true
% 10.84/2.04  --smt_ac_axioms                         fast
% 10.84/2.04  --preprocessed_out                      false
% 10.84/2.04  --preprocessed_stats                    false
% 10.84/2.04  
% 10.84/2.04  ------ Abstraction refinement Options
% 10.84/2.04  
% 10.84/2.04  --abstr_ref                             []
% 10.84/2.04  --abstr_ref_prep                        false
% 10.84/2.04  --abstr_ref_until_sat                   false
% 10.84/2.04  --abstr_ref_sig_restrict                funpre
% 10.84/2.04  --abstr_ref_af_restrict_to_split_sk     false
% 10.84/2.04  --abstr_ref_under                       []
% 10.84/2.04  
% 10.84/2.04  ------ SAT Options
% 10.84/2.04  
% 10.84/2.04  --sat_mode                              false
% 10.84/2.04  --sat_fm_restart_options                ""
% 10.84/2.04  --sat_gr_def                            false
% 10.84/2.04  --sat_epr_types                         true
% 10.84/2.04  --sat_non_cyclic_types                  false
% 10.84/2.04  --sat_finite_models                     false
% 10.84/2.04  --sat_fm_lemmas                         false
% 10.84/2.04  --sat_fm_prep                           false
% 10.84/2.04  --sat_fm_uc_incr                        true
% 10.84/2.04  --sat_out_model                         small
% 10.84/2.04  --sat_out_clauses                       false
% 10.84/2.04  
% 10.84/2.04  ------ QBF Options
% 10.84/2.04  
% 10.84/2.04  --qbf_mode                              false
% 10.84/2.04  --qbf_elim_univ                         false
% 10.84/2.04  --qbf_dom_inst                          none
% 10.84/2.04  --qbf_dom_pre_inst                      false
% 10.84/2.04  --qbf_sk_in                             false
% 10.84/2.04  --qbf_pred_elim                         true
% 10.84/2.04  --qbf_split                             512
% 10.84/2.04  
% 10.84/2.04  ------ BMC1 Options
% 10.84/2.04  
% 10.84/2.04  --bmc1_incremental                      false
% 10.84/2.04  --bmc1_axioms                           reachable_all
% 10.84/2.04  --bmc1_min_bound                        0
% 10.84/2.04  --bmc1_max_bound                        -1
% 10.84/2.04  --bmc1_max_bound_default                -1
% 10.84/2.04  --bmc1_symbol_reachability              true
% 10.84/2.04  --bmc1_property_lemmas                  false
% 10.84/2.04  --bmc1_k_induction                      false
% 10.84/2.04  --bmc1_non_equiv_states                 false
% 10.84/2.04  --bmc1_deadlock                         false
% 10.84/2.04  --bmc1_ucm                              false
% 10.84/2.04  --bmc1_add_unsat_core                   none
% 10.84/2.04  --bmc1_unsat_core_children              false
% 10.84/2.04  --bmc1_unsat_core_extrapolate_axioms    false
% 10.84/2.04  --bmc1_out_stat                         full
% 10.84/2.04  --bmc1_ground_init                      false
% 10.84/2.04  --bmc1_pre_inst_next_state              false
% 10.84/2.04  --bmc1_pre_inst_state                   false
% 10.84/2.04  --bmc1_pre_inst_reach_state             false
% 10.84/2.04  --bmc1_out_unsat_core                   false
% 10.84/2.04  --bmc1_aig_witness_out                  false
% 10.84/2.04  --bmc1_verbose                          false
% 10.84/2.04  --bmc1_dump_clauses_tptp                false
% 10.84/2.04  --bmc1_dump_unsat_core_tptp             false
% 10.84/2.04  --bmc1_dump_file                        -
% 10.84/2.04  --bmc1_ucm_expand_uc_limit              128
% 10.84/2.04  --bmc1_ucm_n_expand_iterations          6
% 10.84/2.04  --bmc1_ucm_extend_mode                  1
% 10.84/2.04  --bmc1_ucm_init_mode                    2
% 10.84/2.04  --bmc1_ucm_cone_mode                    none
% 10.84/2.04  --bmc1_ucm_reduced_relation_type        0
% 10.84/2.04  --bmc1_ucm_relax_model                  4
% 10.84/2.04  --bmc1_ucm_full_tr_after_sat            true
% 10.84/2.04  --bmc1_ucm_expand_neg_assumptions       false
% 10.84/2.04  --bmc1_ucm_layered_model                none
% 10.84/2.04  --bmc1_ucm_max_lemma_size               10
% 10.84/2.04  
% 10.84/2.04  ------ AIG Options
% 10.84/2.04  
% 10.84/2.04  --aig_mode                              false
% 10.84/2.04  
% 10.84/2.04  ------ Instantiation Options
% 10.84/2.04  
% 10.84/2.04  --instantiation_flag                    true
% 10.84/2.04  --inst_sos_flag                         true
% 10.84/2.04  --inst_sos_phase                        true
% 10.84/2.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 10.84/2.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 10.84/2.04  --inst_lit_sel_side                     none
% 10.84/2.04  --inst_solver_per_active                1400
% 10.84/2.04  --inst_solver_calls_frac                1.
% 10.84/2.04  --inst_passive_queue_type               priority_queues
% 10.84/2.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 10.84/2.04  --inst_passive_queues_freq              [25;2]
% 10.84/2.04  --inst_dismatching                      true
% 10.84/2.04  --inst_eager_unprocessed_to_passive     true
% 10.84/2.04  --inst_prop_sim_given                   true
% 10.84/2.04  --inst_prop_sim_new                     false
% 10.84/2.04  --inst_subs_new                         false
% 10.84/2.04  --inst_eq_res_simp                      false
% 10.84/2.04  --inst_subs_given                       false
% 10.84/2.04  --inst_orphan_elimination               true
% 10.84/2.04  --inst_learning_loop_flag               true
% 10.84/2.04  --inst_learning_start                   3000
% 10.84/2.04  --inst_learning_factor                  2
% 10.84/2.04  --inst_start_prop_sim_after_learn       3
% 10.84/2.04  --inst_sel_renew                        solver
% 10.84/2.04  --inst_lit_activity_flag                true
% 10.84/2.04  --inst_restr_to_given                   false
% 10.84/2.04  --inst_activity_threshold               500
% 10.84/2.04  --inst_out_proof                        true
% 10.84/2.04  
% 10.84/2.04  ------ Resolution Options
% 10.84/2.04  
% 10.84/2.04  --resolution_flag                       false
% 10.84/2.04  --res_lit_sel                           adaptive
% 10.84/2.04  --res_lit_sel_side                      none
% 10.84/2.04  --res_ordering                          kbo
% 10.84/2.04  --res_to_prop_solver                    active
% 10.84/2.04  --res_prop_simpl_new                    false
% 10.84/2.04  --res_prop_simpl_given                  true
% 10.84/2.04  --res_passive_queue_type                priority_queues
% 10.84/2.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 10.84/2.04  --res_passive_queues_freq               [15;5]
% 10.84/2.04  --res_forward_subs                      full
% 10.84/2.04  --res_backward_subs                     full
% 10.84/2.04  --res_forward_subs_resolution           true
% 10.84/2.04  --res_backward_subs_resolution          true
% 10.84/2.04  --res_orphan_elimination                true
% 10.84/2.04  --res_time_limit                        2.
% 10.84/2.04  --res_out_proof                         true
% 10.84/2.04  
% 10.84/2.04  ------ Superposition Options
% 10.84/2.04  
% 10.84/2.04  --superposition_flag                    true
% 10.84/2.04  --sup_passive_queue_type                priority_queues
% 10.84/2.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 10.84/2.04  --sup_passive_queues_freq               [8;1;4]
% 10.84/2.04  --demod_completeness_check              fast
% 10.84/2.04  --demod_use_ground                      true
% 10.84/2.04  --sup_to_prop_solver                    passive
% 10.84/2.04  --sup_prop_simpl_new                    true
% 10.84/2.04  --sup_prop_simpl_given                  true
% 10.84/2.04  --sup_fun_splitting                     true
% 10.84/2.04  --sup_smt_interval                      50000
% 10.84/2.04  
% 10.84/2.04  ------ Superposition Simplification Setup
% 10.84/2.04  
% 10.84/2.04  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 10.84/2.04  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 10.84/2.04  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 10.84/2.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 10.84/2.04  --sup_full_triv                         [TrivRules;PropSubs]
% 10.84/2.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 10.84/2.04  --sup_full_bw                           [BwDemod;BwSubsumption]
% 10.84/2.04  --sup_immed_triv                        [TrivRules]
% 10.84/2.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 10.84/2.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 10.84/2.04  --sup_immed_bw_main                     []
% 10.84/2.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 10.84/2.04  --sup_input_triv                        [Unflattening;TrivRules]
% 10.84/2.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 10.84/2.04  --sup_input_bw                          []
% 10.84/2.04  
% 10.84/2.04  ------ Combination Options
% 10.84/2.04  
% 10.84/2.04  --comb_res_mult                         3
% 10.84/2.04  --comb_sup_mult                         2
% 10.84/2.04  --comb_inst_mult                        10
% 10.84/2.04  
% 10.84/2.04  ------ Debug Options
% 10.84/2.04  
% 10.84/2.04  --dbg_backtrace                         false
% 10.84/2.04  --dbg_dump_prop_clauses                 false
% 10.84/2.04  --dbg_dump_prop_clauses_file            -
% 10.84/2.04  --dbg_out_stat                          false
% 10.84/2.04  
% 10.84/2.04  
% 10.84/2.04  
% 10.84/2.04  
% 10.84/2.04  ------ Proving...
% 10.84/2.04  
% 10.84/2.04  
% 10.84/2.04  % SZS status Theorem for theBenchmark.p
% 10.84/2.04  
% 10.84/2.04   Resolution empty clause
% 10.84/2.04  
% 10.84/2.04  % SZS output start CNFRefutation for theBenchmark.p
% 10.84/2.04  
% 10.84/2.04  fof(f8,axiom,(
% 10.84/2.04    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f64,plain,(
% 10.84/2.04    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 10.84/2.04    inference(cnf_transformation,[],[f8])).
% 10.84/2.04  
% 10.84/2.04  fof(f11,axiom,(
% 10.84/2.04    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f28,plain,(
% 10.84/2.04    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 10.84/2.04    inference(ennf_transformation,[],[f11])).
% 10.84/2.04  
% 10.84/2.04  fof(f67,plain,(
% 10.84/2.04    ( ! [X0,X1] : (k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 10.84/2.04    inference(cnf_transformation,[],[f28])).
% 10.84/2.04  
% 10.84/2.04  fof(f1,axiom,(
% 10.84/2.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f42,plain,(
% 10.84/2.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.84/2.04    inference(nnf_transformation,[],[f1])).
% 10.84/2.04  
% 10.84/2.04  fof(f43,plain,(
% 10.84/2.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 10.84/2.04    inference(flattening,[],[f42])).
% 10.84/2.04  
% 10.84/2.04  fof(f52,plain,(
% 10.84/2.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 10.84/2.04    inference(cnf_transformation,[],[f43])).
% 10.84/2.04  
% 10.84/2.04  fof(f85,plain,(
% 10.84/2.04    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 10.84/2.04    inference(equality_resolution,[],[f52])).
% 10.84/2.04  
% 10.84/2.04  fof(f7,axiom,(
% 10.84/2.04    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f25,plain,(
% 10.84/2.04    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 10.84/2.04    inference(ennf_transformation,[],[f7])).
% 10.84/2.04  
% 10.84/2.04  fof(f47,plain,(
% 10.84/2.04    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 10.84/2.04    inference(nnf_transformation,[],[f25])).
% 10.84/2.04  
% 10.84/2.04  fof(f63,plain,(
% 10.84/2.04    ( ! [X0,X1] : (v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 10.84/2.04    inference(cnf_transformation,[],[f47])).
% 10.84/2.04  
% 10.84/2.04  fof(f20,conjecture,(
% 10.84/2.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f21,negated_conjecture,(
% 10.84/2.04    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) => ((k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0) => k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) = X0)))),
% 10.84/2.04    inference(negated_conjecture,[],[f20])).
% 10.84/2.04  
% 10.84/2.04  fof(f40,plain,(
% 10.84/2.04    ? [X0,X1] : (? [X2] : ((k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & (k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 10.84/2.04    inference(ennf_transformation,[],[f21])).
% 10.84/2.04  
% 10.84/2.04  fof(f41,plain,(
% 10.84/2.04    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))),
% 10.84/2.04    inference(flattening,[],[f40])).
% 10.84/2.04  
% 10.84/2.04  fof(f50,plain,(
% 10.84/2.04    ( ! [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,sK2,X1)) != X0 & k2_relset_1(X0,X0,sK2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))))) )),
% 10.84/2.04    introduced(choice_axiom,[])).
% 10.84/2.04  
% 10.84/2.04  fof(f49,plain,(
% 10.84/2.04    ? [X0,X1] : (? [X2] : (k2_relset_1(X0,X0,k4_relset_1(X0,X0,X0,X0,X2,X1)) != X0 & k2_relset_1(X0,X0,X2) = X0 & k2_relset_1(X0,X0,X1) = X0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) => (? [X2] : (k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,X2,sK1)) != sK0 & k2_relset_1(sK0,sK0,X2) = sK0 & k2_relset_1(sK0,sK0,sK1) = sK0 & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))))),
% 10.84/2.04    introduced(choice_axiom,[])).
% 10.84/2.04  
% 10.84/2.04  fof(f51,plain,(
% 10.84/2.04    (k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 & k2_relset_1(sK0,sK0,sK2) = sK0 & k2_relset_1(sK0,sK0,sK1) = sK0 & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 10.84/2.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f50,f49])).
% 10.84/2.04  
% 10.84/2.04  fof(f79,plain,(
% 10.84/2.04    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 10.84/2.04    inference(cnf_transformation,[],[f51])).
% 10.84/2.04  
% 10.84/2.04  fof(f6,axiom,(
% 10.84/2.04    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v4_relat_1(X2,X0)))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f23,plain,(
% 10.84/2.04    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 10.84/2.04    inference(ennf_transformation,[],[f6])).
% 10.84/2.04  
% 10.84/2.04  fof(f24,plain,(
% 10.84/2.04    ! [X0,X1] : (! [X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 10.84/2.04    inference(flattening,[],[f23])).
% 10.84/2.04  
% 10.84/2.04  fof(f61,plain,(
% 10.84/2.04    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 10.84/2.04    inference(cnf_transformation,[],[f24])).
% 10.84/2.04  
% 10.84/2.04  fof(f12,axiom,(
% 10.84/2.04    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f29,plain,(
% 10.84/2.04    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 10.84/2.04    inference(ennf_transformation,[],[f12])).
% 10.84/2.04  
% 10.84/2.04  fof(f30,plain,(
% 10.84/2.04    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 10.84/2.04    inference(flattening,[],[f29])).
% 10.84/2.04  
% 10.84/2.04  fof(f69,plain,(
% 10.84/2.04    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 10.84/2.04    inference(cnf_transformation,[],[f30])).
% 10.84/2.04  
% 10.84/2.04  fof(f16,axiom,(
% 10.84/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f34,plain,(
% 10.84/2.04    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.84/2.04    inference(ennf_transformation,[],[f16])).
% 10.84/2.04  
% 10.84/2.04  fof(f75,plain,(
% 10.84/2.04    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.84/2.04    inference(cnf_transformation,[],[f34])).
% 10.84/2.04  
% 10.84/2.04  fof(f9,axiom,(
% 10.84/2.04    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f26,plain,(
% 10.84/2.04    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 10.84/2.04    inference(ennf_transformation,[],[f9])).
% 10.84/2.04  
% 10.84/2.04  fof(f65,plain,(
% 10.84/2.04    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 10.84/2.04    inference(cnf_transformation,[],[f26])).
% 10.84/2.04  
% 10.84/2.04  fof(f18,axiom,(
% 10.84/2.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f37,plain,(
% 10.84/2.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.84/2.04    inference(ennf_transformation,[],[f18])).
% 10.84/2.04  
% 10.84/2.04  fof(f77,plain,(
% 10.84/2.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.84/2.04    inference(cnf_transformation,[],[f37])).
% 10.84/2.04  
% 10.84/2.04  fof(f81,plain,(
% 10.84/2.04    k2_relset_1(sK0,sK0,sK1) = sK0),
% 10.84/2.04    inference(cnf_transformation,[],[f51])).
% 10.84/2.04  
% 10.84/2.04  fof(f80,plain,(
% 10.84/2.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 10.84/2.04    inference(cnf_transformation,[],[f51])).
% 10.84/2.04  
% 10.84/2.04  fof(f17,axiom,(
% 10.84/2.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f35,plain,(
% 10.84/2.04    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 10.84/2.04    inference(ennf_transformation,[],[f17])).
% 10.84/2.04  
% 10.84/2.04  fof(f36,plain,(
% 10.84/2.04    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.84/2.04    inference(flattening,[],[f35])).
% 10.84/2.04  
% 10.84/2.04  fof(f76,plain,(
% 10.84/2.04    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.84/2.04    inference(cnf_transformation,[],[f36])).
% 10.84/2.04  
% 10.84/2.04  fof(f10,axiom,(
% 10.84/2.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f27,plain,(
% 10.84/2.04    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 10.84/2.04    inference(ennf_transformation,[],[f10])).
% 10.84/2.04  
% 10.84/2.04  fof(f66,plain,(
% 10.84/2.04    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 10.84/2.04    inference(cnf_transformation,[],[f27])).
% 10.84/2.04  
% 10.84/2.04  fof(f82,plain,(
% 10.84/2.04    k2_relset_1(sK0,sK0,sK2) = sK0),
% 10.84/2.04    inference(cnf_transformation,[],[f51])).
% 10.84/2.04  
% 10.84/2.04  fof(f19,axiom,(
% 10.84/2.04    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f38,plain,(
% 10.84/2.04    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 10.84/2.04    inference(ennf_transformation,[],[f19])).
% 10.84/2.04  
% 10.84/2.04  fof(f39,plain,(
% 10.84/2.04    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 10.84/2.04    inference(flattening,[],[f38])).
% 10.84/2.04  
% 10.84/2.04  fof(f78,plain,(
% 10.84/2.04    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 10.84/2.04    inference(cnf_transformation,[],[f39])).
% 10.84/2.04  
% 10.84/2.04  fof(f83,plain,(
% 10.84/2.04    k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0),
% 10.84/2.04    inference(cnf_transformation,[],[f51])).
% 10.84/2.04  
% 10.84/2.04  fof(f15,axiom,(
% 10.84/2.04    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 10.84/2.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 10.84/2.04  
% 10.84/2.04  fof(f33,plain,(
% 10.84/2.04    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 10.84/2.04    inference(ennf_transformation,[],[f15])).
% 10.84/2.04  
% 10.84/2.04  fof(f48,plain,(
% 10.84/2.04    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 10.84/2.04    inference(nnf_transformation,[],[f33])).
% 10.84/2.04  
% 10.84/2.04  fof(f74,plain,(
% 10.84/2.04    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 10.84/2.04    inference(cnf_transformation,[],[f48])).
% 10.84/2.04  
% 10.84/2.04  cnf(c_12,plain,
% 10.84/2.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 10.84/2.04      inference(cnf_transformation,[],[f64]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1091,plain,
% 10.84/2.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_16,plain,
% 10.84/2.04      ( k1_relat_1(k2_zfmisc_1(X0,X1)) = X0
% 10.84/2.04      | k1_xboole_0 = X1
% 10.84/2.04      | k1_xboole_0 = X0 ),
% 10.84/2.04      inference(cnf_transformation,[],[f67]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f85]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1098,plain,
% 10.84/2.04      ( r1_tarski(X0,X0) = iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_10,plain,
% 10.84/2.04      ( v4_relat_1(X0,X1) | ~ r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 10.84/2.04      inference(cnf_transformation,[],[f63]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1093,plain,
% 10.84/2.04      ( v4_relat_1(X0,X1) = iProver_top
% 10.84/2.04      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 10.84/2.04      | v1_relat_1(X0) != iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_4463,plain,
% 10.84/2.04      ( v4_relat_1(X0,k1_relat_1(X0)) = iProver_top
% 10.84/2.04      | v1_relat_1(X0) != iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1098,c_1093]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_31,negated_conjecture,
% 10.84/2.04      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 10.84/2.04      inference(cnf_transformation,[],[f79]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1077,plain,
% 10.84/2.04      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_9,plain,
% 10.84/2.04      ( ~ v4_relat_1(X0,X1)
% 10.84/2.04      | v4_relat_1(X2,X1)
% 10.84/2.04      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 10.84/2.04      | ~ v1_relat_1(X0) ),
% 10.84/2.04      inference(cnf_transformation,[],[f61]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1094,plain,
% 10.84/2.04      ( v4_relat_1(X0,X1) != iProver_top
% 10.84/2.04      | v4_relat_1(X2,X1) = iProver_top
% 10.84/2.04      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 10.84/2.04      | v1_relat_1(X0) != iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_3961,plain,
% 10.84/2.04      ( v4_relat_1(k2_zfmisc_1(sK0,sK0),X0) != iProver_top
% 10.84/2.04      | v4_relat_1(sK1,X0) = iProver_top
% 10.84/2.04      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1077,c_1094]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_18736,plain,
% 10.84/2.04      ( v4_relat_1(sK1,k1_relat_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 10.84/2.04      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_4463,c_3961]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_19051,plain,
% 10.84/2.04      ( sK0 = k1_xboole_0
% 10.84/2.04      | v4_relat_1(sK1,sK0) = iProver_top
% 10.84/2.04      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_16,c_18736]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_19636,plain,
% 10.84/2.04      ( sK0 = k1_xboole_0 | v4_relat_1(sK1,sK0) = iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1091,c_19051]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_17,plain,
% 10.84/2.04      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 10.84/2.04      inference(cnf_transformation,[],[f69]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1088,plain,
% 10.84/2.04      ( k7_relat_1(X0,X1) = X0
% 10.84/2.04      | v4_relat_1(X0,X1) != iProver_top
% 10.84/2.04      | v1_relat_1(X0) != iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_31628,plain,
% 10.84/2.04      ( k7_relat_1(sK1,sK0) = sK1
% 10.84/2.04      | sK0 = k1_xboole_0
% 10.84/2.04      | v1_relat_1(sK1) != iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_19636,c_1088]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_23,plain,
% 10.84/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 10.84/2.04      inference(cnf_transformation,[],[f75]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1082,plain,
% 10.84/2.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 10.84/2.04      | v1_relat_1(X0) = iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_2011,plain,
% 10.84/2.04      ( v1_relat_1(sK1) = iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1077,c_1082]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_44814,plain,
% 10.84/2.04      ( sK0 = k1_xboole_0 | k7_relat_1(sK1,sK0) = sK1 ),
% 10.84/2.04      inference(global_propositional_subsumption,
% 10.84/2.04                [status(thm)],
% 10.84/2.04                [c_31628,c_2011]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_44815,plain,
% 10.84/2.04      ( k7_relat_1(sK1,sK0) = sK1 | sK0 = k1_xboole_0 ),
% 10.84/2.04      inference(renaming,[status(thm)],[c_44814]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_13,plain,
% 10.84/2.04      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 10.84/2.04      inference(cnf_transformation,[],[f65]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1090,plain,
% 10.84/2.04      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 10.84/2.04      | v1_relat_1(X0) != iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_2549,plain,
% 10.84/2.04      ( k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_2011,c_1090]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_44818,plain,
% 10.84/2.04      ( k9_relat_1(sK1,sK0) = k2_relat_1(sK1) | sK0 = k1_xboole_0 ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_44815,c_2549]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_25,plain,
% 10.84/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 10.84/2.04      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 10.84/2.04      inference(cnf_transformation,[],[f77]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1080,plain,
% 10.84/2.04      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 10.84/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_3243,plain,
% 10.84/2.04      ( k2_relset_1(sK0,sK0,sK1) = k2_relat_1(sK1) ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1077,c_1080]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_29,negated_conjecture,
% 10.84/2.04      ( k2_relset_1(sK0,sK0,sK1) = sK0 ),
% 10.84/2.04      inference(cnf_transformation,[],[f81]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_3246,plain,
% 10.84/2.04      ( k2_relat_1(sK1) = sK0 ),
% 10.84/2.04      inference(light_normalisation,[status(thm)],[c_3243,c_29]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_44819,plain,
% 10.84/2.04      ( k9_relat_1(sK1,sK0) = sK0 | sK0 = k1_xboole_0 ),
% 10.84/2.04      inference(light_normalisation,[status(thm)],[c_44818,c_3246]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_30,negated_conjecture,
% 10.84/2.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 10.84/2.04      inference(cnf_transformation,[],[f80]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1078,plain,
% 10.84/2.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_24,plain,
% 10.84/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 10.84/2.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 10.84/2.04      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 10.84/2.04      inference(cnf_transformation,[],[f76]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1081,plain,
% 10.84/2.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 10.84/2.04      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 10.84/2.04      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_3241,plain,
% 10.84/2.04      ( k2_relset_1(X0,X1,k4_relset_1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k4_relset_1(X0,X2,X3,X1,X4,X5))
% 10.84/2.04      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 10.84/2.04      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1081,c_1080]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_10071,plain,
% 10.84/2.04      ( k2_relset_1(X0,sK0,k4_relset_1(X0,X1,sK0,sK0,X2,sK1)) = k2_relat_1(k4_relset_1(X0,X1,sK0,sK0,X2,sK1))
% 10.84/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1077,c_3241]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_11025,plain,
% 10.84/2.04      ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) = k2_relat_1(k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1078,c_10071]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_2010,plain,
% 10.84/2.04      ( v1_relat_1(sK2) = iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1078,c_1082]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_14,plain,
% 10.84/2.04      ( ~ v1_relat_1(X0)
% 10.84/2.04      | ~ v1_relat_1(X1)
% 10.84/2.04      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 10.84/2.04      inference(cnf_transformation,[],[f66]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1089,plain,
% 10.84/2.04      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 10.84/2.04      | v1_relat_1(X0) != iProver_top
% 10.84/2.04      | v1_relat_1(X1) != iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_4512,plain,
% 10.84/2.04      ( k9_relat_1(sK1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK1))
% 10.84/2.04      | v1_relat_1(X0) != iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_2011,c_1089]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_4764,plain,
% 10.84/2.04      ( k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_2010,c_4512]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_3242,plain,
% 10.84/2.04      ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1078,c_1080]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_28,negated_conjecture,
% 10.84/2.04      ( k2_relset_1(sK0,sK0,sK2) = sK0 ),
% 10.84/2.04      inference(cnf_transformation,[],[f82]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_3247,plain,
% 10.84/2.04      ( k2_relat_1(sK2) = sK0 ),
% 10.84/2.04      inference(light_normalisation,[status(thm)],[c_3242,c_28]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_4767,plain,
% 10.84/2.04      ( k2_relat_1(k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,sK0) ),
% 10.84/2.04      inference(light_normalisation,[status(thm)],[c_4764,c_3247]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_26,plain,
% 10.84/2.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 10.84/2.04      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 10.84/2.04      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 10.84/2.04      inference(cnf_transformation,[],[f78]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1079,plain,
% 10.84/2.04      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 10.84/2.04      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 10.84/2.04      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_5463,plain,
% 10.84/2.04      ( k4_relset_1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 10.84/2.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1077,c_1079]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_6094,plain,
% 10.84/2.04      ( k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_1078,c_5463]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_11034,plain,
% 10.84/2.04      ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) = k9_relat_1(sK1,sK0) ),
% 10.84/2.04      inference(light_normalisation,[status(thm)],[c_11025,c_4767,c_6094]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_27,negated_conjecture,
% 10.84/2.04      ( k2_relset_1(sK0,sK0,k4_relset_1(sK0,sK0,sK0,sK0,sK2,sK1)) != sK0 ),
% 10.84/2.04      inference(cnf_transformation,[],[f83]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_6295,plain,
% 10.84/2.04      ( k2_relset_1(sK0,sK0,k5_relat_1(sK2,sK1)) != sK0 ),
% 10.84/2.04      inference(demodulation,[status(thm)],[c_6094,c_27]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_11233,plain,
% 10.84/2.04      ( k9_relat_1(sK1,sK0) != sK0 ),
% 10.84/2.04      inference(demodulation,[status(thm)],[c_11034,c_6295]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_45138,plain,
% 10.84/2.04      ( sK0 = k1_xboole_0 ),
% 10.84/2.04      inference(global_propositional_subsumption,
% 10.84/2.04                [status(thm)],
% 10.84/2.04                [c_44819,c_11233]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_18735,plain,
% 10.84/2.04      ( k7_relat_1(X0,k1_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_4463,c_1088]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_39668,plain,
% 10.84/2.04      ( k7_relat_1(sK1,k1_relat_1(sK1)) = sK1 ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_2011,c_18735]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_39902,plain,
% 10.84/2.04      ( k9_relat_1(sK1,k1_relat_1(sK1)) = k2_relat_1(sK1) ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_39668,c_2549]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_39903,plain,
% 10.84/2.04      ( k9_relat_1(sK1,k1_relat_1(sK1)) = sK0 ),
% 10.84/2.04      inference(light_normalisation,[status(thm)],[c_39902,c_3246]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_45178,plain,
% 10.84/2.04      ( k9_relat_1(sK1,k1_relat_1(sK1)) = k1_xboole_0 ),
% 10.84/2.04      inference(demodulation,[status(thm)],[c_45138,c_39903]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_21,plain,
% 10.84/2.04      ( ~ v1_relat_1(X0)
% 10.84/2.04      | k2_relat_1(X0) != k1_xboole_0
% 10.84/2.04      | k1_relat_1(X0) = k1_xboole_0 ),
% 10.84/2.04      inference(cnf_transformation,[],[f74]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_1084,plain,
% 10.84/2.04      ( k2_relat_1(X0) != k1_xboole_0
% 10.84/2.04      | k1_relat_1(X0) = k1_xboole_0
% 10.84/2.04      | v1_relat_1(X0) != iProver_top ),
% 10.84/2.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_3255,plain,
% 10.84/2.04      ( k1_relat_1(sK1) = k1_xboole_0
% 10.84/2.04      | sK0 != k1_xboole_0
% 10.84/2.04      | v1_relat_1(sK1) != iProver_top ),
% 10.84/2.04      inference(superposition,[status(thm)],[c_3246,c_1084]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_3459,plain,
% 10.84/2.04      ( sK0 != k1_xboole_0 | k1_relat_1(sK1) = k1_xboole_0 ),
% 10.84/2.04      inference(global_propositional_subsumption,[status(thm)],[c_3255,c_2011]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_3460,plain,
% 10.84/2.04      ( k1_relat_1(sK1) = k1_xboole_0 | sK0 != k1_xboole_0 ),
% 10.84/2.04      inference(renaming,[status(thm)],[c_3459]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_45472,plain,
% 10.84/2.04      ( k1_relat_1(sK1) = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 10.84/2.04      inference(demodulation,[status(thm)],[c_45138,c_3460]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_45489,plain,
% 10.84/2.04      ( k1_relat_1(sK1) = k1_xboole_0 ),
% 10.84/2.04      inference(equality_resolution_simp,[status(thm)],[c_45472]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_45551,plain,
% 10.84/2.04      ( k9_relat_1(sK1,k1_xboole_0) = k1_xboole_0 ),
% 10.84/2.04      inference(demodulation,[status(thm)],[c_45178,c_45489]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_45403,plain,
% 10.84/2.04      ( k9_relat_1(sK1,k1_xboole_0) != k1_xboole_0 ),
% 10.84/2.04      inference(demodulation,[status(thm)],[c_45138,c_11233]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_45559,plain,
% 10.84/2.04      ( k1_xboole_0 != k1_xboole_0 ),
% 10.84/2.04      inference(demodulation,[status(thm)],[c_45551,c_45403]) ).
% 10.84/2.04  
% 10.84/2.04  cnf(c_45574,plain,
% 10.84/2.04      ( $false ),
% 10.84/2.04      inference(equality_resolution_simp,[status(thm)],[c_45559]) ).
% 10.84/2.04  
% 10.84/2.04  
% 10.84/2.04  % SZS output end CNFRefutation for theBenchmark.p
% 10.84/2.04  
% 10.84/2.04  ------                               Statistics
% 10.84/2.04  
% 10.84/2.04  ------ General
% 10.84/2.04  
% 10.84/2.04  abstr_ref_over_cycles:                  0
% 10.84/2.04  abstr_ref_under_cycles:                 0
% 10.84/2.04  gc_basic_clause_elim:                   0
% 10.84/2.04  forced_gc_time:                         0
% 10.84/2.04  parsing_time:                           0.019
% 10.84/2.04  unif_index_cands_time:                  0.
% 10.84/2.04  unif_index_add_time:                    0.
% 10.84/2.04  orderings_time:                         0.
% 10.84/2.04  out_proof_time:                         0.012
% 10.84/2.04  total_time:                             1.287
% 10.84/2.04  num_of_symbols:                         48
% 10.84/2.04  num_of_terms:                           27785
% 10.84/2.04  
% 10.84/2.04  ------ Preprocessing
% 10.84/2.04  
% 10.84/2.04  num_of_splits:                          0
% 10.84/2.04  num_of_split_atoms:                     0
% 10.84/2.04  num_of_reused_defs:                     0
% 10.84/2.04  num_eq_ax_congr_red:                    15
% 10.84/2.04  num_of_sem_filtered_clauses:            1
% 10.84/2.04  num_of_subtypes:                        0
% 10.84/2.04  monotx_restored_types:                  0
% 10.84/2.04  sat_num_of_epr_types:                   0
% 10.84/2.04  sat_num_of_non_cyclic_types:            0
% 10.84/2.04  sat_guarded_non_collapsed_types:        0
% 10.84/2.04  num_pure_diseq_elim:                    0
% 10.84/2.04  simp_replaced_by:                       0
% 10.84/2.04  res_preprocessed:                       151
% 10.84/2.04  prep_upred:                             0
% 10.84/2.04  prep_unflattend:                        0
% 10.84/2.04  smt_new_axioms:                         0
% 10.84/2.04  pred_elim_cands:                        4
% 10.84/2.04  pred_elim:                              0
% 10.84/2.04  pred_elim_cl:                           0
% 10.84/2.04  pred_elim_cycles:                       2
% 10.84/2.04  merged_defs:                            8
% 10.84/2.04  merged_defs_ncl:                        0
% 10.84/2.04  bin_hyper_res:                          8
% 10.84/2.04  prep_cycles:                            4
% 10.84/2.04  pred_elim_time:                         0.001
% 10.84/2.04  splitting_time:                         0.
% 10.84/2.04  sem_filter_time:                        0.
% 10.84/2.04  monotx_time:                            0.001
% 10.84/2.04  subtype_inf_time:                       0.
% 10.84/2.04  
% 10.84/2.04  ------ Problem properties
% 10.84/2.04  
% 10.84/2.04  clauses:                                31
% 10.84/2.04  conjectures:                            5
% 10.84/2.04  epr:                                    2
% 10.84/2.04  horn:                                   28
% 10.84/2.04  ground:                                 5
% 10.84/2.04  unary:                                  10
% 10.84/2.04  binary:                                 8
% 10.84/2.04  lits:                                   66
% 10.84/2.04  lits_eq:                                26
% 10.84/2.04  fd_pure:                                0
% 10.84/2.04  fd_pseudo:                              0
% 10.84/2.04  fd_cond:                                1
% 10.84/2.04  fd_pseudo_cond:                         1
% 10.84/2.04  ac_symbols:                             0
% 10.84/2.04  
% 10.84/2.04  ------ Propositional Solver
% 10.84/2.04  
% 10.84/2.04  prop_solver_calls:                      34
% 10.84/2.04  prop_fast_solver_calls:                 1882
% 10.84/2.04  smt_solver_calls:                       0
% 10.84/2.04  smt_fast_solver_calls:                  0
% 10.84/2.04  prop_num_of_clauses:                    15893
% 10.84/2.04  prop_preprocess_simplified:             30687
% 10.84/2.04  prop_fo_subsumed:                       41
% 10.84/2.04  prop_solver_time:                       0.
% 10.84/2.04  smt_solver_time:                        0.
% 10.84/2.04  smt_fast_solver_time:                   0.
% 10.84/2.04  prop_fast_solver_time:                  0.
% 10.84/2.04  prop_unsat_core_time:                   0.
% 10.84/2.04  
% 10.84/2.04  ------ QBF
% 10.84/2.04  
% 10.84/2.04  qbf_q_res:                              0
% 10.84/2.04  qbf_num_tautologies:                    0
% 10.84/2.04  qbf_prep_cycles:                        0
% 10.84/2.04  
% 10.84/2.04  ------ BMC1
% 10.84/2.04  
% 10.84/2.04  bmc1_current_bound:                     -1
% 10.84/2.04  bmc1_last_solved_bound:                 -1
% 10.84/2.04  bmc1_unsat_core_size:                   -1
% 10.84/2.04  bmc1_unsat_core_parents_size:           -1
% 10.84/2.04  bmc1_merge_next_fun:                    0
% 10.84/2.04  bmc1_unsat_core_clauses_time:           0.
% 10.84/2.04  
% 10.84/2.04  ------ Instantiation
% 10.84/2.04  
% 10.84/2.04  inst_num_of_clauses:                    4568
% 10.84/2.04  inst_num_in_passive:                    2545
% 10.84/2.04  inst_num_in_active:                     1764
% 10.84/2.04  inst_num_in_unprocessed:                259
% 10.84/2.04  inst_num_of_loops:                      2500
% 10.84/2.04  inst_num_of_learning_restarts:          0
% 10.84/2.04  inst_num_moves_active_passive:          731
% 10.84/2.04  inst_lit_activity:                      0
% 10.84/2.04  inst_lit_activity_moves:                0
% 10.84/2.04  inst_num_tautologies:                   0
% 10.84/2.04  inst_num_prop_implied:                  0
% 10.84/2.04  inst_num_existing_simplified:           0
% 10.84/2.04  inst_num_eq_res_simplified:             0
% 10.84/2.04  inst_num_child_elim:                    0
% 10.84/2.04  inst_num_of_dismatching_blockings:      3579
% 10.84/2.04  inst_num_of_non_proper_insts:           7426
% 10.84/2.04  inst_num_of_duplicates:                 0
% 10.84/2.04  inst_inst_num_from_inst_to_res:         0
% 10.84/2.04  inst_dismatching_checking_time:         0.
% 10.84/2.04  
% 10.84/2.04  ------ Resolution
% 10.84/2.04  
% 10.84/2.04  res_num_of_clauses:                     0
% 10.84/2.04  res_num_in_passive:                     0
% 10.84/2.04  res_num_in_active:                      0
% 10.84/2.04  res_num_of_loops:                       155
% 10.84/2.04  res_forward_subset_subsumed:            711
% 10.84/2.04  res_backward_subset_subsumed:           0
% 10.84/2.04  res_forward_subsumed:                   0
% 10.84/2.04  res_backward_subsumed:                  0
% 10.84/2.04  res_forward_subsumption_resolution:     0
% 10.84/2.04  res_backward_subsumption_resolution:    0
% 10.84/2.04  res_clause_to_clause_subsumption:       14519
% 10.84/2.04  res_orphan_elimination:                 0
% 10.84/2.04  res_tautology_del:                      465
% 10.84/2.04  res_num_eq_res_simplified:              0
% 10.84/2.04  res_num_sel_changes:                    0
% 10.84/2.04  res_moves_from_active_to_pass:          0
% 10.84/2.04  
% 10.84/2.04  ------ Superposition
% 10.84/2.04  
% 10.84/2.04  sup_time_total:                         0.
% 10.84/2.04  sup_time_generating:                    0.
% 10.84/2.04  sup_time_sim_full:                      0.
% 10.84/2.04  sup_time_sim_immed:                     0.
% 10.84/2.04  
% 10.84/2.04  sup_num_of_clauses:                     1280
% 10.84/2.04  sup_num_in_active:                      133
% 10.84/2.04  sup_num_in_passive:                     1147
% 10.84/2.04  sup_num_of_loops:                       498
% 10.84/2.04  sup_fw_superposition:                   1915
% 10.84/2.04  sup_bw_superposition:                   423
% 10.84/2.04  sup_immediate_simplified:               327
% 10.84/2.04  sup_given_eliminated:                   0
% 10.84/2.04  comparisons_done:                       0
% 10.84/2.04  comparisons_avoided:                    31
% 10.84/2.04  
% 10.84/2.04  ------ Simplifications
% 10.84/2.04  
% 10.84/2.04  
% 10.84/2.04  sim_fw_subset_subsumed:                 11
% 10.84/2.04  sim_bw_subset_subsumed:                 23
% 10.84/2.04  sim_fw_subsumed:                        46
% 10.84/2.04  sim_bw_subsumed:                        10
% 10.84/2.04  sim_fw_subsumption_res:                 0
% 10.84/2.04  sim_bw_subsumption_res:                 0
% 10.84/2.04  sim_tautology_del:                      20
% 10.84/2.04  sim_eq_tautology_del:                   202
% 10.84/2.04  sim_eq_res_simp:                        4
% 10.84/2.04  sim_fw_demodulated:                     129
% 10.84/2.04  sim_bw_demodulated:                     382
% 10.84/2.04  sim_light_normalised:                   222
% 10.84/2.04  sim_joinable_taut:                      0
% 10.84/2.04  sim_joinable_simp:                      0
% 10.84/2.04  sim_ac_normalised:                      0
% 10.84/2.04  sim_smt_subsumption:                    0
% 10.84/2.04  
%------------------------------------------------------------------------------
