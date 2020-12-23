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
% DateTime   : Thu Dec  3 12:08:56 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :  175 (1670 expanded)
%              Number of clauses        :  100 ( 535 expanded)
%              Number of leaves         :   24 ( 332 expanded)
%              Depth                    :   20
%              Number of atoms          :  472 (4948 expanded)
%              Number of equality atoms :  259 (1940 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f18,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f78,f81])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f23,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f39,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f48,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK3),sK2)
        | k1_relat_1(sK3) != sK1 )
      & r2_hidden(sK3,k1_funct_2(sK1,sK2))
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK3),sK2)
      | k1_relat_1(sK3) != sK1 )
    & r2_hidden(sK3,k1_funct_2(sK1,sK2))
    & v1_relat_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f48])).

fof(f83,plain,(
    r2_hidden(sK3,k1_funct_2(sK1,sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f88,plain,(
    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
    inference(definition_unfolding,[],[f83,f81])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f41])).

fof(f43,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f80,f81])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f82,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f79,f81])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f84,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k1_relat_1(sK3) != sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f68,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1906,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_28,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1890,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1905,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3307,plain,
    ( k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) = k1_xboole_0
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1890,c_1905])).

cnf(c_6987,plain,
    ( k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1906,c_3307])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1887,plain,
    ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1907,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2521,plain,
    ( v1_xboole_0(k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_1907])).

cnf(c_3308,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1890,c_2521])).

cnf(c_7346,plain,
    ( k5_partfun1(sK2,k1_xboole_0,k3_partfun1(k1_xboole_0,sK2,k1_xboole_0)) = k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6987,c_3308])).

cnf(c_7588,plain,
    ( k5_partfun1(sK2,k1_xboole_0,k3_partfun1(k1_xboole_0,sK2,k1_xboole_0)) = k1_xboole_0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7346,c_1905])).

cnf(c_111,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1269,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3181,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_4474,plain,
    ( ~ v1_xboole_0(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_4475,plain,
    ( k1_xboole_0 = sK1
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4474])).

cnf(c_1270,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3183,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_1270])).

cnf(c_6068,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_3183])).

cnf(c_6069,plain,
    ( sK1 != sK1
    | sK1 = k1_xboole_0
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_6068])).

cnf(c_29,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1889,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3251,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1887,c_1889])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1902,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3630,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3251,c_1902])).

cnf(c_8,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_10,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1900,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4084,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_1900])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_96,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_6958,plain,
    ( v1_relat_1(X2) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4084,c_96])).

cnf(c_6959,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6958])).

cnf(c_6968,plain,
    ( sK1 = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3630,c_6959])).

cnf(c_33,negated_conjecture,
    ( v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_30,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_477,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_30,c_27])).

cnf(c_481,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_477,c_29])).

cnf(c_1885,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_481])).

cnf(c_3291,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1887,c_1885])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1893,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3633,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3251,c_1893])).

cnf(c_3758,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3291,c_3633])).

cnf(c_31,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k1_relat_1(sK3) != sK1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1888,plain,
    ( k1_relat_1(sK3) != sK1
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3846,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3758,c_1888])).

cnf(c_3895,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3846])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1897,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3844,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3758,c_1897])).

cnf(c_34,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_1273,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2202,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | k2_relat_1(sK3) != X0
    | sK2 != X1 ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_2404,plain,
    ( ~ r1_tarski(X0,sK2)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | k2_relat_1(sK3) != X0
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_2406,plain,
    ( k2_relat_1(sK3) != X0
    | sK2 != sK2
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2404])).

cnf(c_2408,plain,
    ( k2_relat_1(sK3) != k1_xboole_0
    | sK2 != sK2
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2406])).

cnf(c_2405,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1269])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2918,plain,
    ( r1_tarski(k1_xboole_0,sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2921,plain,
    ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2918])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1895,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3843,plain,
    ( k2_relat_1(sK3) = k1_xboole_0
    | sK1 != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3758,c_1895])).

cnf(c_4619,plain,
    ( sK1 != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3844,c_34,c_2408,c_2405,c_2921,c_3843,c_3846])).

cnf(c_6982,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | sK1 = k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6968])).

cnf(c_7602,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6968,c_33,c_3895,c_4619,c_6982])).

cnf(c_7610,plain,
    ( v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7602,c_3308])).

cnf(c_7895,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7588,c_111,c_3181,c_4475,c_6069,c_7610])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k6_relat_1(X1),X0)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1891,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k6_relat_1(X0),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3632,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | r1_tarski(k6_relat_1(sK1),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3251,c_1891])).

cnf(c_3636,plain,
    ( k1_relat_1(sK3) = sK1
    | r1_tarski(k6_relat_1(sK1),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3632,c_3633])).

cnf(c_7902,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k6_relat_1(k1_xboole_0),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7895,c_3636])).

cnf(c_17,plain,
    ( k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2775,plain,
    ( k6_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_17,c_1897])).

cnf(c_18,plain,
    ( v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_71,plain,
    ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3041,plain,
    ( k1_xboole_0 != X0
    | k6_relat_1(X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2775,c_71])).

cnf(c_3042,plain,
    ( k6_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(renaming,[status(thm)],[c_3041])).

cnf(c_3046,plain,
    ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[status(thm)],[c_3042])).

cnf(c_7906,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7902,c_3046])).

cnf(c_7616,plain,
    ( k1_relat_1(sK3) != sK1
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7602,c_1888])).

cnf(c_7900,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7895,c_7616])).

cnf(c_7921,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_7900])).

cnf(c_5421,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK3),X2)
    | X2 != X1
    | k2_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_5423,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k2_relat_1(sK3) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5421])).

cnf(c_2786,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2789,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2786])).

cnf(c_2126,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != k1_xboole_0
    | k2_relat_1(sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_109,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_106,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7906,c_7921,c_5423,c_2789,c_2126,c_2,c_109,c_106,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:20:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 2.80/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.01  
% 2.80/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.80/1.01  
% 2.80/1.01  ------  iProver source info
% 2.80/1.01  
% 2.80/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.80/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.80/1.01  git: non_committed_changes: false
% 2.80/1.01  git: last_make_outside_of_git: false
% 2.80/1.01  
% 2.80/1.01  ------ 
% 2.80/1.01  
% 2.80/1.01  ------ Input Options
% 2.80/1.01  
% 2.80/1.01  --out_options                           all
% 2.80/1.01  --tptp_safe_out                         true
% 2.80/1.01  --problem_path                          ""
% 2.80/1.01  --include_path                          ""
% 2.80/1.01  --clausifier                            res/vclausify_rel
% 2.80/1.01  --clausifier_options                    --mode clausify
% 2.80/1.01  --stdin                                 false
% 2.80/1.01  --stats_out                             all
% 2.80/1.01  
% 2.80/1.01  ------ General Options
% 2.80/1.01  
% 2.80/1.01  --fof                                   false
% 2.80/1.01  --time_out_real                         305.
% 2.80/1.01  --time_out_virtual                      -1.
% 2.80/1.01  --symbol_type_check                     false
% 2.80/1.01  --clausify_out                          false
% 2.80/1.01  --sig_cnt_out                           false
% 2.80/1.01  --trig_cnt_out                          false
% 2.80/1.01  --trig_cnt_out_tolerance                1.
% 2.80/1.01  --trig_cnt_out_sk_spl                   false
% 2.80/1.01  --abstr_cl_out                          false
% 2.80/1.01  
% 2.80/1.01  ------ Global Options
% 2.80/1.01  
% 2.80/1.01  --schedule                              default
% 2.80/1.01  --add_important_lit                     false
% 2.80/1.01  --prop_solver_per_cl                    1000
% 2.80/1.01  --min_unsat_core                        false
% 2.80/1.01  --soft_assumptions                      false
% 2.80/1.01  --soft_lemma_size                       3
% 2.80/1.01  --prop_impl_unit_size                   0
% 2.80/1.01  --prop_impl_unit                        []
% 2.80/1.01  --share_sel_clauses                     true
% 2.80/1.01  --reset_solvers                         false
% 2.80/1.01  --bc_imp_inh                            [conj_cone]
% 2.80/1.01  --conj_cone_tolerance                   3.
% 2.80/1.01  --extra_neg_conj                        none
% 2.80/1.01  --large_theory_mode                     true
% 2.80/1.01  --prolific_symb_bound                   200
% 2.80/1.01  --lt_threshold                          2000
% 2.80/1.01  --clause_weak_htbl                      true
% 2.80/1.01  --gc_record_bc_elim                     false
% 2.80/1.01  
% 2.80/1.01  ------ Preprocessing Options
% 2.80/1.01  
% 2.80/1.01  --preprocessing_flag                    true
% 2.80/1.01  --time_out_prep_mult                    0.1
% 2.80/1.01  --splitting_mode                        input
% 2.80/1.01  --splitting_grd                         true
% 2.80/1.01  --splitting_cvd                         false
% 2.80/1.01  --splitting_cvd_svl                     false
% 2.80/1.01  --splitting_nvd                         32
% 2.80/1.01  --sub_typing                            true
% 2.80/1.01  --prep_gs_sim                           true
% 2.80/1.01  --prep_unflatten                        true
% 2.80/1.01  --prep_res_sim                          true
% 2.80/1.01  --prep_upred                            true
% 2.80/1.01  --prep_sem_filter                       exhaustive
% 2.80/1.01  --prep_sem_filter_out                   false
% 2.80/1.01  --pred_elim                             true
% 2.80/1.01  --res_sim_input                         true
% 2.80/1.01  --eq_ax_congr_red                       true
% 2.80/1.01  --pure_diseq_elim                       true
% 2.80/1.01  --brand_transform                       false
% 2.80/1.01  --non_eq_to_eq                          false
% 2.80/1.01  --prep_def_merge                        true
% 2.80/1.01  --prep_def_merge_prop_impl              false
% 2.80/1.01  --prep_def_merge_mbd                    true
% 2.80/1.01  --prep_def_merge_tr_red                 false
% 2.80/1.01  --prep_def_merge_tr_cl                  false
% 2.80/1.01  --smt_preprocessing                     true
% 2.80/1.01  --smt_ac_axioms                         fast
% 2.80/1.01  --preprocessed_out                      false
% 2.80/1.01  --preprocessed_stats                    false
% 2.80/1.01  
% 2.80/1.01  ------ Abstraction refinement Options
% 2.80/1.01  
% 2.80/1.01  --abstr_ref                             []
% 2.80/1.01  --abstr_ref_prep                        false
% 2.80/1.01  --abstr_ref_until_sat                   false
% 2.80/1.01  --abstr_ref_sig_restrict                funpre
% 2.80/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/1.01  --abstr_ref_under                       []
% 2.80/1.01  
% 2.80/1.01  ------ SAT Options
% 2.80/1.01  
% 2.80/1.01  --sat_mode                              false
% 2.80/1.01  --sat_fm_restart_options                ""
% 2.80/1.01  --sat_gr_def                            false
% 2.80/1.01  --sat_epr_types                         true
% 2.80/1.01  --sat_non_cyclic_types                  false
% 2.80/1.01  --sat_finite_models                     false
% 2.80/1.01  --sat_fm_lemmas                         false
% 2.80/1.01  --sat_fm_prep                           false
% 2.80/1.01  --sat_fm_uc_incr                        true
% 2.80/1.01  --sat_out_model                         small
% 2.80/1.01  --sat_out_clauses                       false
% 2.80/1.01  
% 2.80/1.01  ------ QBF Options
% 2.80/1.01  
% 2.80/1.01  --qbf_mode                              false
% 2.80/1.01  --qbf_elim_univ                         false
% 2.80/1.01  --qbf_dom_inst                          none
% 2.80/1.01  --qbf_dom_pre_inst                      false
% 2.80/1.01  --qbf_sk_in                             false
% 2.80/1.01  --qbf_pred_elim                         true
% 2.80/1.01  --qbf_split                             512
% 2.80/1.01  
% 2.80/1.01  ------ BMC1 Options
% 2.80/1.01  
% 2.80/1.01  --bmc1_incremental                      false
% 2.80/1.01  --bmc1_axioms                           reachable_all
% 2.80/1.01  --bmc1_min_bound                        0
% 2.80/1.01  --bmc1_max_bound                        -1
% 2.80/1.01  --bmc1_max_bound_default                -1
% 2.80/1.01  --bmc1_symbol_reachability              true
% 2.80/1.01  --bmc1_property_lemmas                  false
% 2.80/1.01  --bmc1_k_induction                      false
% 2.80/1.01  --bmc1_non_equiv_states                 false
% 2.80/1.01  --bmc1_deadlock                         false
% 2.80/1.01  --bmc1_ucm                              false
% 2.80/1.01  --bmc1_add_unsat_core                   none
% 2.80/1.01  --bmc1_unsat_core_children              false
% 2.80/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/1.01  --bmc1_out_stat                         full
% 2.80/1.01  --bmc1_ground_init                      false
% 2.80/1.01  --bmc1_pre_inst_next_state              false
% 2.80/1.01  --bmc1_pre_inst_state                   false
% 2.80/1.01  --bmc1_pre_inst_reach_state             false
% 2.80/1.01  --bmc1_out_unsat_core                   false
% 2.80/1.01  --bmc1_aig_witness_out                  false
% 2.80/1.01  --bmc1_verbose                          false
% 2.80/1.01  --bmc1_dump_clauses_tptp                false
% 2.80/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.80/1.01  --bmc1_dump_file                        -
% 2.80/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.80/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.80/1.01  --bmc1_ucm_extend_mode                  1
% 2.80/1.01  --bmc1_ucm_init_mode                    2
% 2.80/1.01  --bmc1_ucm_cone_mode                    none
% 2.80/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.80/1.01  --bmc1_ucm_relax_model                  4
% 2.80/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.80/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/1.01  --bmc1_ucm_layered_model                none
% 2.80/1.01  --bmc1_ucm_max_lemma_size               10
% 2.80/1.01  
% 2.80/1.01  ------ AIG Options
% 2.80/1.01  
% 2.80/1.01  --aig_mode                              false
% 2.80/1.01  
% 2.80/1.01  ------ Instantiation Options
% 2.80/1.01  
% 2.80/1.01  --instantiation_flag                    true
% 2.80/1.01  --inst_sos_flag                         false
% 2.80/1.01  --inst_sos_phase                        true
% 2.80/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/1.01  --inst_lit_sel_side                     num_symb
% 2.80/1.01  --inst_solver_per_active                1400
% 2.80/1.01  --inst_solver_calls_frac                1.
% 2.80/1.01  --inst_passive_queue_type               priority_queues
% 2.80/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/1.01  --inst_passive_queues_freq              [25;2]
% 2.80/1.01  --inst_dismatching                      true
% 2.80/1.01  --inst_eager_unprocessed_to_passive     true
% 2.80/1.01  --inst_prop_sim_given                   true
% 2.80/1.01  --inst_prop_sim_new                     false
% 2.80/1.01  --inst_subs_new                         false
% 2.80/1.01  --inst_eq_res_simp                      false
% 2.80/1.01  --inst_subs_given                       false
% 2.80/1.01  --inst_orphan_elimination               true
% 2.80/1.01  --inst_learning_loop_flag               true
% 2.80/1.01  --inst_learning_start                   3000
% 2.80/1.01  --inst_learning_factor                  2
% 2.80/1.01  --inst_start_prop_sim_after_learn       3
% 2.80/1.01  --inst_sel_renew                        solver
% 2.80/1.01  --inst_lit_activity_flag                true
% 2.80/1.01  --inst_restr_to_given                   false
% 2.80/1.01  --inst_activity_threshold               500
% 2.80/1.01  --inst_out_proof                        true
% 2.80/1.01  
% 2.80/1.01  ------ Resolution Options
% 2.80/1.01  
% 2.80/1.01  --resolution_flag                       true
% 2.80/1.01  --res_lit_sel                           adaptive
% 2.80/1.01  --res_lit_sel_side                      none
% 2.80/1.01  --res_ordering                          kbo
% 2.80/1.01  --res_to_prop_solver                    active
% 2.80/1.01  --res_prop_simpl_new                    false
% 2.80/1.01  --res_prop_simpl_given                  true
% 2.80/1.01  --res_passive_queue_type                priority_queues
% 2.80/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/1.01  --res_passive_queues_freq               [15;5]
% 2.80/1.01  --res_forward_subs                      full
% 2.80/1.01  --res_backward_subs                     full
% 2.80/1.01  --res_forward_subs_resolution           true
% 2.80/1.01  --res_backward_subs_resolution          true
% 2.80/1.01  --res_orphan_elimination                true
% 2.80/1.01  --res_time_limit                        2.
% 2.80/1.01  --res_out_proof                         true
% 2.80/1.01  
% 2.80/1.01  ------ Superposition Options
% 2.80/1.01  
% 2.80/1.01  --superposition_flag                    true
% 2.80/1.01  --sup_passive_queue_type                priority_queues
% 2.80/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.80/1.01  --demod_completeness_check              fast
% 2.80/1.01  --demod_use_ground                      true
% 2.80/1.01  --sup_to_prop_solver                    passive
% 2.80/1.01  --sup_prop_simpl_new                    true
% 2.80/1.01  --sup_prop_simpl_given                  true
% 2.80/1.01  --sup_fun_splitting                     false
% 2.80/1.01  --sup_smt_interval                      50000
% 2.80/1.01  
% 2.80/1.01  ------ Superposition Simplification Setup
% 2.80/1.01  
% 2.80/1.01  --sup_indices_passive                   []
% 2.80/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_full_bw                           [BwDemod]
% 2.80/1.01  --sup_immed_triv                        [TrivRules]
% 2.80/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_immed_bw_main                     []
% 2.80/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.01  
% 2.80/1.01  ------ Combination Options
% 2.80/1.01  
% 2.80/1.01  --comb_res_mult                         3
% 2.80/1.01  --comb_sup_mult                         2
% 2.80/1.01  --comb_inst_mult                        10
% 2.80/1.01  
% 2.80/1.01  ------ Debug Options
% 2.80/1.01  
% 2.80/1.01  --dbg_backtrace                         false
% 2.80/1.01  --dbg_dump_prop_clauses                 false
% 2.80/1.01  --dbg_dump_prop_clauses_file            -
% 2.80/1.01  --dbg_out_stat                          false
% 2.80/1.01  ------ Parsing...
% 2.80/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.80/1.01  
% 2.80/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.80/1.01  
% 2.80/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.80/1.01  
% 2.80/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.80/1.01  ------ Proving...
% 2.80/1.01  ------ Problem Properties 
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  clauses                                 30
% 2.80/1.01  conjectures                             3
% 2.80/1.01  EPR                                     5
% 2.80/1.01  Horn                                    24
% 2.80/1.01  unary                                   8
% 2.80/1.01  binary                                  9
% 2.80/1.01  lits                                    67
% 2.80/1.01  lits eq                                 25
% 2.80/1.01  fd_pure                                 0
% 2.80/1.01  fd_pseudo                               0
% 2.80/1.01  fd_cond                                 4
% 2.80/1.01  fd_pseudo_cond                          0
% 2.80/1.01  AC symbols                              0
% 2.80/1.01  
% 2.80/1.01  ------ Schedule dynamic 5 is on 
% 2.80/1.01  
% 2.80/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  ------ 
% 2.80/1.01  Current options:
% 2.80/1.01  ------ 
% 2.80/1.01  
% 2.80/1.01  ------ Input Options
% 2.80/1.01  
% 2.80/1.01  --out_options                           all
% 2.80/1.01  --tptp_safe_out                         true
% 2.80/1.01  --problem_path                          ""
% 2.80/1.01  --include_path                          ""
% 2.80/1.01  --clausifier                            res/vclausify_rel
% 2.80/1.01  --clausifier_options                    --mode clausify
% 2.80/1.01  --stdin                                 false
% 2.80/1.01  --stats_out                             all
% 2.80/1.01  
% 2.80/1.01  ------ General Options
% 2.80/1.01  
% 2.80/1.01  --fof                                   false
% 2.80/1.01  --time_out_real                         305.
% 2.80/1.01  --time_out_virtual                      -1.
% 2.80/1.01  --symbol_type_check                     false
% 2.80/1.01  --clausify_out                          false
% 2.80/1.01  --sig_cnt_out                           false
% 2.80/1.01  --trig_cnt_out                          false
% 2.80/1.01  --trig_cnt_out_tolerance                1.
% 2.80/1.01  --trig_cnt_out_sk_spl                   false
% 2.80/1.01  --abstr_cl_out                          false
% 2.80/1.01  
% 2.80/1.01  ------ Global Options
% 2.80/1.01  
% 2.80/1.01  --schedule                              default
% 2.80/1.01  --add_important_lit                     false
% 2.80/1.01  --prop_solver_per_cl                    1000
% 2.80/1.01  --min_unsat_core                        false
% 2.80/1.01  --soft_assumptions                      false
% 2.80/1.01  --soft_lemma_size                       3
% 2.80/1.01  --prop_impl_unit_size                   0
% 2.80/1.01  --prop_impl_unit                        []
% 2.80/1.01  --share_sel_clauses                     true
% 2.80/1.01  --reset_solvers                         false
% 2.80/1.01  --bc_imp_inh                            [conj_cone]
% 2.80/1.01  --conj_cone_tolerance                   3.
% 2.80/1.01  --extra_neg_conj                        none
% 2.80/1.01  --large_theory_mode                     true
% 2.80/1.01  --prolific_symb_bound                   200
% 2.80/1.01  --lt_threshold                          2000
% 2.80/1.01  --clause_weak_htbl                      true
% 2.80/1.01  --gc_record_bc_elim                     false
% 2.80/1.01  
% 2.80/1.01  ------ Preprocessing Options
% 2.80/1.01  
% 2.80/1.01  --preprocessing_flag                    true
% 2.80/1.01  --time_out_prep_mult                    0.1
% 2.80/1.01  --splitting_mode                        input
% 2.80/1.01  --splitting_grd                         true
% 2.80/1.01  --splitting_cvd                         false
% 2.80/1.01  --splitting_cvd_svl                     false
% 2.80/1.01  --splitting_nvd                         32
% 2.80/1.01  --sub_typing                            true
% 2.80/1.01  --prep_gs_sim                           true
% 2.80/1.01  --prep_unflatten                        true
% 2.80/1.01  --prep_res_sim                          true
% 2.80/1.01  --prep_upred                            true
% 2.80/1.01  --prep_sem_filter                       exhaustive
% 2.80/1.01  --prep_sem_filter_out                   false
% 2.80/1.01  --pred_elim                             true
% 2.80/1.01  --res_sim_input                         true
% 2.80/1.01  --eq_ax_congr_red                       true
% 2.80/1.01  --pure_diseq_elim                       true
% 2.80/1.01  --brand_transform                       false
% 2.80/1.01  --non_eq_to_eq                          false
% 2.80/1.01  --prep_def_merge                        true
% 2.80/1.01  --prep_def_merge_prop_impl              false
% 2.80/1.01  --prep_def_merge_mbd                    true
% 2.80/1.01  --prep_def_merge_tr_red                 false
% 2.80/1.01  --prep_def_merge_tr_cl                  false
% 2.80/1.01  --smt_preprocessing                     true
% 2.80/1.01  --smt_ac_axioms                         fast
% 2.80/1.01  --preprocessed_out                      false
% 2.80/1.01  --preprocessed_stats                    false
% 2.80/1.01  
% 2.80/1.01  ------ Abstraction refinement Options
% 2.80/1.01  
% 2.80/1.01  --abstr_ref                             []
% 2.80/1.01  --abstr_ref_prep                        false
% 2.80/1.01  --abstr_ref_until_sat                   false
% 2.80/1.01  --abstr_ref_sig_restrict                funpre
% 2.80/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.80/1.01  --abstr_ref_under                       []
% 2.80/1.01  
% 2.80/1.01  ------ SAT Options
% 2.80/1.01  
% 2.80/1.01  --sat_mode                              false
% 2.80/1.01  --sat_fm_restart_options                ""
% 2.80/1.01  --sat_gr_def                            false
% 2.80/1.01  --sat_epr_types                         true
% 2.80/1.01  --sat_non_cyclic_types                  false
% 2.80/1.01  --sat_finite_models                     false
% 2.80/1.01  --sat_fm_lemmas                         false
% 2.80/1.01  --sat_fm_prep                           false
% 2.80/1.01  --sat_fm_uc_incr                        true
% 2.80/1.01  --sat_out_model                         small
% 2.80/1.01  --sat_out_clauses                       false
% 2.80/1.01  
% 2.80/1.01  ------ QBF Options
% 2.80/1.01  
% 2.80/1.01  --qbf_mode                              false
% 2.80/1.01  --qbf_elim_univ                         false
% 2.80/1.01  --qbf_dom_inst                          none
% 2.80/1.01  --qbf_dom_pre_inst                      false
% 2.80/1.01  --qbf_sk_in                             false
% 2.80/1.01  --qbf_pred_elim                         true
% 2.80/1.01  --qbf_split                             512
% 2.80/1.01  
% 2.80/1.01  ------ BMC1 Options
% 2.80/1.01  
% 2.80/1.01  --bmc1_incremental                      false
% 2.80/1.01  --bmc1_axioms                           reachable_all
% 2.80/1.01  --bmc1_min_bound                        0
% 2.80/1.01  --bmc1_max_bound                        -1
% 2.80/1.01  --bmc1_max_bound_default                -1
% 2.80/1.01  --bmc1_symbol_reachability              true
% 2.80/1.01  --bmc1_property_lemmas                  false
% 2.80/1.01  --bmc1_k_induction                      false
% 2.80/1.01  --bmc1_non_equiv_states                 false
% 2.80/1.01  --bmc1_deadlock                         false
% 2.80/1.01  --bmc1_ucm                              false
% 2.80/1.01  --bmc1_add_unsat_core                   none
% 2.80/1.01  --bmc1_unsat_core_children              false
% 2.80/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.80/1.01  --bmc1_out_stat                         full
% 2.80/1.01  --bmc1_ground_init                      false
% 2.80/1.01  --bmc1_pre_inst_next_state              false
% 2.80/1.01  --bmc1_pre_inst_state                   false
% 2.80/1.01  --bmc1_pre_inst_reach_state             false
% 2.80/1.01  --bmc1_out_unsat_core                   false
% 2.80/1.01  --bmc1_aig_witness_out                  false
% 2.80/1.01  --bmc1_verbose                          false
% 2.80/1.01  --bmc1_dump_clauses_tptp                false
% 2.80/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.80/1.01  --bmc1_dump_file                        -
% 2.80/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.80/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.80/1.01  --bmc1_ucm_extend_mode                  1
% 2.80/1.01  --bmc1_ucm_init_mode                    2
% 2.80/1.01  --bmc1_ucm_cone_mode                    none
% 2.80/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.80/1.01  --bmc1_ucm_relax_model                  4
% 2.80/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.80/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.80/1.01  --bmc1_ucm_layered_model                none
% 2.80/1.01  --bmc1_ucm_max_lemma_size               10
% 2.80/1.01  
% 2.80/1.01  ------ AIG Options
% 2.80/1.01  
% 2.80/1.01  --aig_mode                              false
% 2.80/1.01  
% 2.80/1.01  ------ Instantiation Options
% 2.80/1.01  
% 2.80/1.01  --instantiation_flag                    true
% 2.80/1.01  --inst_sos_flag                         false
% 2.80/1.01  --inst_sos_phase                        true
% 2.80/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.80/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.80/1.01  --inst_lit_sel_side                     none
% 2.80/1.01  --inst_solver_per_active                1400
% 2.80/1.01  --inst_solver_calls_frac                1.
% 2.80/1.01  --inst_passive_queue_type               priority_queues
% 2.80/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.80/1.01  --inst_passive_queues_freq              [25;2]
% 2.80/1.01  --inst_dismatching                      true
% 2.80/1.01  --inst_eager_unprocessed_to_passive     true
% 2.80/1.01  --inst_prop_sim_given                   true
% 2.80/1.01  --inst_prop_sim_new                     false
% 2.80/1.01  --inst_subs_new                         false
% 2.80/1.01  --inst_eq_res_simp                      false
% 2.80/1.01  --inst_subs_given                       false
% 2.80/1.01  --inst_orphan_elimination               true
% 2.80/1.01  --inst_learning_loop_flag               true
% 2.80/1.01  --inst_learning_start                   3000
% 2.80/1.01  --inst_learning_factor                  2
% 2.80/1.01  --inst_start_prop_sim_after_learn       3
% 2.80/1.01  --inst_sel_renew                        solver
% 2.80/1.01  --inst_lit_activity_flag                true
% 2.80/1.01  --inst_restr_to_given                   false
% 2.80/1.01  --inst_activity_threshold               500
% 2.80/1.01  --inst_out_proof                        true
% 2.80/1.01  
% 2.80/1.01  ------ Resolution Options
% 2.80/1.01  
% 2.80/1.01  --resolution_flag                       false
% 2.80/1.01  --res_lit_sel                           adaptive
% 2.80/1.01  --res_lit_sel_side                      none
% 2.80/1.01  --res_ordering                          kbo
% 2.80/1.01  --res_to_prop_solver                    active
% 2.80/1.01  --res_prop_simpl_new                    false
% 2.80/1.01  --res_prop_simpl_given                  true
% 2.80/1.01  --res_passive_queue_type                priority_queues
% 2.80/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.80/1.01  --res_passive_queues_freq               [15;5]
% 2.80/1.01  --res_forward_subs                      full
% 2.80/1.01  --res_backward_subs                     full
% 2.80/1.01  --res_forward_subs_resolution           true
% 2.80/1.01  --res_backward_subs_resolution          true
% 2.80/1.01  --res_orphan_elimination                true
% 2.80/1.01  --res_time_limit                        2.
% 2.80/1.01  --res_out_proof                         true
% 2.80/1.01  
% 2.80/1.01  ------ Superposition Options
% 2.80/1.01  
% 2.80/1.01  --superposition_flag                    true
% 2.80/1.01  --sup_passive_queue_type                priority_queues
% 2.80/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.80/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.80/1.01  --demod_completeness_check              fast
% 2.80/1.01  --demod_use_ground                      true
% 2.80/1.01  --sup_to_prop_solver                    passive
% 2.80/1.01  --sup_prop_simpl_new                    true
% 2.80/1.01  --sup_prop_simpl_given                  true
% 2.80/1.01  --sup_fun_splitting                     false
% 2.80/1.01  --sup_smt_interval                      50000
% 2.80/1.01  
% 2.80/1.01  ------ Superposition Simplification Setup
% 2.80/1.01  
% 2.80/1.01  --sup_indices_passive                   []
% 2.80/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.80/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.80/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_full_bw                           [BwDemod]
% 2.80/1.01  --sup_immed_triv                        [TrivRules]
% 2.80/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.80/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_immed_bw_main                     []
% 2.80/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.80/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.80/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.80/1.01  
% 2.80/1.01  ------ Combination Options
% 2.80/1.01  
% 2.80/1.01  --comb_res_mult                         3
% 2.80/1.01  --comb_sup_mult                         2
% 2.80/1.01  --comb_inst_mult                        10
% 2.80/1.01  
% 2.80/1.01  ------ Debug Options
% 2.80/1.01  
% 2.80/1.01  --dbg_backtrace                         false
% 2.80/1.01  --dbg_dump_prop_clauses                 false
% 2.80/1.01  --dbg_dump_prop_clauses_file            -
% 2.80/1.01  --dbg_out_stat                          false
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  ------ Proving...
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  % SZS status Theorem for theBenchmark.p
% 2.80/1.01  
% 2.80/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.80/1.01  
% 2.80/1.01  fof(f2,axiom,(
% 2.80/1.01    v1_xboole_0(k1_xboole_0)),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f52,plain,(
% 2.80/1.01    v1_xboole_0(k1_xboole_0)),
% 2.80/1.01    inference(cnf_transformation,[],[f2])).
% 2.80/1.01  
% 2.80/1.01  fof(f16,axiom,(
% 2.80/1.01    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f36,plain,(
% 2.80/1.01    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.80/1.01    inference(ennf_transformation,[],[f16])).
% 2.80/1.01  
% 2.80/1.01  fof(f37,plain,(
% 2.80/1.01    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.80/1.01    inference(flattening,[],[f36])).
% 2.80/1.01  
% 2.80/1.01  fof(f78,plain,(
% 2.80/1.01    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.80/1.01    inference(cnf_transformation,[],[f37])).
% 2.80/1.01  
% 2.80/1.01  fof(f18,axiom,(
% 2.80/1.01    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f81,plain,(
% 2.80/1.01    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 2.80/1.01    inference(cnf_transformation,[],[f18])).
% 2.80/1.01  
% 2.80/1.01  fof(f85,plain,(
% 2.80/1.01    ( ! [X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.80/1.01    inference(definition_unfolding,[],[f78,f81])).
% 2.80/1.01  
% 2.80/1.01  fof(f3,axiom,(
% 2.80/1.01    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f24,plain,(
% 2.80/1.01    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.80/1.01    inference(ennf_transformation,[],[f3])).
% 2.80/1.01  
% 2.80/1.01  fof(f53,plain,(
% 2.80/1.01    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.80/1.01    inference(cnf_transformation,[],[f24])).
% 2.80/1.01  
% 2.80/1.01  fof(f19,conjecture,(
% 2.80/1.01    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f20,negated_conjecture,(
% 2.80/1.01    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.80/1.01    inference(negated_conjecture,[],[f19])).
% 2.80/1.01  
% 2.80/1.01  fof(f23,plain,(
% 2.80/1.01    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 2.80/1.01    inference(pure_predicate_removal,[],[f20])).
% 2.80/1.01  
% 2.80/1.01  fof(f39,plain,(
% 2.80/1.01    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & v1_relat_1(X2))),
% 2.80/1.01    inference(ennf_transformation,[],[f23])).
% 2.80/1.01  
% 2.80/1.01  fof(f40,plain,(
% 2.80/1.01    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2))),
% 2.80/1.01    inference(flattening,[],[f39])).
% 2.80/1.01  
% 2.80/1.01  fof(f48,plain,(
% 2.80/1.01    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_relat_1(sK3))),
% 2.80/1.01    introduced(choice_axiom,[])).
% 2.80/1.01  
% 2.80/1.01  fof(f49,plain,(
% 2.80/1.01    (~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1) & r2_hidden(sK3,k1_funct_2(sK1,sK2)) & v1_relat_1(sK3)),
% 2.80/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f40,f48])).
% 2.80/1.01  
% 2.80/1.01  fof(f83,plain,(
% 2.80/1.01    r2_hidden(sK3,k1_funct_2(sK1,sK2))),
% 2.80/1.01    inference(cnf_transformation,[],[f49])).
% 2.80/1.01  
% 2.80/1.01  fof(f88,plain,(
% 2.80/1.01    r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2)))),
% 2.80/1.01    inference(definition_unfolding,[],[f83,f81])).
% 2.80/1.01  
% 2.80/1.01  fof(f1,axiom,(
% 2.80/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f41,plain,(
% 2.80/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.80/1.01    inference(nnf_transformation,[],[f1])).
% 2.80/1.01  
% 2.80/1.01  fof(f42,plain,(
% 2.80/1.01    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.80/1.01    inference(rectify,[],[f41])).
% 2.80/1.01  
% 2.80/1.01  fof(f43,plain,(
% 2.80/1.01    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 2.80/1.01    introduced(choice_axiom,[])).
% 2.80/1.01  
% 2.80/1.01  fof(f44,plain,(
% 2.80/1.01    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.80/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f42,f43])).
% 2.80/1.01  
% 2.80/1.01  fof(f50,plain,(
% 2.80/1.01    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 2.80/1.01    inference(cnf_transformation,[],[f44])).
% 2.80/1.01  
% 2.80/1.01  fof(f17,axiom,(
% 2.80/1.01    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f22,plain,(
% 2.80/1.01    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 2.80/1.01    inference(pure_predicate_removal,[],[f17])).
% 2.80/1.01  
% 2.80/1.01  fof(f38,plain,(
% 2.80/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 2.80/1.01    inference(ennf_transformation,[],[f22])).
% 2.80/1.01  
% 2.80/1.01  fof(f80,plain,(
% 2.80/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 2.80/1.01    inference(cnf_transformation,[],[f38])).
% 2.80/1.01  
% 2.80/1.01  fof(f86,plain,(
% 2.80/1.01    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 2.80/1.01    inference(definition_unfolding,[],[f80,f81])).
% 2.80/1.01  
% 2.80/1.01  fof(f5,axiom,(
% 2.80/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f45,plain,(
% 2.80/1.01    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.80/1.01    inference(nnf_transformation,[],[f5])).
% 2.80/1.01  
% 2.80/1.01  fof(f55,plain,(
% 2.80/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.80/1.01    inference(cnf_transformation,[],[f45])).
% 2.80/1.01  
% 2.80/1.01  fof(f7,axiom,(
% 2.80/1.01    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f25,plain,(
% 2.80/1.01    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 2.80/1.01    inference(ennf_transformation,[],[f7])).
% 2.80/1.01  
% 2.80/1.01  fof(f59,plain,(
% 2.80/1.01    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 2.80/1.01    inference(cnf_transformation,[],[f25])).
% 2.80/1.01  
% 2.80/1.01  fof(f8,axiom,(
% 2.80/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f26,plain,(
% 2.80/1.01    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.80/1.01    inference(ennf_transformation,[],[f8])).
% 2.80/1.01  
% 2.80/1.01  fof(f27,plain,(
% 2.80/1.01    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.80/1.01    inference(flattening,[],[f26])).
% 2.80/1.01  
% 2.80/1.01  fof(f61,plain,(
% 2.80/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.80/1.01    inference(cnf_transformation,[],[f27])).
% 2.80/1.01  
% 2.80/1.01  fof(f6,axiom,(
% 2.80/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f57,plain,(
% 2.80/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.80/1.01    inference(cnf_transformation,[],[f6])).
% 2.80/1.01  
% 2.80/1.01  fof(f82,plain,(
% 2.80/1.01    v1_relat_1(sK3)),
% 2.80/1.01    inference(cnf_transformation,[],[f49])).
% 2.80/1.01  
% 2.80/1.01  fof(f79,plain,(
% 2.80/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 2.80/1.01    inference(cnf_transformation,[],[f38])).
% 2.80/1.01  
% 2.80/1.01  fof(f87,plain,(
% 2.80/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 2.80/1.01    inference(definition_unfolding,[],[f79,f81])).
% 2.80/1.01  
% 2.80/1.01  fof(f15,axiom,(
% 2.80/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f34,plain,(
% 2.80/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/1.01    inference(ennf_transformation,[],[f15])).
% 2.80/1.01  
% 2.80/1.01  fof(f35,plain,(
% 2.80/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/1.01    inference(flattening,[],[f34])).
% 2.80/1.01  
% 2.80/1.01  fof(f47,plain,(
% 2.80/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/1.01    inference(nnf_transformation,[],[f35])).
% 2.80/1.01  
% 2.80/1.01  fof(f72,plain,(
% 2.80/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/1.01    inference(cnf_transformation,[],[f47])).
% 2.80/1.01  
% 2.80/1.01  fof(f13,axiom,(
% 2.80/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f31,plain,(
% 2.80/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.80/1.01    inference(ennf_transformation,[],[f13])).
% 2.80/1.01  
% 2.80/1.01  fof(f69,plain,(
% 2.80/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.80/1.01    inference(cnf_transformation,[],[f31])).
% 2.80/1.01  
% 2.80/1.01  fof(f84,plain,(
% 2.80/1.01    ~r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1),
% 2.80/1.01    inference(cnf_transformation,[],[f49])).
% 2.80/1.01  
% 2.80/1.01  fof(f9,axiom,(
% 2.80/1.01    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f28,plain,(
% 2.80/1.01    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.80/1.01    inference(ennf_transformation,[],[f9])).
% 2.80/1.01  
% 2.80/1.01  fof(f29,plain,(
% 2.80/1.01    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.80/1.01    inference(flattening,[],[f28])).
% 2.80/1.01  
% 2.80/1.01  fof(f62,plain,(
% 2.80/1.01    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/1.01    inference(cnf_transformation,[],[f29])).
% 2.80/1.01  
% 2.80/1.01  fof(f4,axiom,(
% 2.80/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f54,plain,(
% 2.80/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.80/1.01    inference(cnf_transformation,[],[f4])).
% 2.80/1.01  
% 2.80/1.01  fof(f10,axiom,(
% 2.80/1.01    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f30,plain,(
% 2.80/1.01    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.80/1.01    inference(ennf_transformation,[],[f10])).
% 2.80/1.01  
% 2.80/1.01  fof(f46,plain,(
% 2.80/1.01    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.80/1.01    inference(nnf_transformation,[],[f30])).
% 2.80/1.01  
% 2.80/1.01  fof(f64,plain,(
% 2.80/1.01    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.80/1.01    inference(cnf_transformation,[],[f46])).
% 2.80/1.01  
% 2.80/1.01  fof(f14,axiom,(
% 2.80/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f32,plain,(
% 2.80/1.01    ! [X0,X1,X2] : (((r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1) | ~r1_tarski(k6_relat_1(X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.80/1.01    inference(ennf_transformation,[],[f14])).
% 2.80/1.01  
% 2.80/1.01  fof(f33,plain,(
% 2.80/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1) | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.80/1.01    inference(flattening,[],[f32])).
% 2.80/1.01  
% 2.80/1.01  fof(f70,plain,(
% 2.80/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.80/1.01    inference(cnf_transformation,[],[f33])).
% 2.80/1.01  
% 2.80/1.01  fof(f11,axiom,(
% 2.80/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f66,plain,(
% 2.80/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 2.80/1.01    inference(cnf_transformation,[],[f11])).
% 2.80/1.01  
% 2.80/1.01  fof(f12,axiom,(
% 2.80/1.01    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.80/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.80/1.01  
% 2.80/1.01  fof(f21,plain,(
% 2.80/1.01    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 2.80/1.01    inference(pure_predicate_removal,[],[f12])).
% 2.80/1.01  
% 2.80/1.01  fof(f68,plain,(
% 2.80/1.01    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 2.80/1.01    inference(cnf_transformation,[],[f21])).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2,plain,
% 2.80/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.80/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1906,plain,
% 2.80/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_28,plain,
% 2.80/1.01      ( ~ v1_xboole_0(X0)
% 2.80/1.01      | v1_xboole_0(X1)
% 2.80/1.01      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
% 2.80/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1890,plain,
% 2.80/1.01      ( v1_xboole_0(X0) != iProver_top
% 2.80/1.01      | v1_xboole_0(X1) = iProver_top
% 2.80/1.01      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3,plain,
% 2.80/1.01      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.80/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1905,plain,
% 2.80/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3307,plain,
% 2.80/1.01      ( k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) = k1_xboole_0
% 2.80/1.01      | v1_xboole_0(X1) != iProver_top
% 2.80/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_1890,c_1905]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_6987,plain,
% 2.80/1.01      ( k5_partfun1(X0,k1_xboole_0,k3_partfun1(k1_xboole_0,X0,k1_xboole_0)) = k1_xboole_0
% 2.80/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_1906,c_3307]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_32,negated_conjecture,
% 2.80/1.01      ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) ),
% 2.80/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1887,plain,
% 2.80/1.01      ( r2_hidden(sK3,k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) = iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1,plain,
% 2.80/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.80/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1907,plain,
% 2.80/1.01      ( r2_hidden(X0,X1) != iProver_top
% 2.80/1.01      | v1_xboole_0(X1) != iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2521,plain,
% 2.80/1.01      ( v1_xboole_0(k5_partfun1(sK1,sK2,k3_partfun1(k1_xboole_0,sK1,sK2))) != iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_1887,c_1907]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3308,plain,
% 2.80/1.01      ( v1_xboole_0(sK1) = iProver_top
% 2.80/1.01      | v1_xboole_0(sK2) != iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_1890,c_2521]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_7346,plain,
% 2.80/1.01      ( k5_partfun1(sK2,k1_xboole_0,k3_partfun1(k1_xboole_0,sK2,k1_xboole_0)) = k1_xboole_0
% 2.80/1.01      | v1_xboole_0(sK1) = iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_6987,c_3308]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_7588,plain,
% 2.80/1.01      ( k5_partfun1(sK2,k1_xboole_0,k3_partfun1(k1_xboole_0,sK2,k1_xboole_0)) = k1_xboole_0
% 2.80/1.01      | sK1 = k1_xboole_0 ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_7346,c_1905]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_111,plain,
% 2.80/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1269,plain,( X0 = X0 ),theory(equality) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3181,plain,
% 2.80/1.01      ( sK1 = sK1 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_1269]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_4474,plain,
% 2.80/1.01      ( ~ v1_xboole_0(sK1) | k1_xboole_0 = sK1 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_4475,plain,
% 2.80/1.01      ( k1_xboole_0 = sK1 | v1_xboole_0(sK1) != iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_4474]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1270,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3183,plain,
% 2.80/1.01      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_1270]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_6068,plain,
% 2.80/1.01      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_3183]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_6069,plain,
% 2.80/1.01      ( sK1 != sK1 | sK1 = k1_xboole_0 | k1_xboole_0 != sK1 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_6068]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_29,plain,
% 2.80/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.01      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 2.80/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1889,plain,
% 2.80/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.80/1.01      | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3251,plain,
% 2.80/1.01      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_1887,c_1889]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_6,plain,
% 2.80/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.80/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1902,plain,
% 2.80/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.80/1.01      | r1_tarski(X0,X1) = iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3630,plain,
% 2.80/1.01      ( r1_tarski(sK3,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_3251,c_1902]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_8,plain,
% 2.80/1.01      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 2.80/1.01      | k1_xboole_0 = X0
% 2.80/1.01      | k1_xboole_0 = X1 ),
% 2.80/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_10,plain,
% 2.80/1.01      ( ~ r1_tarski(X0,X1)
% 2.80/1.01      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 2.80/1.01      | ~ v1_relat_1(X1)
% 2.80/1.01      | ~ v1_relat_1(X0) ),
% 2.80/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1900,plain,
% 2.80/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.80/1.01      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 2.80/1.01      | v1_relat_1(X0) != iProver_top
% 2.80/1.01      | v1_relat_1(X1) != iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_4084,plain,
% 2.80/1.01      ( k1_xboole_0 = X0
% 2.80/1.01      | k1_xboole_0 = X1
% 2.80/1.01      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 2.80/1.01      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 2.80/1.01      | v1_relat_1(X2) != iProver_top
% 2.80/1.01      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_8,c_1900]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_7,plain,
% 2.80/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.80/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_96,plain,
% 2.80/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_6958,plain,
% 2.80/1.01      ( v1_relat_1(X2) != iProver_top
% 2.80/1.01      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 2.80/1.01      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 2.80/1.01      | k1_xboole_0 = X1
% 2.80/1.01      | k1_xboole_0 = X0 ),
% 2.80/1.01      inference(global_propositional_subsumption,
% 2.80/1.01                [status(thm)],
% 2.80/1.01                [c_4084,c_96]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_6959,plain,
% 2.80/1.01      ( k1_xboole_0 = X0
% 2.80/1.01      | k1_xboole_0 = X1
% 2.80/1.01      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 2.80/1.01      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 2.80/1.01      | v1_relat_1(X2) != iProver_top ),
% 2.80/1.01      inference(renaming,[status(thm)],[c_6958]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_6968,plain,
% 2.80/1.01      ( sK1 = k1_xboole_0
% 2.80/1.01      | sK2 = k1_xboole_0
% 2.80/1.01      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.80/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_3630,c_6959]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_33,negated_conjecture,
% 2.80/1.01      ( v1_relat_1(sK3) ),
% 2.80/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_30,plain,
% 2.80/1.01      ( v1_funct_2(X0,X1,X2)
% 2.80/1.01      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 2.80/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_27,plain,
% 2.80/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.80/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.80/1.01      | k1_xboole_0 = X2 ),
% 2.80/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_477,plain,
% 2.80/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.01      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.80/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.80/1.01      | k1_xboole_0 = X2 ),
% 2.80/1.01      inference(resolution,[status(thm)],[c_30,c_27]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_481,plain,
% 2.80/1.01      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 2.80/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.80/1.01      | k1_xboole_0 = X2 ),
% 2.80/1.01      inference(global_propositional_subsumption,
% 2.80/1.01                [status(thm)],
% 2.80/1.01                [c_477,c_29]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1885,plain,
% 2.80/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 2.80/1.01      | k1_xboole_0 = X1
% 2.80/1.01      | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_481]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3291,plain,
% 2.80/1.01      ( k1_relset_1(sK1,sK2,sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_1887,c_1885]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_19,plain,
% 2.80/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.80/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1893,plain,
% 2.80/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.80/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3633,plain,
% 2.80/1.01      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_3251,c_1893]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3758,plain,
% 2.80/1.01      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_3291,c_3633]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_31,negated_conjecture,
% 2.80/1.01      ( ~ r1_tarski(k2_relat_1(sK3),sK2) | k1_relat_1(sK3) != sK1 ),
% 2.80/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1888,plain,
% 2.80/1.01      ( k1_relat_1(sK3) != sK1
% 2.80/1.01      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3846,plain,
% 2.80/1.01      ( sK2 = k1_xboole_0
% 2.80/1.01      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_3758,c_1888]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3895,plain,
% 2.80/1.01      ( ~ r1_tarski(k2_relat_1(sK3),sK2) | sK2 = k1_xboole_0 ),
% 2.80/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_3846]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_13,plain,
% 2.80/1.01      ( ~ v1_relat_1(X0)
% 2.80/1.01      | k1_relat_1(X0) != k1_xboole_0
% 2.80/1.01      | k1_xboole_0 = X0 ),
% 2.80/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1897,plain,
% 2.80/1.01      ( k1_relat_1(X0) != k1_xboole_0
% 2.80/1.01      | k1_xboole_0 = X0
% 2.80/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3844,plain,
% 2.80/1.01      ( sK1 != k1_xboole_0
% 2.80/1.01      | sK2 = k1_xboole_0
% 2.80/1.01      | sK3 = k1_xboole_0
% 2.80/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_3758,c_1897]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_34,plain,
% 2.80/1.01      ( v1_relat_1(sK3) = iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1273,plain,
% 2.80/1.01      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.80/1.01      theory(equality) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2202,plain,
% 2.80/1.01      ( ~ r1_tarski(X0,X1)
% 2.80/1.01      | r1_tarski(k2_relat_1(sK3),sK2)
% 2.80/1.01      | k2_relat_1(sK3) != X0
% 2.80/1.01      | sK2 != X1 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_1273]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2404,plain,
% 2.80/1.01      ( ~ r1_tarski(X0,sK2)
% 2.80/1.01      | r1_tarski(k2_relat_1(sK3),sK2)
% 2.80/1.01      | k2_relat_1(sK3) != X0
% 2.80/1.01      | sK2 != sK2 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_2202]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2406,plain,
% 2.80/1.01      ( k2_relat_1(sK3) != X0
% 2.80/1.01      | sK2 != sK2
% 2.80/1.01      | r1_tarski(X0,sK2) != iProver_top
% 2.80/1.01      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_2404]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2408,plain,
% 2.80/1.01      ( k2_relat_1(sK3) != k1_xboole_0
% 2.80/1.01      | sK2 != sK2
% 2.80/1.01      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.80/1.01      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_2406]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2405,plain,
% 2.80/1.01      ( sK2 = sK2 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_1269]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_4,plain,
% 2.80/1.01      ( r1_tarski(k1_xboole_0,X0) ),
% 2.80/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2918,plain,
% 2.80/1.01      ( r1_tarski(k1_xboole_0,sK2) ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2921,plain,
% 2.80/1.01      ( r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_2918]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_15,plain,
% 2.80/1.01      ( ~ v1_relat_1(X0)
% 2.80/1.01      | k1_relat_1(X0) != k1_xboole_0
% 2.80/1.01      | k2_relat_1(X0) = k1_xboole_0 ),
% 2.80/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1895,plain,
% 2.80/1.01      ( k1_relat_1(X0) != k1_xboole_0
% 2.80/1.01      | k2_relat_1(X0) = k1_xboole_0
% 2.80/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3843,plain,
% 2.80/1.01      ( k2_relat_1(sK3) = k1_xboole_0
% 2.80/1.01      | sK1 != k1_xboole_0
% 2.80/1.01      | sK2 = k1_xboole_0
% 2.80/1.01      | v1_relat_1(sK3) != iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_3758,c_1895]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_4619,plain,
% 2.80/1.01      ( sK1 != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 2.80/1.01      inference(global_propositional_subsumption,
% 2.80/1.01                [status(thm)],
% 2.80/1.01                [c_3844,c_34,c_2408,c_2405,c_2921,c_3843,c_3846]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_6982,plain,
% 2.80/1.01      ( r1_tarski(k2_relat_1(sK3),sK2)
% 2.80/1.01      | ~ v1_relat_1(sK3)
% 2.80/1.01      | sK1 = k1_xboole_0
% 2.80/1.01      | sK2 = k1_xboole_0 ),
% 2.80/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_6968]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_7602,plain,
% 2.80/1.01      ( sK2 = k1_xboole_0 ),
% 2.80/1.01      inference(global_propositional_subsumption,
% 2.80/1.01                [status(thm)],
% 2.80/1.01                [c_6968,c_33,c_3895,c_4619,c_6982]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_7610,plain,
% 2.80/1.01      ( v1_xboole_0(sK1) = iProver_top
% 2.80/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.80/1.01      inference(demodulation,[status(thm)],[c_7602,c_3308]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_7895,plain,
% 2.80/1.01      ( sK1 = k1_xboole_0 ),
% 2.80/1.01      inference(global_propositional_subsumption,
% 2.80/1.01                [status(thm)],
% 2.80/1.01                [c_7588,c_111,c_3181,c_4475,c_6069,c_7610]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_21,plain,
% 2.80/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.80/1.01      | ~ r1_tarski(k6_relat_1(X1),X0)
% 2.80/1.01      | k1_relset_1(X1,X2,X0) = X1 ),
% 2.80/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_1891,plain,
% 2.80/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 2.80/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.80/1.01      | r1_tarski(k6_relat_1(X0),X2) != iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3632,plain,
% 2.80/1.01      ( k1_relset_1(sK1,sK2,sK3) = sK1
% 2.80/1.01      | r1_tarski(k6_relat_1(sK1),sK3) != iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_3251,c_1891]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3636,plain,
% 2.80/1.01      ( k1_relat_1(sK3) = sK1
% 2.80/1.01      | r1_tarski(k6_relat_1(sK1),sK3) != iProver_top ),
% 2.80/1.01      inference(demodulation,[status(thm)],[c_3632,c_3633]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_7902,plain,
% 2.80/1.01      ( k1_relat_1(sK3) = k1_xboole_0
% 2.80/1.01      | r1_tarski(k6_relat_1(k1_xboole_0),sK3) != iProver_top ),
% 2.80/1.01      inference(demodulation,[status(thm)],[c_7895,c_3636]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_17,plain,
% 2.80/1.01      ( k1_relat_1(k6_relat_1(X0)) = X0 ),
% 2.80/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2775,plain,
% 2.80/1.01      ( k6_relat_1(X0) = k1_xboole_0
% 2.80/1.01      | k1_xboole_0 != X0
% 2.80/1.01      | v1_relat_1(k6_relat_1(X0)) != iProver_top ),
% 2.80/1.01      inference(superposition,[status(thm)],[c_17,c_1897]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_18,plain,
% 2.80/1.01      ( v1_relat_1(k6_relat_1(X0)) ),
% 2.80/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_71,plain,
% 2.80/1.01      ( v1_relat_1(k6_relat_1(X0)) = iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3041,plain,
% 2.80/1.01      ( k1_xboole_0 != X0 | k6_relat_1(X0) = k1_xboole_0 ),
% 2.80/1.01      inference(global_propositional_subsumption,
% 2.80/1.01                [status(thm)],
% 2.80/1.01                [c_2775,c_71]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3042,plain,
% 2.80/1.01      ( k6_relat_1(X0) = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.80/1.01      inference(renaming,[status(thm)],[c_3041]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_3046,plain,
% 2.80/1.01      ( k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.80/1.01      inference(equality_resolution,[status(thm)],[c_3042]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_7906,plain,
% 2.80/1.01      ( k1_relat_1(sK3) = k1_xboole_0
% 2.80/1.01      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 2.80/1.01      inference(light_normalisation,[status(thm)],[c_7902,c_3046]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_7616,plain,
% 2.80/1.01      ( k1_relat_1(sK3) != sK1
% 2.80/1.01      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 2.80/1.01      inference(demodulation,[status(thm)],[c_7602,c_1888]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_7900,plain,
% 2.80/1.01      ( k1_relat_1(sK3) != k1_xboole_0
% 2.80/1.01      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 2.80/1.01      inference(demodulation,[status(thm)],[c_7895,c_7616]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_7921,plain,
% 2.80/1.01      ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 2.80/1.01      | k1_relat_1(sK3) != k1_xboole_0 ),
% 2.80/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_7900]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_5421,plain,
% 2.80/1.01      ( ~ r1_tarski(X0,X1)
% 2.80/1.01      | r1_tarski(k2_relat_1(sK3),X2)
% 2.80/1.01      | X2 != X1
% 2.80/1.01      | k2_relat_1(sK3) != X0 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_1273]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_5423,plain,
% 2.80/1.01      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 2.80/1.01      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.80/1.01      | k2_relat_1(sK3) != k1_xboole_0
% 2.80/1.01      | k1_xboole_0 != k1_xboole_0 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_5421]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2786,plain,
% 2.80/1.01      ( r1_tarski(k1_xboole_0,sK3) ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2789,plain,
% 2.80/1.01      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 2.80/1.01      inference(predicate_to_equality,[status(thm)],[c_2786]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_2126,plain,
% 2.80/1.01      ( ~ v1_relat_1(sK3)
% 2.80/1.01      | k1_relat_1(sK3) != k1_xboole_0
% 2.80/1.01      | k2_relat_1(sK3) = k1_xboole_0 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_109,plain,
% 2.80/1.01      ( ~ v1_xboole_0(k1_xboole_0) | k1_xboole_0 = k1_xboole_0 ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(c_106,plain,
% 2.80/1.01      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.80/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.80/1.01  
% 2.80/1.01  cnf(contradiction,plain,
% 2.80/1.01      ( $false ),
% 2.80/1.01      inference(minisat,
% 2.80/1.01                [status(thm)],
% 2.80/1.01                [c_7906,c_7921,c_5423,c_2789,c_2126,c_2,c_109,c_106,c_33]) ).
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.80/1.01  
% 2.80/1.01  ------                               Statistics
% 2.80/1.01  
% 2.80/1.01  ------ General
% 2.80/1.01  
% 2.80/1.01  abstr_ref_over_cycles:                  0
% 2.80/1.01  abstr_ref_under_cycles:                 0
% 2.80/1.01  gc_basic_clause_elim:                   0
% 2.80/1.01  forced_gc_time:                         0
% 2.80/1.01  parsing_time:                           0.011
% 2.80/1.01  unif_index_cands_time:                  0.
% 2.80/1.01  unif_index_add_time:                    0.
% 2.80/1.01  orderings_time:                         0.
% 2.80/1.01  out_proof_time:                         0.009
% 2.80/1.01  total_time:                             0.231
% 2.80/1.01  num_of_symbols:                         51
% 2.80/1.01  num_of_terms:                           6723
% 2.80/1.01  
% 2.80/1.01  ------ Preprocessing
% 2.80/1.01  
% 2.80/1.01  num_of_splits:                          0
% 2.80/1.01  num_of_split_atoms:                     0
% 2.80/1.01  num_of_reused_defs:                     0
% 2.80/1.01  num_eq_ax_congr_red:                    27
% 2.80/1.01  num_of_sem_filtered_clauses:            1
% 2.80/1.01  num_of_subtypes:                        0
% 2.80/1.01  monotx_restored_types:                  0
% 2.80/1.01  sat_num_of_epr_types:                   0
% 2.80/1.01  sat_num_of_non_cyclic_types:            0
% 2.80/1.01  sat_guarded_non_collapsed_types:        0
% 2.80/1.01  num_pure_diseq_elim:                    0
% 2.80/1.01  simp_replaced_by:                       0
% 2.80/1.01  res_preprocessed:                       151
% 2.80/1.01  prep_upred:                             0
% 2.80/1.01  prep_unflattend:                        76
% 2.80/1.01  smt_new_axioms:                         0
% 2.80/1.01  pred_elim_cands:                        5
% 2.80/1.01  pred_elim:                              1
% 2.80/1.01  pred_elim_cl:                           4
% 2.80/1.01  pred_elim_cycles:                       6
% 2.80/1.01  merged_defs:                            8
% 2.80/1.01  merged_defs_ncl:                        0
% 2.80/1.01  bin_hyper_res:                          8
% 2.80/1.01  prep_cycles:                            4
% 2.80/1.01  pred_elim_time:                         0.012
% 2.80/1.01  splitting_time:                         0.
% 2.80/1.01  sem_filter_time:                        0.
% 2.80/1.01  monotx_time:                            0.001
% 2.80/1.01  subtype_inf_time:                       0.
% 2.80/1.01  
% 2.80/1.01  ------ Problem properties
% 2.80/1.01  
% 2.80/1.01  clauses:                                30
% 2.80/1.01  conjectures:                            3
% 2.80/1.01  epr:                                    5
% 2.80/1.01  horn:                                   24
% 2.80/1.01  ground:                                 4
% 2.80/1.01  unary:                                  8
% 2.80/1.01  binary:                                 9
% 2.80/1.01  lits:                                   67
% 2.80/1.01  lits_eq:                                25
% 2.80/1.01  fd_pure:                                0
% 2.80/1.01  fd_pseudo:                              0
% 2.80/1.01  fd_cond:                                4
% 2.80/1.01  fd_pseudo_cond:                         0
% 2.80/1.01  ac_symbols:                             0
% 2.80/1.01  
% 2.80/1.01  ------ Propositional Solver
% 2.80/1.01  
% 2.80/1.01  prop_solver_calls:                      28
% 2.80/1.01  prop_fast_solver_calls:                 1183
% 2.80/1.01  smt_solver_calls:                       0
% 2.80/1.01  smt_fast_solver_calls:                  0
% 2.80/1.01  prop_num_of_clauses:                    2441
% 2.80/1.01  prop_preprocess_simplified:             8200
% 2.80/1.01  prop_fo_subsumed:                       27
% 2.80/1.01  prop_solver_time:                       0.
% 2.80/1.01  smt_solver_time:                        0.
% 2.80/1.01  smt_fast_solver_time:                   0.
% 2.80/1.01  prop_fast_solver_time:                  0.
% 2.80/1.01  prop_unsat_core_time:                   0.
% 2.80/1.01  
% 2.80/1.01  ------ QBF
% 2.80/1.01  
% 2.80/1.01  qbf_q_res:                              0
% 2.80/1.01  qbf_num_tautologies:                    0
% 2.80/1.01  qbf_prep_cycles:                        0
% 2.80/1.01  
% 2.80/1.01  ------ BMC1
% 2.80/1.01  
% 2.80/1.01  bmc1_current_bound:                     -1
% 2.80/1.01  bmc1_last_solved_bound:                 -1
% 2.80/1.01  bmc1_unsat_core_size:                   -1
% 2.80/1.01  bmc1_unsat_core_parents_size:           -1
% 2.80/1.01  bmc1_merge_next_fun:                    0
% 2.80/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.80/1.01  
% 2.80/1.01  ------ Instantiation
% 2.80/1.01  
% 2.80/1.01  inst_num_of_clauses:                    781
% 2.80/1.01  inst_num_in_passive:                    362
% 2.80/1.01  inst_num_in_active:                     383
% 2.80/1.01  inst_num_in_unprocessed:                36
% 2.80/1.01  inst_num_of_loops:                      480
% 2.80/1.01  inst_num_of_learning_restarts:          0
% 2.80/1.01  inst_num_moves_active_passive:          95
% 2.80/1.01  inst_lit_activity:                      0
% 2.80/1.01  inst_lit_activity_moves:                0
% 2.80/1.01  inst_num_tautologies:                   0
% 2.80/1.01  inst_num_prop_implied:                  0
% 2.80/1.01  inst_num_existing_simplified:           0
% 2.80/1.01  inst_num_eq_res_simplified:             0
% 2.80/1.01  inst_num_child_elim:                    0
% 2.80/1.01  inst_num_of_dismatching_blockings:      125
% 2.80/1.01  inst_num_of_non_proper_insts:           557
% 2.80/1.01  inst_num_of_duplicates:                 0
% 2.80/1.01  inst_inst_num_from_inst_to_res:         0
% 2.80/1.01  inst_dismatching_checking_time:         0.
% 2.80/1.01  
% 2.80/1.01  ------ Resolution
% 2.80/1.01  
% 2.80/1.01  res_num_of_clauses:                     0
% 2.80/1.01  res_num_in_passive:                     0
% 2.80/1.01  res_num_in_active:                      0
% 2.80/1.01  res_num_of_loops:                       155
% 2.80/1.01  res_forward_subset_subsumed:            25
% 2.80/1.01  res_backward_subset_subsumed:           0
% 2.80/1.01  res_forward_subsumed:                   0
% 2.80/1.01  res_backward_subsumed:                  0
% 2.80/1.01  res_forward_subsumption_resolution:     2
% 2.80/1.01  res_backward_subsumption_resolution:    0
% 2.80/1.01  res_clause_to_clause_subsumption:       480
% 2.80/1.01  res_orphan_elimination:                 0
% 2.80/1.01  res_tautology_del:                      54
% 2.80/1.01  res_num_eq_res_simplified:              0
% 2.80/1.01  res_num_sel_changes:                    0
% 2.80/1.01  res_moves_from_active_to_pass:          0
% 2.80/1.01  
% 2.80/1.01  ------ Superposition
% 2.80/1.01  
% 2.80/1.01  sup_time_total:                         0.
% 2.80/1.01  sup_time_generating:                    0.
% 2.80/1.01  sup_time_sim_full:                      0.
% 2.80/1.01  sup_time_sim_immed:                     0.
% 2.80/1.01  
% 2.80/1.01  sup_num_of_clauses:                     125
% 2.80/1.01  sup_num_in_active:                      65
% 2.80/1.01  sup_num_in_passive:                     60
% 2.80/1.01  sup_num_of_loops:                       95
% 2.80/1.01  sup_fw_superposition:                   82
% 2.80/1.01  sup_bw_superposition:                   92
% 2.80/1.01  sup_immediate_simplified:               32
% 2.80/1.01  sup_given_eliminated:                   0
% 2.80/1.01  comparisons_done:                       0
% 2.80/1.01  comparisons_avoided:                    9
% 2.80/1.01  
% 2.80/1.01  ------ Simplifications
% 2.80/1.01  
% 2.80/1.01  
% 2.80/1.01  sim_fw_subset_subsumed:                 8
% 2.80/1.01  sim_bw_subset_subsumed:                 16
% 2.80/1.01  sim_fw_subsumed:                        18
% 2.80/1.01  sim_bw_subsumed:                        0
% 2.80/1.01  sim_fw_subsumption_res:                 5
% 2.80/1.01  sim_bw_subsumption_res:                 0
% 2.80/1.01  sim_tautology_del:                      12
% 2.80/1.01  sim_eq_tautology_del:                   12
% 2.80/1.01  sim_eq_res_simp:                        0
% 2.80/1.01  sim_fw_demodulated:                     4
% 2.80/1.01  sim_bw_demodulated:                     19
% 2.80/1.01  sim_light_normalised:                   13
% 2.80/1.01  sim_joinable_taut:                      0
% 2.80/1.01  sim_joinable_simp:                      0
% 2.80/1.01  sim_ac_normalised:                      0
% 2.80/1.01  sim_smt_subsumption:                    0
% 2.80/1.01  
%------------------------------------------------------------------------------
