%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:57 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :  194 (1521 expanded)
%              Number of clauses        :  107 ( 453 expanded)
%              Number of leaves         :   28 ( 307 expanded)
%              Depth                    :   21
%              Number of atoms          :  520 (4926 expanded)
%              Number of equality atoms :  261 (1941 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   13 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f40,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f57,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X2,k1_funct_2(X0,X1))
     => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1) )
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f19,axiom,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f90,f92])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k1_funct_2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) ) ),
    inference(definition_unfolding,[],[f91,f92])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(X2,k1_funct_2(X0,X1))
       => ( r1_tarski(k2_relat_1(X2),X1)
          & k1_relat_1(X2) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f23,plain,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r2_hidden(X2,k1_funct_2(X0,X1))
         => ( r1_tarski(k2_relat_1(X2),X1)
            & k1_relat_1(X2) = X0 ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_tarski(k2_relat_1(X2),X1)
        | k1_relat_1(X2) != X0 )
      & r2_hidden(X2,k1_funct_2(X0,X1))
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f54,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_tarski(k2_relat_1(X2),X1)
          | k1_relat_1(X2) != X0 )
        & r2_hidden(X2,k1_funct_2(X0,X1))
        & v1_relat_1(X2) )
   => ( ( ~ r1_tarski(k2_relat_1(sK5),sK4)
        | k1_relat_1(sK5) != sK3 )
      & r2_hidden(sK5,k1_funct_2(sK3,sK4))
      & v1_relat_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ( ~ r1_tarski(k2_relat_1(sK5),sK4)
      | k1_relat_1(sK5) != sK3 )
    & r2_hidden(sK5,k1_funct_2(sK3,sK4))
    & v1_relat_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f54])).

fof(f94,plain,(
    r2_hidden(sK5,k1_funct_2(sK3,sK4)) ),
    inference(cnf_transformation,[],[f55])).

fof(f99,plain,(
    r2_hidden(sK5,k5_partfun1(sK3,sK4,k3_partfun1(k1_xboole_0,sK3,sK4))) ),
    inference(definition_unfolding,[],[f94,f92])).

fof(f56,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f55])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f95,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),sK4)
    | k1_relat_1(sK5) != sK3 ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f80,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( ~ ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
            & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
        & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0 )
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f10,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f100,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f70])).

fof(f3,axiom,(
    ? [X0] : v1_xboole_0(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,
    ( ? [X0] : v1_xboole_0(X0)
   => v1_xboole_0(sK1) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    v1_xboole_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f43])).

fof(f59,plain,(
    v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f45])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => v1_xboole_0(k1_funct_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k1_funct_2(X0,X1))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f96,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f89,f92])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1350,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3986,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1350])).

cnf(c_6982,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_3986])).

cnf(c_6983,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_6982])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_2078,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_35,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_841,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_35,c_32])).

cnf(c_34,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_536,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_34,c_32])).

cnf(c_540,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_536,c_35])).

cnf(c_845,plain,
    ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_841,c_35,c_536])).

cnf(c_2053,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_845])).

cnf(c_3307,plain,
    ( k1_relset_1(X0,X1,sK0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) = X0
    | k1_xboole_0 = X1
    | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2078,c_2053])).

cnf(c_37,negated_conjecture,
    ( r2_hidden(sK5,k5_partfun1(sK3,sK4,k3_partfun1(k1_xboole_0,sK3,sK4))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_2055,plain,
    ( r2_hidden(sK5,k5_partfun1(sK3,sK4,k3_partfun1(k1_xboole_0,sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2077,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3119,plain,
    ( v1_xboole_0(k5_partfun1(sK3,sK4,k3_partfun1(k1_xboole_0,sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2055,c_2077])).

cnf(c_6569,plain,
    ( k1_relset_1(sK3,sK4,sK0(k5_partfun1(sK3,sK4,k3_partfun1(k1_xboole_0,sK3,sK4)))) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3307,c_3119])).

cnf(c_38,negated_conjecture,
    ( v1_relat_1(sK5) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_3308,plain,
    ( k1_relset_1(sK3,sK4,sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2055,c_2053])).

cnf(c_2057,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4024,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2055,c_2057])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2059,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4290,plain,
    ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4024,c_2059])).

cnf(c_4384,plain,
    ( k1_relat_1(sK5) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3308,c_4290])).

cnf(c_36,negated_conjecture,
    ( ~ r1_tarski(k2_relat_1(sK5),sK4)
    | k1_relat_1(sK5) != sK3 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_2056,plain,
    ( k1_relat_1(sK5) != sK3
    | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_4394,plain,
    ( sK4 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4384,c_2056])).

cnf(c_4408,plain,
    ( ~ r1_tarski(k2_relat_1(sK5),sK4)
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4394])).

cnf(c_25,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_2060,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4393,plain,
    ( k2_relat_1(sK5) = k1_xboole_0
    | sK3 != k1_xboole_0
    | sK4 = k1_xboole_0
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4384,c_2060])).

cnf(c_39,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_1353,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2363,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK5),sK4)
    | k2_relat_1(sK5) != X0
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_1353])).

cnf(c_2499,plain,
    ( ~ r1_tarski(X0,sK4)
    | r1_tarski(k2_relat_1(sK5),sK4)
    | k2_relat_1(sK5) != X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2363])).

cnf(c_2501,plain,
    ( k2_relat_1(sK5) != X0
    | sK4 != sK4
    | r1_tarski(X0,sK4) != iProver_top
    | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2499])).

cnf(c_2503,plain,
    ( k2_relat_1(sK5) != k1_xboole_0
    | sK4 != sK4
    | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
    | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2501])).

cnf(c_1349,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2500,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_9,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2771,plain,
    ( r1_tarski(k1_xboole_0,sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2774,plain,
    ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2771])).

cnf(c_4541,plain,
    ( sK4 = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4393,c_39,c_2503,c_2500,c_2774,c_4394])).

cnf(c_4542,plain,
    ( sK3 != k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4541])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2065,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4289,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4024,c_2065])).

cnf(c_18,plain,
    ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2063,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4725,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_2063])).

cnf(c_17,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_84,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6593,plain,
    ( v1_relat_1(X2) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4725,c_84])).

cnf(c_6594,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
    | r1_tarski(k2_relat_1(X2),X1) = iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6593])).

cnf(c_6603,plain,
    ( sK3 = k1_xboole_0
    | sK4 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4289,c_6594])).

cnf(c_6619,plain,
    ( r1_tarski(k2_relat_1(sK5),sK4)
    | ~ v1_relat_1(sK5)
    | sK3 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6603])).

cnf(c_6792,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6569,c_38,c_4408,c_4542,c_6619])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2071,plain,
    ( k4_xboole_0(X0,X1) = k1_xboole_0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4382,plain,
    ( k4_xboole_0(sK5,k2_zfmisc_1(sK3,sK4)) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4289,c_2071])).

cnf(c_6801,plain,
    ( k4_xboole_0(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6792,c_4382])).

cnf(c_12,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_3,plain,
    ( v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2075,plain,
    ( v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2076,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2669,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2075,c_2076])).

cnf(c_2800,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2669,c_2075])).

cnf(c_5,plain,
    ( r1_xboole_0(X0,X1)
    | r2_hidden(sK2(X0,X1),X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2073,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3378,plain,
    ( r1_xboole_0(X0,X1) = iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2073,c_2077])).

cnf(c_11,plain,
    ( ~ r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2067,plain,
    ( k4_xboole_0(X0,X1) = X0
    | r1_xboole_0(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3704,plain,
    ( k4_xboole_0(X0,X1) = X0
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3378,c_2067])).

cnf(c_3774,plain,
    ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[status(thm)],[c_2800,c_3704])).

cnf(c_6831,plain,
    ( sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6801,c_12,c_3774])).

cnf(c_6808,plain,
    ( k1_relat_1(sK5) != sK3
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6792,c_2056])).

cnf(c_6835,plain,
    ( k1_relat_1(k1_xboole_0) != sK3
    | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6831,c_6808])).

cnf(c_22,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_23,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_6842,plain,
    ( sK3 != k1_xboole_0
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6835,c_22,c_23])).

cnf(c_1351,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5728,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK4)
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_1351])).

cnf(c_5730,plain,
    ( v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5728])).

cnf(c_33,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_2058,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4260,plain,
    ( v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2058,c_3119])).

cnf(c_4286,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4260])).

cnf(c_3863,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1349])).

cnf(c_3845,plain,
    ( ~ v1_xboole_0(sK3)
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2680,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK0(X0),X0)
    | ~ r2_hidden(sK0(X0),X1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2682,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2680])).

cnf(c_123,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_106,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_101,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_103,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_102,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_10,plain,
    ( r1_xboole_0(X0,X1)
    | k4_xboole_0(X0,X1) != X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_99,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6983,c_6842,c_6792,c_5730,c_4286,c_3863,c_3845,c_2682,c_123,c_106,c_103,c_102,c_99])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:01:33 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.17/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.17/0.98  
% 3.17/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.17/0.98  
% 3.17/0.98  ------  iProver source info
% 3.17/0.98  
% 3.17/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.17/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.17/0.98  git: non_committed_changes: false
% 3.17/0.98  git: last_make_outside_of_git: false
% 3.17/0.98  
% 3.17/0.98  ------ 
% 3.17/0.98  
% 3.17/0.98  ------ Input Options
% 3.17/0.98  
% 3.17/0.98  --out_options                           all
% 3.17/0.98  --tptp_safe_out                         true
% 3.17/0.98  --problem_path                          ""
% 3.17/0.98  --include_path                          ""
% 3.17/0.98  --clausifier                            res/vclausify_rel
% 3.17/0.98  --clausifier_options                    --mode clausify
% 3.17/0.98  --stdin                                 false
% 3.17/0.98  --stats_out                             all
% 3.17/0.98  
% 3.17/0.98  ------ General Options
% 3.17/0.98  
% 3.17/0.98  --fof                                   false
% 3.17/0.98  --time_out_real                         305.
% 3.17/0.98  --time_out_virtual                      -1.
% 3.17/0.98  --symbol_type_check                     false
% 3.17/0.98  --clausify_out                          false
% 3.17/0.98  --sig_cnt_out                           false
% 3.17/0.98  --trig_cnt_out                          false
% 3.17/0.98  --trig_cnt_out_tolerance                1.
% 3.17/0.98  --trig_cnt_out_sk_spl                   false
% 3.17/0.98  --abstr_cl_out                          false
% 3.17/0.98  
% 3.17/0.98  ------ Global Options
% 3.17/0.98  
% 3.17/0.98  --schedule                              default
% 3.17/0.98  --add_important_lit                     false
% 3.17/0.98  --prop_solver_per_cl                    1000
% 3.17/0.98  --min_unsat_core                        false
% 3.17/0.98  --soft_assumptions                      false
% 3.17/0.98  --soft_lemma_size                       3
% 3.17/0.98  --prop_impl_unit_size                   0
% 3.17/0.98  --prop_impl_unit                        []
% 3.17/0.98  --share_sel_clauses                     true
% 3.17/0.98  --reset_solvers                         false
% 3.17/0.98  --bc_imp_inh                            [conj_cone]
% 3.17/0.98  --conj_cone_tolerance                   3.
% 3.17/0.98  --extra_neg_conj                        none
% 3.17/0.98  --large_theory_mode                     true
% 3.17/0.98  --prolific_symb_bound                   200
% 3.17/0.98  --lt_threshold                          2000
% 3.17/0.98  --clause_weak_htbl                      true
% 3.17/0.98  --gc_record_bc_elim                     false
% 3.17/0.98  
% 3.17/0.98  ------ Preprocessing Options
% 3.17/0.98  
% 3.17/0.98  --preprocessing_flag                    true
% 3.17/0.98  --time_out_prep_mult                    0.1
% 3.17/0.98  --splitting_mode                        input
% 3.17/0.98  --splitting_grd                         true
% 3.17/0.98  --splitting_cvd                         false
% 3.17/0.98  --splitting_cvd_svl                     false
% 3.17/0.98  --splitting_nvd                         32
% 3.17/0.98  --sub_typing                            true
% 3.17/0.98  --prep_gs_sim                           true
% 3.17/0.98  --prep_unflatten                        true
% 3.17/0.98  --prep_res_sim                          true
% 3.17/0.98  --prep_upred                            true
% 3.17/0.98  --prep_sem_filter                       exhaustive
% 3.17/0.98  --prep_sem_filter_out                   false
% 3.17/0.98  --pred_elim                             true
% 3.17/0.98  --res_sim_input                         true
% 3.17/0.98  --eq_ax_congr_red                       true
% 3.17/0.98  --pure_diseq_elim                       true
% 3.17/0.98  --brand_transform                       false
% 3.17/0.98  --non_eq_to_eq                          false
% 3.17/0.98  --prep_def_merge                        true
% 3.17/0.98  --prep_def_merge_prop_impl              false
% 3.17/0.98  --prep_def_merge_mbd                    true
% 3.17/0.98  --prep_def_merge_tr_red                 false
% 3.17/0.98  --prep_def_merge_tr_cl                  false
% 3.17/0.98  --smt_preprocessing                     true
% 3.17/0.98  --smt_ac_axioms                         fast
% 3.17/0.98  --preprocessed_out                      false
% 3.17/0.98  --preprocessed_stats                    false
% 3.17/0.98  
% 3.17/0.98  ------ Abstraction refinement Options
% 3.17/0.98  
% 3.17/0.98  --abstr_ref                             []
% 3.17/0.98  --abstr_ref_prep                        false
% 3.17/0.98  --abstr_ref_until_sat                   false
% 3.17/0.98  --abstr_ref_sig_restrict                funpre
% 3.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/0.98  --abstr_ref_under                       []
% 3.17/0.98  
% 3.17/0.98  ------ SAT Options
% 3.17/0.98  
% 3.17/0.98  --sat_mode                              false
% 3.17/0.98  --sat_fm_restart_options                ""
% 3.17/0.98  --sat_gr_def                            false
% 3.17/0.98  --sat_epr_types                         true
% 3.17/0.98  --sat_non_cyclic_types                  false
% 3.17/0.98  --sat_finite_models                     false
% 3.17/0.98  --sat_fm_lemmas                         false
% 3.17/0.98  --sat_fm_prep                           false
% 3.17/0.98  --sat_fm_uc_incr                        true
% 3.17/0.98  --sat_out_model                         small
% 3.17/0.98  --sat_out_clauses                       false
% 3.17/0.98  
% 3.17/0.98  ------ QBF Options
% 3.17/0.98  
% 3.17/0.98  --qbf_mode                              false
% 3.17/0.98  --qbf_elim_univ                         false
% 3.17/0.98  --qbf_dom_inst                          none
% 3.17/0.98  --qbf_dom_pre_inst                      false
% 3.17/0.98  --qbf_sk_in                             false
% 3.17/0.98  --qbf_pred_elim                         true
% 3.17/0.98  --qbf_split                             512
% 3.17/0.98  
% 3.17/0.98  ------ BMC1 Options
% 3.17/0.98  
% 3.17/0.98  --bmc1_incremental                      false
% 3.17/0.98  --bmc1_axioms                           reachable_all
% 3.17/0.98  --bmc1_min_bound                        0
% 3.17/0.98  --bmc1_max_bound                        -1
% 3.17/0.98  --bmc1_max_bound_default                -1
% 3.17/0.98  --bmc1_symbol_reachability              true
% 3.17/0.98  --bmc1_property_lemmas                  false
% 3.17/0.98  --bmc1_k_induction                      false
% 3.17/0.98  --bmc1_non_equiv_states                 false
% 3.17/0.98  --bmc1_deadlock                         false
% 3.17/0.98  --bmc1_ucm                              false
% 3.17/0.98  --bmc1_add_unsat_core                   none
% 3.17/0.98  --bmc1_unsat_core_children              false
% 3.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/0.98  --bmc1_out_stat                         full
% 3.17/0.98  --bmc1_ground_init                      false
% 3.17/0.98  --bmc1_pre_inst_next_state              false
% 3.17/0.98  --bmc1_pre_inst_state                   false
% 3.17/0.98  --bmc1_pre_inst_reach_state             false
% 3.17/0.98  --bmc1_out_unsat_core                   false
% 3.17/0.98  --bmc1_aig_witness_out                  false
% 3.17/0.98  --bmc1_verbose                          false
% 3.17/0.98  --bmc1_dump_clauses_tptp                false
% 3.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.17/0.98  --bmc1_dump_file                        -
% 3.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.17/0.98  --bmc1_ucm_extend_mode                  1
% 3.17/0.98  --bmc1_ucm_init_mode                    2
% 3.17/0.98  --bmc1_ucm_cone_mode                    none
% 3.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.17/0.98  --bmc1_ucm_relax_model                  4
% 3.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/0.98  --bmc1_ucm_layered_model                none
% 3.17/0.98  --bmc1_ucm_max_lemma_size               10
% 3.17/0.98  
% 3.17/0.98  ------ AIG Options
% 3.17/0.98  
% 3.17/0.98  --aig_mode                              false
% 3.17/0.98  
% 3.17/0.98  ------ Instantiation Options
% 3.17/0.98  
% 3.17/0.98  --instantiation_flag                    true
% 3.17/0.98  --inst_sos_flag                         false
% 3.17/0.98  --inst_sos_phase                        true
% 3.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/0.98  --inst_lit_sel_side                     num_symb
% 3.17/0.98  --inst_solver_per_active                1400
% 3.17/0.98  --inst_solver_calls_frac                1.
% 3.17/0.98  --inst_passive_queue_type               priority_queues
% 3.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/0.98  --inst_passive_queues_freq              [25;2]
% 3.17/0.98  --inst_dismatching                      true
% 3.17/0.98  --inst_eager_unprocessed_to_passive     true
% 3.17/0.98  --inst_prop_sim_given                   true
% 3.17/0.98  --inst_prop_sim_new                     false
% 3.17/0.98  --inst_subs_new                         false
% 3.17/0.98  --inst_eq_res_simp                      false
% 3.17/0.98  --inst_subs_given                       false
% 3.17/0.98  --inst_orphan_elimination               true
% 3.17/0.98  --inst_learning_loop_flag               true
% 3.17/0.98  --inst_learning_start                   3000
% 3.17/0.98  --inst_learning_factor                  2
% 3.17/0.98  --inst_start_prop_sim_after_learn       3
% 3.17/0.98  --inst_sel_renew                        solver
% 3.17/0.98  --inst_lit_activity_flag                true
% 3.17/0.98  --inst_restr_to_given                   false
% 3.17/0.98  --inst_activity_threshold               500
% 3.17/0.98  --inst_out_proof                        true
% 3.17/0.98  
% 3.17/0.98  ------ Resolution Options
% 3.17/0.98  
% 3.17/0.98  --resolution_flag                       true
% 3.17/0.98  --res_lit_sel                           adaptive
% 3.17/0.98  --res_lit_sel_side                      none
% 3.17/0.98  --res_ordering                          kbo
% 3.17/0.98  --res_to_prop_solver                    active
% 3.17/0.98  --res_prop_simpl_new                    false
% 3.17/0.98  --res_prop_simpl_given                  true
% 3.17/0.98  --res_passive_queue_type                priority_queues
% 3.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/0.98  --res_passive_queues_freq               [15;5]
% 3.17/0.98  --res_forward_subs                      full
% 3.17/0.98  --res_backward_subs                     full
% 3.17/0.98  --res_forward_subs_resolution           true
% 3.17/0.98  --res_backward_subs_resolution          true
% 3.17/0.98  --res_orphan_elimination                true
% 3.17/0.98  --res_time_limit                        2.
% 3.17/0.98  --res_out_proof                         true
% 3.17/0.98  
% 3.17/0.98  ------ Superposition Options
% 3.17/0.98  
% 3.17/0.98  --superposition_flag                    true
% 3.17/0.98  --sup_passive_queue_type                priority_queues
% 3.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.17/0.98  --demod_completeness_check              fast
% 3.17/0.98  --demod_use_ground                      true
% 3.17/0.98  --sup_to_prop_solver                    passive
% 3.17/0.98  --sup_prop_simpl_new                    true
% 3.17/0.98  --sup_prop_simpl_given                  true
% 3.17/0.98  --sup_fun_splitting                     false
% 3.17/0.98  --sup_smt_interval                      50000
% 3.17/0.98  
% 3.17/0.98  ------ Superposition Simplification Setup
% 3.17/0.98  
% 3.17/0.98  --sup_indices_passive                   []
% 3.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_full_bw                           [BwDemod]
% 3.17/0.98  --sup_immed_triv                        [TrivRules]
% 3.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_immed_bw_main                     []
% 3.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.98  
% 3.17/0.98  ------ Combination Options
% 3.17/0.98  
% 3.17/0.98  --comb_res_mult                         3
% 3.17/0.98  --comb_sup_mult                         2
% 3.17/0.98  --comb_inst_mult                        10
% 3.17/0.98  
% 3.17/0.98  ------ Debug Options
% 3.17/0.98  
% 3.17/0.98  --dbg_backtrace                         false
% 3.17/0.98  --dbg_dump_prop_clauses                 false
% 3.17/0.98  --dbg_dump_prop_clauses_file            -
% 3.17/0.98  --dbg_out_stat                          false
% 3.17/0.98  ------ Parsing...
% 3.17/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.17/0.98  
% 3.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.17/0.98  
% 3.17/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.17/0.98  
% 3.17/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.17/0.98  ------ Proving...
% 3.17/0.98  ------ Problem Properties 
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  clauses                                 35
% 3.17/0.98  conjectures                             3
% 3.17/0.98  EPR                                     6
% 3.17/0.98  Horn                                    26
% 3.17/0.98  unary                                   9
% 3.17/0.98  binary                                  15
% 3.17/0.98  lits                                    74
% 3.17/0.98  lits eq                                 29
% 3.17/0.98  fd_pure                                 0
% 3.17/0.98  fd_pseudo                               0
% 3.17/0.98  fd_cond                                 3
% 3.17/0.98  fd_pseudo_cond                          0
% 3.17/0.98  AC symbols                              0
% 3.17/0.98  
% 3.17/0.98  ------ Schedule dynamic 5 is on 
% 3.17/0.98  
% 3.17/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  ------ 
% 3.17/0.98  Current options:
% 3.17/0.98  ------ 
% 3.17/0.98  
% 3.17/0.98  ------ Input Options
% 3.17/0.98  
% 3.17/0.98  --out_options                           all
% 3.17/0.98  --tptp_safe_out                         true
% 3.17/0.98  --problem_path                          ""
% 3.17/0.98  --include_path                          ""
% 3.17/0.98  --clausifier                            res/vclausify_rel
% 3.17/0.98  --clausifier_options                    --mode clausify
% 3.17/0.98  --stdin                                 false
% 3.17/0.98  --stats_out                             all
% 3.17/0.98  
% 3.17/0.98  ------ General Options
% 3.17/0.98  
% 3.17/0.98  --fof                                   false
% 3.17/0.98  --time_out_real                         305.
% 3.17/0.98  --time_out_virtual                      -1.
% 3.17/0.98  --symbol_type_check                     false
% 3.17/0.98  --clausify_out                          false
% 3.17/0.98  --sig_cnt_out                           false
% 3.17/0.98  --trig_cnt_out                          false
% 3.17/0.98  --trig_cnt_out_tolerance                1.
% 3.17/0.98  --trig_cnt_out_sk_spl                   false
% 3.17/0.98  --abstr_cl_out                          false
% 3.17/0.98  
% 3.17/0.98  ------ Global Options
% 3.17/0.98  
% 3.17/0.98  --schedule                              default
% 3.17/0.98  --add_important_lit                     false
% 3.17/0.98  --prop_solver_per_cl                    1000
% 3.17/0.98  --min_unsat_core                        false
% 3.17/0.98  --soft_assumptions                      false
% 3.17/0.98  --soft_lemma_size                       3
% 3.17/0.98  --prop_impl_unit_size                   0
% 3.17/0.98  --prop_impl_unit                        []
% 3.17/0.98  --share_sel_clauses                     true
% 3.17/0.98  --reset_solvers                         false
% 3.17/0.98  --bc_imp_inh                            [conj_cone]
% 3.17/0.98  --conj_cone_tolerance                   3.
% 3.17/0.98  --extra_neg_conj                        none
% 3.17/0.98  --large_theory_mode                     true
% 3.17/0.98  --prolific_symb_bound                   200
% 3.17/0.98  --lt_threshold                          2000
% 3.17/0.98  --clause_weak_htbl                      true
% 3.17/0.98  --gc_record_bc_elim                     false
% 3.17/0.98  
% 3.17/0.98  ------ Preprocessing Options
% 3.17/0.98  
% 3.17/0.98  --preprocessing_flag                    true
% 3.17/0.98  --time_out_prep_mult                    0.1
% 3.17/0.98  --splitting_mode                        input
% 3.17/0.98  --splitting_grd                         true
% 3.17/0.98  --splitting_cvd                         false
% 3.17/0.98  --splitting_cvd_svl                     false
% 3.17/0.98  --splitting_nvd                         32
% 3.17/0.98  --sub_typing                            true
% 3.17/0.98  --prep_gs_sim                           true
% 3.17/0.98  --prep_unflatten                        true
% 3.17/0.98  --prep_res_sim                          true
% 3.17/0.98  --prep_upred                            true
% 3.17/0.98  --prep_sem_filter                       exhaustive
% 3.17/0.98  --prep_sem_filter_out                   false
% 3.17/0.98  --pred_elim                             true
% 3.17/0.98  --res_sim_input                         true
% 3.17/0.98  --eq_ax_congr_red                       true
% 3.17/0.98  --pure_diseq_elim                       true
% 3.17/0.98  --brand_transform                       false
% 3.17/0.98  --non_eq_to_eq                          false
% 3.17/0.98  --prep_def_merge                        true
% 3.17/0.98  --prep_def_merge_prop_impl              false
% 3.17/0.98  --prep_def_merge_mbd                    true
% 3.17/0.98  --prep_def_merge_tr_red                 false
% 3.17/0.98  --prep_def_merge_tr_cl                  false
% 3.17/0.98  --smt_preprocessing                     true
% 3.17/0.98  --smt_ac_axioms                         fast
% 3.17/0.98  --preprocessed_out                      false
% 3.17/0.98  --preprocessed_stats                    false
% 3.17/0.98  
% 3.17/0.98  ------ Abstraction refinement Options
% 3.17/0.98  
% 3.17/0.98  --abstr_ref                             []
% 3.17/0.98  --abstr_ref_prep                        false
% 3.17/0.98  --abstr_ref_until_sat                   false
% 3.17/0.98  --abstr_ref_sig_restrict                funpre
% 3.17/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.17/0.98  --abstr_ref_under                       []
% 3.17/0.98  
% 3.17/0.98  ------ SAT Options
% 3.17/0.98  
% 3.17/0.98  --sat_mode                              false
% 3.17/0.98  --sat_fm_restart_options                ""
% 3.17/0.98  --sat_gr_def                            false
% 3.17/0.98  --sat_epr_types                         true
% 3.17/0.98  --sat_non_cyclic_types                  false
% 3.17/0.98  --sat_finite_models                     false
% 3.17/0.98  --sat_fm_lemmas                         false
% 3.17/0.98  --sat_fm_prep                           false
% 3.17/0.98  --sat_fm_uc_incr                        true
% 3.17/0.98  --sat_out_model                         small
% 3.17/0.98  --sat_out_clauses                       false
% 3.17/0.98  
% 3.17/0.98  ------ QBF Options
% 3.17/0.98  
% 3.17/0.98  --qbf_mode                              false
% 3.17/0.98  --qbf_elim_univ                         false
% 3.17/0.98  --qbf_dom_inst                          none
% 3.17/0.98  --qbf_dom_pre_inst                      false
% 3.17/0.98  --qbf_sk_in                             false
% 3.17/0.98  --qbf_pred_elim                         true
% 3.17/0.98  --qbf_split                             512
% 3.17/0.98  
% 3.17/0.98  ------ BMC1 Options
% 3.17/0.98  
% 3.17/0.98  --bmc1_incremental                      false
% 3.17/0.98  --bmc1_axioms                           reachable_all
% 3.17/0.98  --bmc1_min_bound                        0
% 3.17/0.98  --bmc1_max_bound                        -1
% 3.17/0.98  --bmc1_max_bound_default                -1
% 3.17/0.98  --bmc1_symbol_reachability              true
% 3.17/0.98  --bmc1_property_lemmas                  false
% 3.17/0.98  --bmc1_k_induction                      false
% 3.17/0.98  --bmc1_non_equiv_states                 false
% 3.17/0.98  --bmc1_deadlock                         false
% 3.17/0.98  --bmc1_ucm                              false
% 3.17/0.98  --bmc1_add_unsat_core                   none
% 3.17/0.98  --bmc1_unsat_core_children              false
% 3.17/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.17/0.98  --bmc1_out_stat                         full
% 3.17/0.98  --bmc1_ground_init                      false
% 3.17/0.98  --bmc1_pre_inst_next_state              false
% 3.17/0.98  --bmc1_pre_inst_state                   false
% 3.17/0.98  --bmc1_pre_inst_reach_state             false
% 3.17/0.98  --bmc1_out_unsat_core                   false
% 3.17/0.98  --bmc1_aig_witness_out                  false
% 3.17/0.98  --bmc1_verbose                          false
% 3.17/0.98  --bmc1_dump_clauses_tptp                false
% 3.17/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.17/0.98  --bmc1_dump_file                        -
% 3.17/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.17/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.17/0.98  --bmc1_ucm_extend_mode                  1
% 3.17/0.98  --bmc1_ucm_init_mode                    2
% 3.17/0.98  --bmc1_ucm_cone_mode                    none
% 3.17/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.17/0.98  --bmc1_ucm_relax_model                  4
% 3.17/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.17/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.17/0.98  --bmc1_ucm_layered_model                none
% 3.17/0.98  --bmc1_ucm_max_lemma_size               10
% 3.17/0.98  
% 3.17/0.98  ------ AIG Options
% 3.17/0.98  
% 3.17/0.98  --aig_mode                              false
% 3.17/0.98  
% 3.17/0.98  ------ Instantiation Options
% 3.17/0.98  
% 3.17/0.98  --instantiation_flag                    true
% 3.17/0.98  --inst_sos_flag                         false
% 3.17/0.98  --inst_sos_phase                        true
% 3.17/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.17/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.17/0.98  --inst_lit_sel_side                     none
% 3.17/0.98  --inst_solver_per_active                1400
% 3.17/0.98  --inst_solver_calls_frac                1.
% 3.17/0.98  --inst_passive_queue_type               priority_queues
% 3.17/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.17/0.98  --inst_passive_queues_freq              [25;2]
% 3.17/0.98  --inst_dismatching                      true
% 3.17/0.98  --inst_eager_unprocessed_to_passive     true
% 3.17/0.98  --inst_prop_sim_given                   true
% 3.17/0.98  --inst_prop_sim_new                     false
% 3.17/0.98  --inst_subs_new                         false
% 3.17/0.98  --inst_eq_res_simp                      false
% 3.17/0.98  --inst_subs_given                       false
% 3.17/0.98  --inst_orphan_elimination               true
% 3.17/0.98  --inst_learning_loop_flag               true
% 3.17/0.98  --inst_learning_start                   3000
% 3.17/0.98  --inst_learning_factor                  2
% 3.17/0.98  --inst_start_prop_sim_after_learn       3
% 3.17/0.98  --inst_sel_renew                        solver
% 3.17/0.98  --inst_lit_activity_flag                true
% 3.17/0.98  --inst_restr_to_given                   false
% 3.17/0.98  --inst_activity_threshold               500
% 3.17/0.98  --inst_out_proof                        true
% 3.17/0.98  
% 3.17/0.98  ------ Resolution Options
% 3.17/0.98  
% 3.17/0.98  --resolution_flag                       false
% 3.17/0.98  --res_lit_sel                           adaptive
% 3.17/0.98  --res_lit_sel_side                      none
% 3.17/0.98  --res_ordering                          kbo
% 3.17/0.98  --res_to_prop_solver                    active
% 3.17/0.98  --res_prop_simpl_new                    false
% 3.17/0.98  --res_prop_simpl_given                  true
% 3.17/0.98  --res_passive_queue_type                priority_queues
% 3.17/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.17/0.98  --res_passive_queues_freq               [15;5]
% 3.17/0.98  --res_forward_subs                      full
% 3.17/0.98  --res_backward_subs                     full
% 3.17/0.98  --res_forward_subs_resolution           true
% 3.17/0.98  --res_backward_subs_resolution          true
% 3.17/0.98  --res_orphan_elimination                true
% 3.17/0.98  --res_time_limit                        2.
% 3.17/0.98  --res_out_proof                         true
% 3.17/0.98  
% 3.17/0.98  ------ Superposition Options
% 3.17/0.98  
% 3.17/0.98  --superposition_flag                    true
% 3.17/0.98  --sup_passive_queue_type                priority_queues
% 3.17/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.17/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.17/0.98  --demod_completeness_check              fast
% 3.17/0.98  --demod_use_ground                      true
% 3.17/0.98  --sup_to_prop_solver                    passive
% 3.17/0.98  --sup_prop_simpl_new                    true
% 3.17/0.98  --sup_prop_simpl_given                  true
% 3.17/0.98  --sup_fun_splitting                     false
% 3.17/0.98  --sup_smt_interval                      50000
% 3.17/0.98  
% 3.17/0.98  ------ Superposition Simplification Setup
% 3.17/0.98  
% 3.17/0.98  --sup_indices_passive                   []
% 3.17/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.17/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.17/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_full_bw                           [BwDemod]
% 3.17/0.98  --sup_immed_triv                        [TrivRules]
% 3.17/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.17/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_immed_bw_main                     []
% 3.17/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.17/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.17/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.17/0.98  
% 3.17/0.98  ------ Combination Options
% 3.17/0.98  
% 3.17/0.98  --comb_res_mult                         3
% 3.17/0.98  --comb_sup_mult                         2
% 3.17/0.98  --comb_inst_mult                        10
% 3.17/0.98  
% 3.17/0.98  ------ Debug Options
% 3.17/0.98  
% 3.17/0.98  --dbg_backtrace                         false
% 3.17/0.98  --dbg_dump_prop_clauses                 false
% 3.17/0.98  --dbg_dump_prop_clauses_file            -
% 3.17/0.98  --dbg_out_stat                          false
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  ------ Proving...
% 3.17/0.98  
% 3.17/0.98  
% 3.17/0.98  % SZS status Theorem for theBenchmark.p
% 3.17/0.98  
% 3.17/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.17/0.98  
% 3.17/0.98  fof(f1,axiom,(
% 3.17/0.98    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f39,plain,(
% 3.17/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.17/0.98    inference(nnf_transformation,[],[f1])).
% 3.17/0.98  
% 3.17/0.98  fof(f40,plain,(
% 3.17/0.98    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.17/0.98    inference(rectify,[],[f39])).
% 3.17/0.98  
% 3.17/0.98  fof(f41,plain,(
% 3.17/0.98    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.17/0.98    introduced(choice_axiom,[])).
% 3.17/0.98  
% 3.17/0.98  fof(f42,plain,(
% 3.17/0.98    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.17/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.17/0.98  
% 3.17/0.98  fof(f57,plain,(
% 3.17/0.98    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.17/0.98    inference(cnf_transformation,[],[f42])).
% 3.17/0.98  
% 3.17/0.98  fof(f18,axiom,(
% 3.17/0.98    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f24,plain,(
% 3.17/0.98    ! [X0,X1,X2] : (r2_hidden(X2,k1_funct_2(X0,X1)) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)))),
% 3.17/0.98    inference(pure_predicate_removal,[],[f18])).
% 3.17/0.98  
% 3.17/0.98  fof(f36,plain,(
% 3.17/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1)) | ~r2_hidden(X2,k1_funct_2(X0,X1)))),
% 3.17/0.98    inference(ennf_transformation,[],[f24])).
% 3.17/0.98  
% 3.17/0.98  fof(f90,plain,(
% 3.17/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 3.17/0.98    inference(cnf_transformation,[],[f36])).
% 3.17/0.98  
% 3.17/0.98  fof(f19,axiom,(
% 3.17/0.98    ! [X0,X1] : k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))),
% 3.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f92,plain,(
% 3.17/0.98    ( ! [X0,X1] : (k1_funct_2(X0,X1) = k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) )),
% 3.17/0.98    inference(cnf_transformation,[],[f19])).
% 3.17/0.98  
% 3.17/0.98  fof(f98,plain,(
% 3.17/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 3.17/0.98    inference(definition_unfolding,[],[f90,f92])).
% 3.17/0.98  
% 3.17/0.98  fof(f16,axiom,(
% 3.17/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f32,plain,(
% 3.17/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/0.98    inference(ennf_transformation,[],[f16])).
% 3.17/0.98  
% 3.17/0.98  fof(f33,plain,(
% 3.17/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/0.98    inference(flattening,[],[f32])).
% 3.17/0.98  
% 3.17/0.98  fof(f53,plain,(
% 3.17/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/0.98    inference(nnf_transformation,[],[f33])).
% 3.17/0.98  
% 3.17/0.98  fof(f83,plain,(
% 3.17/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.98    inference(cnf_transformation,[],[f53])).
% 3.17/0.98  
% 3.17/0.98  fof(f91,plain,(
% 3.17/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k1_funct_2(X0,X1))) )),
% 3.17/0.98    inference(cnf_transformation,[],[f36])).
% 3.17/0.98  
% 3.17/0.98  fof(f97,plain,(
% 3.17/0.98    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) )),
% 3.17/0.98    inference(definition_unfolding,[],[f91,f92])).
% 3.17/0.98  
% 3.17/0.98  fof(f20,conjecture,(
% 3.17/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 3.17/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.98  
% 3.17/0.98  fof(f21,negated_conjecture,(
% 3.17/0.98    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 3.17/0.98    inference(negated_conjecture,[],[f20])).
% 3.17/0.98  
% 3.17/0.98  fof(f23,plain,(
% 3.17/0.98    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X2,k1_funct_2(X0,X1)) => (r1_tarski(k2_relat_1(X2),X1) & k1_relat_1(X2) = X0)))),
% 3.17/0.98    inference(pure_predicate_removal,[],[f21])).
% 3.17/0.98  
% 3.17/0.98  fof(f37,plain,(
% 3.17/0.98    ? [X0,X1,X2] : (((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1))) & v1_relat_1(X2))),
% 3.17/0.98    inference(ennf_transformation,[],[f23])).
% 3.17/0.98  
% 3.17/0.98  fof(f38,plain,(
% 3.17/0.98    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2))),
% 3.17/0.98    inference(flattening,[],[f37])).
% 3.17/0.99  
% 3.17/0.99  fof(f54,plain,(
% 3.17/0.99    ? [X0,X1,X2] : ((~r1_tarski(k2_relat_1(X2),X1) | k1_relat_1(X2) != X0) & r2_hidden(X2,k1_funct_2(X0,X1)) & v1_relat_1(X2)) => ((~r1_tarski(k2_relat_1(sK5),sK4) | k1_relat_1(sK5) != sK3) & r2_hidden(sK5,k1_funct_2(sK3,sK4)) & v1_relat_1(sK5))),
% 3.17/0.99    introduced(choice_axiom,[])).
% 3.17/0.99  
% 3.17/0.99  fof(f55,plain,(
% 3.17/0.99    (~r1_tarski(k2_relat_1(sK5),sK4) | k1_relat_1(sK5) != sK3) & r2_hidden(sK5,k1_funct_2(sK3,sK4)) & v1_relat_1(sK5)),
% 3.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f38,f54])).
% 3.17/0.99  
% 3.17/0.99  fof(f94,plain,(
% 3.17/0.99    r2_hidden(sK5,k1_funct_2(sK3,sK4))),
% 3.17/0.99    inference(cnf_transformation,[],[f55])).
% 3.17/0.99  
% 3.17/0.99  fof(f99,plain,(
% 3.17/0.99    r2_hidden(sK5,k5_partfun1(sK3,sK4,k3_partfun1(k1_xboole_0,sK3,sK4)))),
% 3.17/0.99    inference(definition_unfolding,[],[f94,f92])).
% 3.17/0.99  
% 3.17/0.99  fof(f56,plain,(
% 3.17/0.99    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.17/0.99    inference(cnf_transformation,[],[f42])).
% 3.17/0.99  
% 3.17/0.99  fof(f93,plain,(
% 3.17/0.99    v1_relat_1(sK5)),
% 3.17/0.99    inference(cnf_transformation,[],[f55])).
% 3.17/0.99  
% 3.17/0.99  fof(f15,axiom,(
% 3.17/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f31,plain,(
% 3.17/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.17/0.99    inference(ennf_transformation,[],[f15])).
% 3.17/0.99  
% 3.17/0.99  fof(f82,plain,(
% 3.17/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.17/0.99    inference(cnf_transformation,[],[f31])).
% 3.17/0.99  
% 3.17/0.99  fof(f95,plain,(
% 3.17/0.99    ~r1_tarski(k2_relat_1(sK5),sK4) | k1_relat_1(sK5) != sK3),
% 3.17/0.99    inference(cnf_transformation,[],[f55])).
% 3.17/0.99  
% 3.17/0.99  fof(f14,axiom,(
% 3.17/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f30,plain,(
% 3.17/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.17/0.99    inference(ennf_transformation,[],[f14])).
% 3.17/0.99  
% 3.17/0.99  fof(f52,plain,(
% 3.17/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.17/0.99    inference(nnf_transformation,[],[f30])).
% 3.17/0.99  
% 3.17/0.99  fof(f80,plain,(
% 3.17/0.99    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.17/0.99    inference(cnf_transformation,[],[f52])).
% 3.17/0.99  
% 3.17/0.99  fof(f6,axiom,(
% 3.17/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f65,plain,(
% 3.17/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.17/0.99    inference(cnf_transformation,[],[f6])).
% 3.17/0.99  
% 3.17/0.99  fof(f9,axiom,(
% 3.17/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f51,plain,(
% 3.17/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.17/0.99    inference(nnf_transformation,[],[f9])).
% 3.17/0.99  
% 3.17/0.99  fof(f71,plain,(
% 3.17/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.17/0.99    inference(cnf_transformation,[],[f51])).
% 3.17/0.99  
% 3.17/0.99  fof(f11,axiom,(
% 3.17/0.99    ! [X0,X1] : ~(~(k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f27,plain,(
% 3.17/0.99    ! [X0,X1] : ((k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 & k1_relat_1(k2_zfmisc_1(X0,X1)) = X0) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 3.17/0.99    inference(ennf_transformation,[],[f11])).
% 3.17/0.99  
% 3.17/0.99  fof(f75,plain,(
% 3.17/0.99    ( ! [X0,X1] : (k2_relat_1(k2_zfmisc_1(X0,X1)) = X1 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 3.17/0.99    inference(cnf_transformation,[],[f27])).
% 3.17/0.99  
% 3.17/0.99  fof(f12,axiom,(
% 3.17/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f28,plain,(
% 3.17/0.99    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.17/0.99    inference(ennf_transformation,[],[f12])).
% 3.17/0.99  
% 3.17/0.99  fof(f29,plain,(
% 3.17/0.99    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.17/0.99    inference(flattening,[],[f28])).
% 3.17/0.99  
% 3.17/0.99  fof(f77,plain,(
% 3.17/0.99    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.17/0.99    inference(cnf_transformation,[],[f29])).
% 3.17/0.99  
% 3.17/0.99  fof(f10,axiom,(
% 3.17/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f73,plain,(
% 3.17/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.17/0.99    inference(cnf_transformation,[],[f10])).
% 3.17/0.99  
% 3.17/0.99  fof(f5,axiom,(
% 3.17/0.99    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f47,plain,(
% 3.17/0.99    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 3.17/0.99    inference(nnf_transformation,[],[f5])).
% 3.17/0.99  
% 3.17/0.99  fof(f64,plain,(
% 3.17/0.99    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 3.17/0.99    inference(cnf_transformation,[],[f47])).
% 3.17/0.99  
% 3.17/0.99  fof(f8,axiom,(
% 3.17/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f49,plain,(
% 3.17/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.17/0.99    inference(nnf_transformation,[],[f8])).
% 3.17/0.99  
% 3.17/0.99  fof(f50,plain,(
% 3.17/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.17/0.99    inference(flattening,[],[f49])).
% 3.17/0.99  
% 3.17/0.99  fof(f70,plain,(
% 3.17/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.17/0.99    inference(cnf_transformation,[],[f50])).
% 3.17/0.99  
% 3.17/0.99  fof(f100,plain,(
% 3.17/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.17/0.99    inference(equality_resolution,[],[f70])).
% 3.17/0.99  
% 3.17/0.99  fof(f3,axiom,(
% 3.17/0.99    ? [X0] : v1_xboole_0(X0)),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f43,plain,(
% 3.17/0.99    ? [X0] : v1_xboole_0(X0) => v1_xboole_0(sK1)),
% 3.17/0.99    introduced(choice_axiom,[])).
% 3.17/0.99  
% 3.17/0.99  fof(f44,plain,(
% 3.17/0.99    v1_xboole_0(sK1)),
% 3.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f3,f43])).
% 3.17/0.99  
% 3.17/0.99  fof(f59,plain,(
% 3.17/0.99    v1_xboole_0(sK1)),
% 3.17/0.99    inference(cnf_transformation,[],[f44])).
% 3.17/0.99  
% 3.17/0.99  fof(f2,axiom,(
% 3.17/0.99    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f25,plain,(
% 3.17/0.99    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 3.17/0.99    inference(ennf_transformation,[],[f2])).
% 3.17/0.99  
% 3.17/0.99  fof(f58,plain,(
% 3.17/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.17/0.99    inference(cnf_transformation,[],[f25])).
% 3.17/0.99  
% 3.17/0.99  fof(f4,axiom,(
% 3.17/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f22,plain,(
% 3.17/0.99    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.17/0.99    inference(rectify,[],[f4])).
% 3.17/0.99  
% 3.17/0.99  fof(f26,plain,(
% 3.17/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.17/0.99    inference(ennf_transformation,[],[f22])).
% 3.17/0.99  
% 3.17/0.99  fof(f45,plain,(
% 3.17/0.99    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 3.17/0.99    introduced(choice_axiom,[])).
% 3.17/0.99  
% 3.17/0.99  fof(f46,plain,(
% 3.17/0.99    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.17/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f45])).
% 3.17/0.99  
% 3.17/0.99  fof(f61,plain,(
% 3.17/0.99    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 3.17/0.99    inference(cnf_transformation,[],[f46])).
% 3.17/0.99  
% 3.17/0.99  fof(f7,axiom,(
% 3.17/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f48,plain,(
% 3.17/0.99    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.17/0.99    inference(nnf_transformation,[],[f7])).
% 3.17/0.99  
% 3.17/0.99  fof(f66,plain,(
% 3.17/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.17/0.99    inference(cnf_transformation,[],[f48])).
% 3.17/0.99  
% 3.17/0.99  fof(f13,axiom,(
% 3.17/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f79,plain,(
% 3.17/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.17/0.99    inference(cnf_transformation,[],[f13])).
% 3.17/0.99  
% 3.17/0.99  fof(f78,plain,(
% 3.17/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.17/0.99    inference(cnf_transformation,[],[f13])).
% 3.17/0.99  
% 3.17/0.99  fof(f17,axiom,(
% 3.17/0.99    ! [X0,X1] : ((v1_xboole_0(X1) & ~v1_xboole_0(X0)) => v1_xboole_0(k1_funct_2(X0,X1)))),
% 3.17/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.17/0.99  
% 3.17/0.99  fof(f34,plain,(
% 3.17/0.99    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | (~v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.17/0.99    inference(ennf_transformation,[],[f17])).
% 3.17/0.99  
% 3.17/0.99  fof(f35,plain,(
% 3.17/0.99    ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.17/0.99    inference(flattening,[],[f34])).
% 3.17/0.99  
% 3.17/0.99  fof(f89,plain,(
% 3.17/0.99    ( ! [X0,X1] : (v1_xboole_0(k1_funct_2(X0,X1)) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.17/0.99    inference(cnf_transformation,[],[f35])).
% 3.17/0.99  
% 3.17/0.99  fof(f96,plain,(
% 3.17/0.99    ( ! [X0,X1] : (v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) | ~v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.17/0.99    inference(definition_unfolding,[],[f89,f92])).
% 3.17/0.99  
% 3.17/0.99  fof(f62,plain,(
% 3.17/0.99    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.17/0.99    inference(cnf_transformation,[],[f46])).
% 3.17/0.99  
% 3.17/0.99  fof(f67,plain,(
% 3.17/0.99    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.17/0.99    inference(cnf_transformation,[],[f48])).
% 3.17/0.99  
% 3.17/0.99  cnf(c_1350,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3986,plain,
% 3.17/0.99      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_1350]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6982,plain,
% 3.17/0.99      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_3986]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6983,plain,
% 3.17/0.99      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_6982]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_0,plain,
% 3.17/0.99      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.17/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2078,plain,
% 3.17/0.99      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.17/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_35,plain,
% 3.17/0.99      ( v1_funct_2(X0,X1,X2)
% 3.17/0.99      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 3.17/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_32,plain,
% 3.17/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.17/0.99      | k1_xboole_0 = X2 ),
% 3.17/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_841,plain,
% 3.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/0.99      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 3.17/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.17/0.99      | k1_xboole_0 = X2 ),
% 3.17/0.99      inference(resolution,[status(thm)],[c_35,c_32]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_34,plain,
% 3.17/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/0.99      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) ),
% 3.17/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_536,plain,
% 3.17/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.17/0.99      | ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 3.17/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.17/0.99      | k1_xboole_0 = X2 ),
% 3.17/0.99      inference(resolution,[status(thm)],[c_34,c_32]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_540,plain,
% 3.17/0.99      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 3.17/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.17/0.99      | k1_xboole_0 = X2 ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_536,c_35]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_845,plain,
% 3.17/0.99      ( ~ r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2)))
% 3.17/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.17/0.99      | k1_xboole_0 = X2 ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_841,c_35,c_536]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2053,plain,
% 3.17/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.17/0.99      | k1_xboole_0 = X1
% 3.17/0.99      | r2_hidden(X2,k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_845]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3307,plain,
% 3.17/0.99      ( k1_relset_1(X0,X1,sK0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1)))) = X0
% 3.17/0.99      | k1_xboole_0 = X1
% 3.17/0.99      | v1_xboole_0(k5_partfun1(X0,X1,k3_partfun1(k1_xboole_0,X0,X1))) = iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_2078,c_2053]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_37,negated_conjecture,
% 3.17/0.99      ( r2_hidden(sK5,k5_partfun1(sK3,sK4,k3_partfun1(k1_xboole_0,sK3,sK4))) ),
% 3.17/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2055,plain,
% 3.17/0.99      ( r2_hidden(sK5,k5_partfun1(sK3,sK4,k3_partfun1(k1_xboole_0,sK3,sK4))) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_1,plain,
% 3.17/0.99      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.17/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2077,plain,
% 3.17/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.17/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3119,plain,
% 3.17/0.99      ( v1_xboole_0(k5_partfun1(sK3,sK4,k3_partfun1(k1_xboole_0,sK3,sK4))) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_2055,c_2077]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6569,plain,
% 3.17/0.99      ( k1_relset_1(sK3,sK4,sK0(k5_partfun1(sK3,sK4,k3_partfun1(k1_xboole_0,sK3,sK4)))) = sK3
% 3.17/0.99      | sK4 = k1_xboole_0 ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_3307,c_3119]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_38,negated_conjecture,
% 3.17/0.99      ( v1_relat_1(sK5) ),
% 3.17/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3308,plain,
% 3.17/0.99      ( k1_relset_1(sK3,sK4,sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_2055,c_2053]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2057,plain,
% 3.17/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.17/0.99      | r2_hidden(X0,k5_partfun1(X1,X2,k3_partfun1(k1_xboole_0,X1,X2))) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4024,plain,
% 3.17/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_2055,c_2057]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_26,plain,
% 3.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.17/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.17/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2059,plain,
% 3.17/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.17/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4290,plain,
% 3.17/0.99      ( k1_relset_1(sK3,sK4,sK5) = k1_relat_1(sK5) ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_4024,c_2059]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4384,plain,
% 3.17/0.99      ( k1_relat_1(sK5) = sK3 | sK4 = k1_xboole_0 ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_3308,c_4290]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_36,negated_conjecture,
% 3.17/0.99      ( ~ r1_tarski(k2_relat_1(sK5),sK4) | k1_relat_1(sK5) != sK3 ),
% 3.17/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2056,plain,
% 3.17/0.99      ( k1_relat_1(sK5) != sK3
% 3.17/0.99      | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4394,plain,
% 3.17/0.99      ( sK4 = k1_xboole_0
% 3.17/0.99      | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_4384,c_2056]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4408,plain,
% 3.17/0.99      ( ~ r1_tarski(k2_relat_1(sK5),sK4) | sK4 = k1_xboole_0 ),
% 3.17/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4394]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_25,plain,
% 3.17/0.99      ( ~ v1_relat_1(X0)
% 3.17/0.99      | k1_relat_1(X0) != k1_xboole_0
% 3.17/0.99      | k2_relat_1(X0) = k1_xboole_0 ),
% 3.17/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2060,plain,
% 3.17/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.17/0.99      | k2_relat_1(X0) = k1_xboole_0
% 3.17/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4393,plain,
% 3.17/0.99      ( k2_relat_1(sK5) = k1_xboole_0
% 3.17/0.99      | sK3 != k1_xboole_0
% 3.17/0.99      | sK4 = k1_xboole_0
% 3.17/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_4384,c_2060]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_39,plain,
% 3.17/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_1353,plain,
% 3.17/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.17/0.99      theory(equality) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2363,plain,
% 3.17/0.99      ( ~ r1_tarski(X0,X1)
% 3.17/0.99      | r1_tarski(k2_relat_1(sK5),sK4)
% 3.17/0.99      | k2_relat_1(sK5) != X0
% 3.17/0.99      | sK4 != X1 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_1353]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2499,plain,
% 3.17/0.99      ( ~ r1_tarski(X0,sK4)
% 3.17/0.99      | r1_tarski(k2_relat_1(sK5),sK4)
% 3.17/0.99      | k2_relat_1(sK5) != X0
% 3.17/0.99      | sK4 != sK4 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_2363]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2501,plain,
% 3.17/0.99      ( k2_relat_1(sK5) != X0
% 3.17/0.99      | sK4 != sK4
% 3.17/0.99      | r1_tarski(X0,sK4) != iProver_top
% 3.17/0.99      | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_2499]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2503,plain,
% 3.17/0.99      ( k2_relat_1(sK5) != k1_xboole_0
% 3.17/0.99      | sK4 != sK4
% 3.17/0.99      | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
% 3.17/0.99      | r1_tarski(k1_xboole_0,sK4) != iProver_top ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_2501]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_1349,plain,( X0 = X0 ),theory(equality) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2500,plain,
% 3.17/0.99      ( sK4 = sK4 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_1349]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_9,plain,
% 3.17/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.17/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2771,plain,
% 3.17/0.99      ( r1_tarski(k1_xboole_0,sK4) ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2774,plain,
% 3.17/0.99      ( r1_tarski(k1_xboole_0,sK4) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_2771]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4541,plain,
% 3.17/0.99      ( sK4 = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_4393,c_39,c_2503,c_2500,c_2774,c_4394]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4542,plain,
% 3.17/0.99      ( sK3 != k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.17/0.99      inference(renaming,[status(thm)],[c_4541]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_16,plain,
% 3.17/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.17/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2065,plain,
% 3.17/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.17/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4289,plain,
% 3.17/0.99      ( r1_tarski(sK5,k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_4024,c_2065]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_18,plain,
% 3.17/0.99      ( k2_relat_1(k2_zfmisc_1(X0,X1)) = X1
% 3.17/0.99      | k1_xboole_0 = X0
% 3.17/0.99      | k1_xboole_0 = X1 ),
% 3.17/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_20,plain,
% 3.17/0.99      ( ~ r1_tarski(X0,X1)
% 3.17/0.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
% 3.17/0.99      | ~ v1_relat_1(X1)
% 3.17/0.99      | ~ v1_relat_1(X0) ),
% 3.17/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2063,plain,
% 3.17/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.17/0.99      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) = iProver_top
% 3.17/0.99      | v1_relat_1(X0) != iProver_top
% 3.17/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4725,plain,
% 3.17/0.99      ( k1_xboole_0 = X0
% 3.17/0.99      | k1_xboole_0 = X1
% 3.17/0.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 3.17/0.99      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 3.17/0.99      | v1_relat_1(X2) != iProver_top
% 3.17/0.99      | v1_relat_1(k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_18,c_2063]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_17,plain,
% 3.17/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.17/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_84,plain,
% 3.17/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6593,plain,
% 3.17/0.99      ( v1_relat_1(X2) != iProver_top
% 3.17/0.99      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 3.17/0.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 3.17/0.99      | k1_xboole_0 = X1
% 3.17/0.99      | k1_xboole_0 = X0 ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_4725,c_84]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6594,plain,
% 3.17/0.99      ( k1_xboole_0 = X0
% 3.17/0.99      | k1_xboole_0 = X1
% 3.17/0.99      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top
% 3.17/0.99      | r1_tarski(k2_relat_1(X2),X1) = iProver_top
% 3.17/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.17/0.99      inference(renaming,[status(thm)],[c_6593]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6603,plain,
% 3.17/0.99      ( sK3 = k1_xboole_0
% 3.17/0.99      | sK4 = k1_xboole_0
% 3.17/0.99      | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
% 3.17/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_4289,c_6594]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6619,plain,
% 3.17/0.99      ( r1_tarski(k2_relat_1(sK5),sK4)
% 3.17/0.99      | ~ v1_relat_1(sK5)
% 3.17/0.99      | sK3 = k1_xboole_0
% 3.17/0.99      | sK4 = k1_xboole_0 ),
% 3.17/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_6603]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6792,plain,
% 3.17/0.99      ( sK4 = k1_xboole_0 ),
% 3.17/0.99      inference(global_propositional_subsumption,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_6569,c_38,c_4408,c_4542,c_6619]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_7,plain,
% 3.17/0.99      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0 ),
% 3.17/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2071,plain,
% 3.17/0.99      ( k4_xboole_0(X0,X1) = k1_xboole_0
% 3.17/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4382,plain,
% 3.17/0.99      ( k4_xboole_0(sK5,k2_zfmisc_1(sK3,sK4)) = k1_xboole_0 ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_4289,c_2071]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6801,plain,
% 3.17/0.99      ( k4_xboole_0(sK5,k2_zfmisc_1(sK3,k1_xboole_0)) = k1_xboole_0 ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_6792,c_4382]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_12,plain,
% 3.17/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.17/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3,plain,
% 3.17/0.99      ( v1_xboole_0(sK1) ),
% 3.17/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2075,plain,
% 3.17/0.99      ( v1_xboole_0(sK1) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2,plain,
% 3.17/0.99      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 3.17/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2076,plain,
% 3.17/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2669,plain,
% 3.17/0.99      ( sK1 = k1_xboole_0 ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_2075,c_2076]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2800,plain,
% 3.17/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_2669,c_2075]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_5,plain,
% 3.17/0.99      ( r1_xboole_0(X0,X1) | r2_hidden(sK2(X0,X1),X1) ),
% 3.17/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2073,plain,
% 3.17/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.17/0.99      | r2_hidden(sK2(X0,X1),X1) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3378,plain,
% 3.17/0.99      ( r1_xboole_0(X0,X1) = iProver_top
% 3.17/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_2073,c_2077]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_11,plain,
% 3.17/0.99      ( ~ r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0 ),
% 3.17/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2067,plain,
% 3.17/0.99      ( k4_xboole_0(X0,X1) = X0 | r1_xboole_0(X0,X1) != iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3704,plain,
% 3.17/0.99      ( k4_xboole_0(X0,X1) = X0 | v1_xboole_0(X1) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_3378,c_2067]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3774,plain,
% 3.17/0.99      ( k4_xboole_0(X0,k1_xboole_0) = X0 ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_2800,c_3704]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6831,plain,
% 3.17/0.99      ( sK5 = k1_xboole_0 ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_6801,c_12,c_3774]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6808,plain,
% 3.17/0.99      ( k1_relat_1(sK5) != sK3
% 3.17/0.99      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_6792,c_2056]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6835,plain,
% 3.17/0.99      ( k1_relat_1(k1_xboole_0) != sK3
% 3.17/0.99      | r1_tarski(k2_relat_1(k1_xboole_0),k1_xboole_0) != iProver_top ),
% 3.17/0.99      inference(demodulation,[status(thm)],[c_6831,c_6808]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_22,plain,
% 3.17/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.17/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_23,plain,
% 3.17/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.17/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_6842,plain,
% 3.17/0.99      ( sK3 != k1_xboole_0
% 3.17/0.99      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.17/0.99      inference(light_normalisation,[status(thm)],[c_6835,c_22,c_23]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_1351,plain,
% 3.17/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.17/0.99      theory(equality) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_5728,plain,
% 3.17/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK4) | sK4 != X0 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_1351]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_5730,plain,
% 3.17/0.99      ( v1_xboole_0(sK4)
% 3.17/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.17/0.99      | sK4 != k1_xboole_0 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_5728]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_33,plain,
% 3.17/0.99      ( ~ v1_xboole_0(X0)
% 3.17/0.99      | v1_xboole_0(X1)
% 3.17/0.99      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) ),
% 3.17/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2058,plain,
% 3.17/0.99      ( v1_xboole_0(X0) != iProver_top
% 3.17/0.99      | v1_xboole_0(X1) = iProver_top
% 3.17/0.99      | v1_xboole_0(k5_partfun1(X1,X0,k3_partfun1(k1_xboole_0,X1,X0))) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4260,plain,
% 3.17/0.99      ( v1_xboole_0(sK3) = iProver_top
% 3.17/0.99      | v1_xboole_0(sK4) != iProver_top ),
% 3.17/0.99      inference(superposition,[status(thm)],[c_2058,c_3119]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4286,plain,
% 3.17/0.99      ( v1_xboole_0(sK3) | ~ v1_xboole_0(sK4) ),
% 3.17/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4260]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3863,plain,
% 3.17/0.99      ( sK3 = sK3 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_1349]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_3845,plain,
% 3.17/0.99      ( ~ v1_xboole_0(sK3) | k1_xboole_0 = sK3 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_4,plain,
% 3.17/0.99      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 3.17/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2680,plain,
% 3.17/0.99      ( ~ r1_xboole_0(X0,X1)
% 3.17/0.99      | ~ r2_hidden(sK0(X0),X0)
% 3.17/0.99      | ~ r2_hidden(sK0(X0),X1) ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_2682,plain,
% 3.17/0.99      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.17/0.99      | ~ r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_2680]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_123,plain,
% 3.17/0.99      ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
% 3.17/0.99      | v1_xboole_0(k1_xboole_0) ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_106,plain,
% 3.17/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.17/0.99      | k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_101,plain,
% 3.17/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.17/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_103,plain,
% 3.17/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_101]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_102,plain,
% 3.17/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_10,plain,
% 3.17/0.99      ( r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0 ),
% 3.17/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(c_99,plain,
% 3.17/0.99      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 3.17/0.99      | k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 3.17/0.99      inference(instantiation,[status(thm)],[c_10]) ).
% 3.17/0.99  
% 3.17/0.99  cnf(contradiction,plain,
% 3.17/0.99      ( $false ),
% 3.17/0.99      inference(minisat,
% 3.17/0.99                [status(thm)],
% 3.17/0.99                [c_6983,c_6842,c_6792,c_5730,c_4286,c_3863,c_3845,c_2682,
% 3.17/0.99                 c_123,c_106,c_103,c_102,c_99]) ).
% 3.17/0.99  
% 3.17/0.99  
% 3.17/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.17/0.99  
% 3.17/0.99  ------                               Statistics
% 3.17/0.99  
% 3.17/0.99  ------ General
% 3.17/0.99  
% 3.17/0.99  abstr_ref_over_cycles:                  0
% 3.17/0.99  abstr_ref_under_cycles:                 0
% 3.17/0.99  gc_basic_clause_elim:                   0
% 3.17/0.99  forced_gc_time:                         0
% 3.17/0.99  parsing_time:                           0.01
% 3.17/0.99  unif_index_cands_time:                  0.
% 3.17/0.99  unif_index_add_time:                    0.
% 3.17/0.99  orderings_time:                         0.
% 3.17/0.99  out_proof_time:                         0.011
% 3.17/0.99  total_time:                             0.204
% 3.17/0.99  num_of_symbols:                         53
% 3.17/0.99  num_of_terms:                           4760
% 3.17/0.99  
% 3.17/0.99  ------ Preprocessing
% 3.17/0.99  
% 3.17/0.99  num_of_splits:                          0
% 3.17/0.99  num_of_split_atoms:                     0
% 3.17/0.99  num_of_reused_defs:                     0
% 3.17/0.99  num_eq_ax_congr_red:                    29
% 3.17/0.99  num_of_sem_filtered_clauses:            1
% 3.17/0.99  num_of_subtypes:                        0
% 3.17/0.99  monotx_restored_types:                  0
% 3.17/0.99  sat_num_of_epr_types:                   0
% 3.17/0.99  sat_num_of_non_cyclic_types:            0
% 3.17/0.99  sat_guarded_non_collapsed_types:        0
% 3.17/0.99  num_pure_diseq_elim:                    0
% 3.17/0.99  simp_replaced_by:                       0
% 3.17/0.99  res_preprocessed:                       173
% 3.17/0.99  prep_upred:                             0
% 3.17/0.99  prep_unflattend:                        42
% 3.17/0.99  smt_new_axioms:                         0
% 3.17/0.99  pred_elim_cands:                        6
% 3.17/0.99  pred_elim:                              1
% 3.17/0.99  pred_elim_cl:                           4
% 3.17/0.99  pred_elim_cycles:                       6
% 3.17/0.99  merged_defs:                            24
% 3.17/0.99  merged_defs_ncl:                        0
% 3.17/0.99  bin_hyper_res:                          24
% 3.17/0.99  prep_cycles:                            4
% 3.17/0.99  pred_elim_time:                         0.011
% 3.17/0.99  splitting_time:                         0.
% 3.17/0.99  sem_filter_time:                        0.
% 3.17/0.99  monotx_time:                            0.
% 3.17/0.99  subtype_inf_time:                       0.
% 3.17/0.99  
% 3.17/0.99  ------ Problem properties
% 3.17/0.99  
% 3.17/0.99  clauses:                                35
% 3.17/0.99  conjectures:                            3
% 3.17/0.99  epr:                                    6
% 3.17/0.99  horn:                                   26
% 3.17/0.99  ground:                                 6
% 3.17/0.99  unary:                                  9
% 3.17/0.99  binary:                                 15
% 3.17/0.99  lits:                                   74
% 3.17/0.99  lits_eq:                                29
% 3.17/0.99  fd_pure:                                0
% 3.17/0.99  fd_pseudo:                              0
% 3.17/0.99  fd_cond:                                3
% 3.17/0.99  fd_pseudo_cond:                         0
% 3.17/0.99  ac_symbols:                             0
% 3.17/0.99  
% 3.17/0.99  ------ Propositional Solver
% 3.17/0.99  
% 3.17/0.99  prop_solver_calls:                      28
% 3.17/0.99  prop_fast_solver_calls:                 1223
% 3.17/0.99  smt_solver_calls:                       0
% 3.17/0.99  smt_fast_solver_calls:                  0
% 3.17/0.99  prop_num_of_clauses:                    2085
% 3.17/0.99  prop_preprocess_simplified:             7095
% 3.17/0.99  prop_fo_subsumed:                       23
% 3.17/0.99  prop_solver_time:                       0.
% 3.17/0.99  smt_solver_time:                        0.
% 3.17/0.99  smt_fast_solver_time:                   0.
% 3.17/0.99  prop_fast_solver_time:                  0.
% 3.17/0.99  prop_unsat_core_time:                   0.
% 3.17/0.99  
% 3.17/0.99  ------ QBF
% 3.17/0.99  
% 3.17/0.99  qbf_q_res:                              0
% 3.17/0.99  qbf_num_tautologies:                    0
% 3.17/0.99  qbf_prep_cycles:                        0
% 3.17/0.99  
% 3.17/0.99  ------ BMC1
% 3.17/0.99  
% 3.17/0.99  bmc1_current_bound:                     -1
% 3.17/0.99  bmc1_last_solved_bound:                 -1
% 3.17/0.99  bmc1_unsat_core_size:                   -1
% 3.17/0.99  bmc1_unsat_core_parents_size:           -1
% 3.17/0.99  bmc1_merge_next_fun:                    0
% 3.17/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.17/0.99  
% 3.17/0.99  ------ Instantiation
% 3.17/0.99  
% 3.17/0.99  inst_num_of_clauses:                    714
% 3.17/0.99  inst_num_in_passive:                    35
% 3.17/0.99  inst_num_in_active:                     405
% 3.17/0.99  inst_num_in_unprocessed:                273
% 3.17/0.99  inst_num_of_loops:                      519
% 3.17/0.99  inst_num_of_learning_restarts:          0
% 3.17/0.99  inst_num_moves_active_passive:          110
% 3.17/0.99  inst_lit_activity:                      0
% 3.17/0.99  inst_lit_activity_moves:                0
% 3.17/0.99  inst_num_tautologies:                   0
% 3.17/0.99  inst_num_prop_implied:                  0
% 3.17/0.99  inst_num_existing_simplified:           0
% 3.17/0.99  inst_num_eq_res_simplified:             0
% 3.17/0.99  inst_num_child_elim:                    0
% 3.17/0.99  inst_num_of_dismatching_blockings:      70
% 3.17/0.99  inst_num_of_non_proper_insts:           488
% 3.17/0.99  inst_num_of_duplicates:                 0
% 3.17/0.99  inst_inst_num_from_inst_to_res:         0
% 3.17/0.99  inst_dismatching_checking_time:         0.
% 3.17/0.99  
% 3.17/0.99  ------ Resolution
% 3.17/0.99  
% 3.17/0.99  res_num_of_clauses:                     0
% 3.17/0.99  res_num_in_passive:                     0
% 3.17/0.99  res_num_in_active:                      0
% 3.17/0.99  res_num_of_loops:                       177
% 3.17/0.99  res_forward_subset_subsumed:            28
% 3.17/0.99  res_backward_subset_subsumed:           0
% 3.17/0.99  res_forward_subsumed:                   0
% 3.17/0.99  res_backward_subsumed:                  0
% 3.17/0.99  res_forward_subsumption_resolution:     3
% 3.17/0.99  res_backward_subsumption_resolution:    0
% 3.17/0.99  res_clause_to_clause_subsumption:       370
% 3.17/0.99  res_orphan_elimination:                 0
% 3.17/0.99  res_tautology_del:                      87
% 3.17/0.99  res_num_eq_res_simplified:              0
% 3.17/0.99  res_num_sel_changes:                    0
% 3.17/0.99  res_moves_from_active_to_pass:          0
% 3.17/0.99  
% 3.17/0.99  ------ Superposition
% 3.17/0.99  
% 3.17/0.99  sup_time_total:                         0.
% 3.17/0.99  sup_time_generating:                    0.
% 3.17/0.99  sup_time_sim_full:                      0.
% 3.17/0.99  sup_time_sim_immed:                     0.
% 3.17/0.99  
% 3.17/0.99  sup_num_of_clauses:                     124
% 3.17/0.99  sup_num_in_active:                      76
% 3.17/0.99  sup_num_in_passive:                     48
% 3.17/0.99  sup_num_of_loops:                       102
% 3.17/0.99  sup_fw_superposition:                   116
% 3.17/0.99  sup_bw_superposition:                   57
% 3.17/0.99  sup_immediate_simplified:               31
% 3.17/0.99  sup_given_eliminated:                   0
% 3.17/0.99  comparisons_done:                       0
% 3.17/0.99  comparisons_avoided:                    9
% 3.17/0.99  
% 3.17/0.99  ------ Simplifications
% 3.17/0.99  
% 3.17/0.99  
% 3.17/0.99  sim_fw_subset_subsumed:                 6
% 3.17/0.99  sim_bw_subset_subsumed:                 10
% 3.17/0.99  sim_fw_subsumed:                        9
% 3.17/0.99  sim_bw_subsumed:                        0
% 3.17/0.99  sim_fw_subsumption_res:                 3
% 3.17/0.99  sim_bw_subsumption_res:                 0
% 3.17/0.99  sim_tautology_del:                      8
% 3.17/0.99  sim_eq_tautology_del:                   27
% 3.17/0.99  sim_eq_res_simp:                        1
% 3.17/0.99  sim_fw_demodulated:                     7
% 3.17/0.99  sim_bw_demodulated:                     21
% 3.17/0.99  sim_light_normalised:                   9
% 3.17/0.99  sim_joinable_taut:                      0
% 3.17/0.99  sim_joinable_simp:                      0
% 3.17/0.99  sim_ac_normalised:                      0
% 3.17/0.99  sim_smt_subsumption:                    0
% 3.17/0.99  
%------------------------------------------------------------------------------
