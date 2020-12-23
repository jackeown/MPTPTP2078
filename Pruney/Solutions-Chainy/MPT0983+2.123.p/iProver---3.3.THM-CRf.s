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
% DateTime   : Thu Dec  3 12:02:11 EST 2020

% Result     : Theorem 3.55s
% Output     : CNFRefutation 3.55s
% Verified   : 
% Statistics : Number of formulae       :  202 ( 902 expanded)
%              Number of clauses        :  113 ( 276 expanded)
%              Number of leaves         :   25 ( 220 expanded)
%              Depth                    :   21
%              Number of atoms          :  622 (5102 expanded)
%              Number of equality atoms :  247 ( 527 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK3,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f50,f49])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f83,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f12,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f19,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f19])).

fof(f94,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f70,f80])).

fof(f11,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f93,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f68,f80])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f44])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f100,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f102,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f76])).

fof(f90,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
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
    inference(nnf_transformation,[],[f2])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f97,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f96,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f74,f80])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f10,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f91,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f67,f80])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f38])).

fof(f81,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f84,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f87,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1076,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1082,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3465,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1076,c_1082])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3697,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3465,c_38])).

cnf(c_3698,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3697])).

cnf(c_3705,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1076,c_3698])).

cnf(c_3766,plain,
    ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3705,c_38])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1084,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3862,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3766,c_1084])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5945,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3862,c_38,c_40])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1091,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5949,plain,
    ( v1_xboole_0(k5_relat_1(sK2,sK2)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5945,c_1091])).

cnf(c_17,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_82,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_84,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_16,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_101,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_6,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_102,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_113,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_23,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_30,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_376,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_30])).

cnf(c_377,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_430,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_377])).

cnf(c_431,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_441,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_431,c_2])).

cnf(c_442,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_441])).

cnf(c_633,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1145,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_1146,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1145])).

cnf(c_1148,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1146])).

cnf(c_1204,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_1205,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1204])).

cnf(c_1207,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1205])).

cnf(c_623,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1362,plain,
    ( X0 != X1
    | X0 = k6_partfun1(X2)
    | k6_partfun1(X2) != X1 ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1363,plain,
    ( k6_partfun1(k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1362])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1444,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1445,plain,
    ( sK2 = X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1444])).

cnf(c_1447,plain,
    ( sK2 = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1445])).

cnf(c_1400,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1713,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1400])).

cnf(c_1714,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1713])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1089,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1079,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1090,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2423,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_1090])).

cnf(c_2429,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1089,c_2423])).

cnf(c_2424,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1076,c_1090])).

cnf(c_2602,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1089,c_2424])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_397,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_11])).

cnf(c_1072,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_397])).

cnf(c_2606,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_1072])).

cnf(c_2971,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2606,c_2429])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1094,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2975,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2971,c_1094])).

cnf(c_3464,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1079,c_1082])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3660,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3464,c_41])).

cnf(c_3661,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3660])).

cnf(c_3668,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1076,c_3661])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_358,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_359,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_22,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_367,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_359,c_22])).

cnf(c_1073,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_367])).

cnf(c_1132,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1462,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1073,c_37,c_35,c_34,c_32,c_367,c_1132])).

cnf(c_3671,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3668,c_1462])).

cnf(c_3853,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3671,c_38])).

cnf(c_13,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1088,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3855,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3853,c_1088])).

cnf(c_14,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_3856,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3855,c_14])).

cnf(c_10988,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5949,c_40,c_84,c_16,c_101,c_102,c_113,c_442,c_1148,c_1207,c_1363,c_1447,c_1714,c_2429,c_2602,c_2975,c_3856])).

cnf(c_1087,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1080,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3391,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1462,c_1080])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7948,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3391,c_38,c_39,c_40,c_41,c_42,c_43,c_442,c_2429,c_2602,c_2975,c_3856])).

cnf(c_7949,plain,
    ( sK0 = k1_xboole_0
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_7948])).

cnf(c_7952,plain,
    ( sK0 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1087,c_7949])).

cnf(c_10992,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10988,c_7952])).

cnf(c_10993,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10992,c_6])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10993,c_113])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.55/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.55/1.00  
% 3.55/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.55/1.00  
% 3.55/1.00  ------  iProver source info
% 3.55/1.00  
% 3.55/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.55/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.55/1.00  git: non_committed_changes: false
% 3.55/1.00  git: last_make_outside_of_git: false
% 3.55/1.00  
% 3.55/1.00  ------ 
% 3.55/1.00  
% 3.55/1.00  ------ Input Options
% 3.55/1.00  
% 3.55/1.00  --out_options                           all
% 3.55/1.00  --tptp_safe_out                         true
% 3.55/1.00  --problem_path                          ""
% 3.55/1.00  --include_path                          ""
% 3.55/1.00  --clausifier                            res/vclausify_rel
% 3.55/1.00  --clausifier_options                    ""
% 3.55/1.00  --stdin                                 false
% 3.55/1.00  --stats_out                             all
% 3.55/1.00  
% 3.55/1.00  ------ General Options
% 3.55/1.00  
% 3.55/1.00  --fof                                   false
% 3.55/1.00  --time_out_real                         305.
% 3.55/1.00  --time_out_virtual                      -1.
% 3.55/1.00  --symbol_type_check                     false
% 3.55/1.00  --clausify_out                          false
% 3.55/1.00  --sig_cnt_out                           false
% 3.55/1.00  --trig_cnt_out                          false
% 3.55/1.00  --trig_cnt_out_tolerance                1.
% 3.55/1.00  --trig_cnt_out_sk_spl                   false
% 3.55/1.00  --abstr_cl_out                          false
% 3.55/1.00  
% 3.55/1.00  ------ Global Options
% 3.55/1.00  
% 3.55/1.00  --schedule                              default
% 3.55/1.00  --add_important_lit                     false
% 3.55/1.00  --prop_solver_per_cl                    1000
% 3.55/1.00  --min_unsat_core                        false
% 3.55/1.00  --soft_assumptions                      false
% 3.55/1.00  --soft_lemma_size                       3
% 3.55/1.00  --prop_impl_unit_size                   0
% 3.55/1.00  --prop_impl_unit                        []
% 3.55/1.00  --share_sel_clauses                     true
% 3.55/1.00  --reset_solvers                         false
% 3.55/1.00  --bc_imp_inh                            [conj_cone]
% 3.55/1.00  --conj_cone_tolerance                   3.
% 3.55/1.00  --extra_neg_conj                        none
% 3.55/1.00  --large_theory_mode                     true
% 3.55/1.00  --prolific_symb_bound                   200
% 3.55/1.00  --lt_threshold                          2000
% 3.55/1.00  --clause_weak_htbl                      true
% 3.55/1.00  --gc_record_bc_elim                     false
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing Options
% 3.55/1.00  
% 3.55/1.00  --preprocessing_flag                    true
% 3.55/1.00  --time_out_prep_mult                    0.1
% 3.55/1.00  --splitting_mode                        input
% 3.55/1.00  --splitting_grd                         true
% 3.55/1.00  --splitting_cvd                         false
% 3.55/1.00  --splitting_cvd_svl                     false
% 3.55/1.00  --splitting_nvd                         32
% 3.55/1.00  --sub_typing                            true
% 3.55/1.00  --prep_gs_sim                           true
% 3.55/1.00  --prep_unflatten                        true
% 3.55/1.00  --prep_res_sim                          true
% 3.55/1.00  --prep_upred                            true
% 3.55/1.00  --prep_sem_filter                       exhaustive
% 3.55/1.00  --prep_sem_filter_out                   false
% 3.55/1.00  --pred_elim                             true
% 3.55/1.00  --res_sim_input                         true
% 3.55/1.00  --eq_ax_congr_red                       true
% 3.55/1.00  --pure_diseq_elim                       true
% 3.55/1.00  --brand_transform                       false
% 3.55/1.00  --non_eq_to_eq                          false
% 3.55/1.00  --prep_def_merge                        true
% 3.55/1.00  --prep_def_merge_prop_impl              false
% 3.55/1.00  --prep_def_merge_mbd                    true
% 3.55/1.00  --prep_def_merge_tr_red                 false
% 3.55/1.00  --prep_def_merge_tr_cl                  false
% 3.55/1.00  --smt_preprocessing                     true
% 3.55/1.00  --smt_ac_axioms                         fast
% 3.55/1.00  --preprocessed_out                      false
% 3.55/1.00  --preprocessed_stats                    false
% 3.55/1.00  
% 3.55/1.00  ------ Abstraction refinement Options
% 3.55/1.00  
% 3.55/1.00  --abstr_ref                             []
% 3.55/1.00  --abstr_ref_prep                        false
% 3.55/1.00  --abstr_ref_until_sat                   false
% 3.55/1.00  --abstr_ref_sig_restrict                funpre
% 3.55/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/1.00  --abstr_ref_under                       []
% 3.55/1.00  
% 3.55/1.00  ------ SAT Options
% 3.55/1.00  
% 3.55/1.00  --sat_mode                              false
% 3.55/1.00  --sat_fm_restart_options                ""
% 3.55/1.00  --sat_gr_def                            false
% 3.55/1.00  --sat_epr_types                         true
% 3.55/1.00  --sat_non_cyclic_types                  false
% 3.55/1.00  --sat_finite_models                     false
% 3.55/1.00  --sat_fm_lemmas                         false
% 3.55/1.00  --sat_fm_prep                           false
% 3.55/1.00  --sat_fm_uc_incr                        true
% 3.55/1.00  --sat_out_model                         small
% 3.55/1.00  --sat_out_clauses                       false
% 3.55/1.00  
% 3.55/1.00  ------ QBF Options
% 3.55/1.00  
% 3.55/1.00  --qbf_mode                              false
% 3.55/1.00  --qbf_elim_univ                         false
% 3.55/1.00  --qbf_dom_inst                          none
% 3.55/1.00  --qbf_dom_pre_inst                      false
% 3.55/1.00  --qbf_sk_in                             false
% 3.55/1.00  --qbf_pred_elim                         true
% 3.55/1.00  --qbf_split                             512
% 3.55/1.00  
% 3.55/1.00  ------ BMC1 Options
% 3.55/1.00  
% 3.55/1.00  --bmc1_incremental                      false
% 3.55/1.00  --bmc1_axioms                           reachable_all
% 3.55/1.00  --bmc1_min_bound                        0
% 3.55/1.00  --bmc1_max_bound                        -1
% 3.55/1.00  --bmc1_max_bound_default                -1
% 3.55/1.00  --bmc1_symbol_reachability              true
% 3.55/1.00  --bmc1_property_lemmas                  false
% 3.55/1.00  --bmc1_k_induction                      false
% 3.55/1.00  --bmc1_non_equiv_states                 false
% 3.55/1.00  --bmc1_deadlock                         false
% 3.55/1.00  --bmc1_ucm                              false
% 3.55/1.00  --bmc1_add_unsat_core                   none
% 3.55/1.00  --bmc1_unsat_core_children              false
% 3.55/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/1.00  --bmc1_out_stat                         full
% 3.55/1.00  --bmc1_ground_init                      false
% 3.55/1.00  --bmc1_pre_inst_next_state              false
% 3.55/1.00  --bmc1_pre_inst_state                   false
% 3.55/1.00  --bmc1_pre_inst_reach_state             false
% 3.55/1.00  --bmc1_out_unsat_core                   false
% 3.55/1.00  --bmc1_aig_witness_out                  false
% 3.55/1.00  --bmc1_verbose                          false
% 3.55/1.00  --bmc1_dump_clauses_tptp                false
% 3.55/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.55/1.00  --bmc1_dump_file                        -
% 3.55/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.55/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.55/1.00  --bmc1_ucm_extend_mode                  1
% 3.55/1.00  --bmc1_ucm_init_mode                    2
% 3.55/1.00  --bmc1_ucm_cone_mode                    none
% 3.55/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.55/1.00  --bmc1_ucm_relax_model                  4
% 3.55/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.55/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/1.00  --bmc1_ucm_layered_model                none
% 3.55/1.00  --bmc1_ucm_max_lemma_size               10
% 3.55/1.00  
% 3.55/1.00  ------ AIG Options
% 3.55/1.00  
% 3.55/1.00  --aig_mode                              false
% 3.55/1.00  
% 3.55/1.00  ------ Instantiation Options
% 3.55/1.00  
% 3.55/1.00  --instantiation_flag                    true
% 3.55/1.00  --inst_sos_flag                         true
% 3.55/1.00  --inst_sos_phase                        true
% 3.55/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel_side                     num_symb
% 3.55/1.00  --inst_solver_per_active                1400
% 3.55/1.00  --inst_solver_calls_frac                1.
% 3.55/1.00  --inst_passive_queue_type               priority_queues
% 3.55/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/1.00  --inst_passive_queues_freq              [25;2]
% 3.55/1.00  --inst_dismatching                      true
% 3.55/1.00  --inst_eager_unprocessed_to_passive     true
% 3.55/1.00  --inst_prop_sim_given                   true
% 3.55/1.00  --inst_prop_sim_new                     false
% 3.55/1.00  --inst_subs_new                         false
% 3.55/1.00  --inst_eq_res_simp                      false
% 3.55/1.00  --inst_subs_given                       false
% 3.55/1.00  --inst_orphan_elimination               true
% 3.55/1.00  --inst_learning_loop_flag               true
% 3.55/1.00  --inst_learning_start                   3000
% 3.55/1.00  --inst_learning_factor                  2
% 3.55/1.00  --inst_start_prop_sim_after_learn       3
% 3.55/1.00  --inst_sel_renew                        solver
% 3.55/1.00  --inst_lit_activity_flag                true
% 3.55/1.00  --inst_restr_to_given                   false
% 3.55/1.00  --inst_activity_threshold               500
% 3.55/1.00  --inst_out_proof                        true
% 3.55/1.00  
% 3.55/1.00  ------ Resolution Options
% 3.55/1.00  
% 3.55/1.00  --resolution_flag                       true
% 3.55/1.00  --res_lit_sel                           adaptive
% 3.55/1.00  --res_lit_sel_side                      none
% 3.55/1.00  --res_ordering                          kbo
% 3.55/1.00  --res_to_prop_solver                    active
% 3.55/1.00  --res_prop_simpl_new                    false
% 3.55/1.00  --res_prop_simpl_given                  true
% 3.55/1.00  --res_passive_queue_type                priority_queues
% 3.55/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/1.00  --res_passive_queues_freq               [15;5]
% 3.55/1.00  --res_forward_subs                      full
% 3.55/1.00  --res_backward_subs                     full
% 3.55/1.00  --res_forward_subs_resolution           true
% 3.55/1.00  --res_backward_subs_resolution          true
% 3.55/1.00  --res_orphan_elimination                true
% 3.55/1.00  --res_time_limit                        2.
% 3.55/1.00  --res_out_proof                         true
% 3.55/1.00  
% 3.55/1.00  ------ Superposition Options
% 3.55/1.00  
% 3.55/1.00  --superposition_flag                    true
% 3.55/1.00  --sup_passive_queue_type                priority_queues
% 3.55/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.55/1.00  --demod_completeness_check              fast
% 3.55/1.00  --demod_use_ground                      true
% 3.55/1.00  --sup_to_prop_solver                    passive
% 3.55/1.00  --sup_prop_simpl_new                    true
% 3.55/1.00  --sup_prop_simpl_given                  true
% 3.55/1.00  --sup_fun_splitting                     true
% 3.55/1.00  --sup_smt_interval                      50000
% 3.55/1.00  
% 3.55/1.00  ------ Superposition Simplification Setup
% 3.55/1.00  
% 3.55/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/1.00  --sup_immed_triv                        [TrivRules]
% 3.55/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_immed_bw_main                     []
% 3.55/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_input_bw                          []
% 3.55/1.00  
% 3.55/1.00  ------ Combination Options
% 3.55/1.00  
% 3.55/1.00  --comb_res_mult                         3
% 3.55/1.00  --comb_sup_mult                         2
% 3.55/1.00  --comb_inst_mult                        10
% 3.55/1.00  
% 3.55/1.00  ------ Debug Options
% 3.55/1.00  
% 3.55/1.00  --dbg_backtrace                         false
% 3.55/1.00  --dbg_dump_prop_clauses                 false
% 3.55/1.00  --dbg_dump_prop_clauses_file            -
% 3.55/1.00  --dbg_out_stat                          false
% 3.55/1.00  ------ Parsing...
% 3.55/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.55/1.00  ------ Proving...
% 3.55/1.00  ------ Problem Properties 
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  clauses                                 31
% 3.55/1.00  conjectures                             6
% 3.55/1.00  EPR                                     8
% 3.55/1.00  Horn                                    29
% 3.55/1.00  unary                                   17
% 3.55/1.00  binary                                  1
% 3.55/1.00  lits                                    75
% 3.55/1.00  lits eq                                 14
% 3.55/1.00  fd_pure                                 0
% 3.55/1.00  fd_pseudo                               0
% 3.55/1.00  fd_cond                                 2
% 3.55/1.00  fd_pseudo_cond                          2
% 3.55/1.00  AC symbols                              0
% 3.55/1.00  
% 3.55/1.00  ------ Schedule dynamic 5 is on 
% 3.55/1.00  
% 3.55/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  ------ 
% 3.55/1.00  Current options:
% 3.55/1.00  ------ 
% 3.55/1.00  
% 3.55/1.00  ------ Input Options
% 3.55/1.00  
% 3.55/1.00  --out_options                           all
% 3.55/1.00  --tptp_safe_out                         true
% 3.55/1.00  --problem_path                          ""
% 3.55/1.00  --include_path                          ""
% 3.55/1.00  --clausifier                            res/vclausify_rel
% 3.55/1.00  --clausifier_options                    ""
% 3.55/1.00  --stdin                                 false
% 3.55/1.00  --stats_out                             all
% 3.55/1.00  
% 3.55/1.00  ------ General Options
% 3.55/1.00  
% 3.55/1.00  --fof                                   false
% 3.55/1.00  --time_out_real                         305.
% 3.55/1.00  --time_out_virtual                      -1.
% 3.55/1.00  --symbol_type_check                     false
% 3.55/1.00  --clausify_out                          false
% 3.55/1.00  --sig_cnt_out                           false
% 3.55/1.00  --trig_cnt_out                          false
% 3.55/1.00  --trig_cnt_out_tolerance                1.
% 3.55/1.00  --trig_cnt_out_sk_spl                   false
% 3.55/1.00  --abstr_cl_out                          false
% 3.55/1.00  
% 3.55/1.00  ------ Global Options
% 3.55/1.00  
% 3.55/1.00  --schedule                              default
% 3.55/1.00  --add_important_lit                     false
% 3.55/1.00  --prop_solver_per_cl                    1000
% 3.55/1.00  --min_unsat_core                        false
% 3.55/1.00  --soft_assumptions                      false
% 3.55/1.00  --soft_lemma_size                       3
% 3.55/1.00  --prop_impl_unit_size                   0
% 3.55/1.00  --prop_impl_unit                        []
% 3.55/1.00  --share_sel_clauses                     true
% 3.55/1.00  --reset_solvers                         false
% 3.55/1.00  --bc_imp_inh                            [conj_cone]
% 3.55/1.00  --conj_cone_tolerance                   3.
% 3.55/1.00  --extra_neg_conj                        none
% 3.55/1.00  --large_theory_mode                     true
% 3.55/1.00  --prolific_symb_bound                   200
% 3.55/1.00  --lt_threshold                          2000
% 3.55/1.00  --clause_weak_htbl                      true
% 3.55/1.00  --gc_record_bc_elim                     false
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing Options
% 3.55/1.00  
% 3.55/1.00  --preprocessing_flag                    true
% 3.55/1.00  --time_out_prep_mult                    0.1
% 3.55/1.00  --splitting_mode                        input
% 3.55/1.00  --splitting_grd                         true
% 3.55/1.00  --splitting_cvd                         false
% 3.55/1.00  --splitting_cvd_svl                     false
% 3.55/1.00  --splitting_nvd                         32
% 3.55/1.00  --sub_typing                            true
% 3.55/1.00  --prep_gs_sim                           true
% 3.55/1.00  --prep_unflatten                        true
% 3.55/1.00  --prep_res_sim                          true
% 3.55/1.00  --prep_upred                            true
% 3.55/1.00  --prep_sem_filter                       exhaustive
% 3.55/1.00  --prep_sem_filter_out                   false
% 3.55/1.00  --pred_elim                             true
% 3.55/1.00  --res_sim_input                         true
% 3.55/1.00  --eq_ax_congr_red                       true
% 3.55/1.00  --pure_diseq_elim                       true
% 3.55/1.00  --brand_transform                       false
% 3.55/1.00  --non_eq_to_eq                          false
% 3.55/1.00  --prep_def_merge                        true
% 3.55/1.00  --prep_def_merge_prop_impl              false
% 3.55/1.00  --prep_def_merge_mbd                    true
% 3.55/1.00  --prep_def_merge_tr_red                 false
% 3.55/1.00  --prep_def_merge_tr_cl                  false
% 3.55/1.00  --smt_preprocessing                     true
% 3.55/1.00  --smt_ac_axioms                         fast
% 3.55/1.00  --preprocessed_out                      false
% 3.55/1.00  --preprocessed_stats                    false
% 3.55/1.00  
% 3.55/1.00  ------ Abstraction refinement Options
% 3.55/1.00  
% 3.55/1.00  --abstr_ref                             []
% 3.55/1.00  --abstr_ref_prep                        false
% 3.55/1.00  --abstr_ref_until_sat                   false
% 3.55/1.00  --abstr_ref_sig_restrict                funpre
% 3.55/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.55/1.00  --abstr_ref_under                       []
% 3.55/1.00  
% 3.55/1.00  ------ SAT Options
% 3.55/1.00  
% 3.55/1.00  --sat_mode                              false
% 3.55/1.00  --sat_fm_restart_options                ""
% 3.55/1.00  --sat_gr_def                            false
% 3.55/1.00  --sat_epr_types                         true
% 3.55/1.00  --sat_non_cyclic_types                  false
% 3.55/1.00  --sat_finite_models                     false
% 3.55/1.00  --sat_fm_lemmas                         false
% 3.55/1.00  --sat_fm_prep                           false
% 3.55/1.00  --sat_fm_uc_incr                        true
% 3.55/1.00  --sat_out_model                         small
% 3.55/1.00  --sat_out_clauses                       false
% 3.55/1.00  
% 3.55/1.00  ------ QBF Options
% 3.55/1.00  
% 3.55/1.00  --qbf_mode                              false
% 3.55/1.00  --qbf_elim_univ                         false
% 3.55/1.00  --qbf_dom_inst                          none
% 3.55/1.00  --qbf_dom_pre_inst                      false
% 3.55/1.00  --qbf_sk_in                             false
% 3.55/1.00  --qbf_pred_elim                         true
% 3.55/1.00  --qbf_split                             512
% 3.55/1.00  
% 3.55/1.00  ------ BMC1 Options
% 3.55/1.00  
% 3.55/1.00  --bmc1_incremental                      false
% 3.55/1.00  --bmc1_axioms                           reachable_all
% 3.55/1.00  --bmc1_min_bound                        0
% 3.55/1.00  --bmc1_max_bound                        -1
% 3.55/1.00  --bmc1_max_bound_default                -1
% 3.55/1.00  --bmc1_symbol_reachability              true
% 3.55/1.00  --bmc1_property_lemmas                  false
% 3.55/1.00  --bmc1_k_induction                      false
% 3.55/1.00  --bmc1_non_equiv_states                 false
% 3.55/1.00  --bmc1_deadlock                         false
% 3.55/1.00  --bmc1_ucm                              false
% 3.55/1.00  --bmc1_add_unsat_core                   none
% 3.55/1.00  --bmc1_unsat_core_children              false
% 3.55/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.55/1.00  --bmc1_out_stat                         full
% 3.55/1.00  --bmc1_ground_init                      false
% 3.55/1.00  --bmc1_pre_inst_next_state              false
% 3.55/1.00  --bmc1_pre_inst_state                   false
% 3.55/1.00  --bmc1_pre_inst_reach_state             false
% 3.55/1.00  --bmc1_out_unsat_core                   false
% 3.55/1.00  --bmc1_aig_witness_out                  false
% 3.55/1.00  --bmc1_verbose                          false
% 3.55/1.00  --bmc1_dump_clauses_tptp                false
% 3.55/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.55/1.00  --bmc1_dump_file                        -
% 3.55/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.55/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.55/1.00  --bmc1_ucm_extend_mode                  1
% 3.55/1.00  --bmc1_ucm_init_mode                    2
% 3.55/1.00  --bmc1_ucm_cone_mode                    none
% 3.55/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.55/1.00  --bmc1_ucm_relax_model                  4
% 3.55/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.55/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.55/1.00  --bmc1_ucm_layered_model                none
% 3.55/1.00  --bmc1_ucm_max_lemma_size               10
% 3.55/1.00  
% 3.55/1.00  ------ AIG Options
% 3.55/1.00  
% 3.55/1.00  --aig_mode                              false
% 3.55/1.00  
% 3.55/1.00  ------ Instantiation Options
% 3.55/1.00  
% 3.55/1.00  --instantiation_flag                    true
% 3.55/1.00  --inst_sos_flag                         true
% 3.55/1.00  --inst_sos_phase                        true
% 3.55/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.55/1.00  --inst_lit_sel_side                     none
% 3.55/1.00  --inst_solver_per_active                1400
% 3.55/1.00  --inst_solver_calls_frac                1.
% 3.55/1.00  --inst_passive_queue_type               priority_queues
% 3.55/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.55/1.00  --inst_passive_queues_freq              [25;2]
% 3.55/1.00  --inst_dismatching                      true
% 3.55/1.00  --inst_eager_unprocessed_to_passive     true
% 3.55/1.00  --inst_prop_sim_given                   true
% 3.55/1.00  --inst_prop_sim_new                     false
% 3.55/1.00  --inst_subs_new                         false
% 3.55/1.00  --inst_eq_res_simp                      false
% 3.55/1.00  --inst_subs_given                       false
% 3.55/1.00  --inst_orphan_elimination               true
% 3.55/1.00  --inst_learning_loop_flag               true
% 3.55/1.00  --inst_learning_start                   3000
% 3.55/1.00  --inst_learning_factor                  2
% 3.55/1.00  --inst_start_prop_sim_after_learn       3
% 3.55/1.00  --inst_sel_renew                        solver
% 3.55/1.00  --inst_lit_activity_flag                true
% 3.55/1.00  --inst_restr_to_given                   false
% 3.55/1.00  --inst_activity_threshold               500
% 3.55/1.00  --inst_out_proof                        true
% 3.55/1.00  
% 3.55/1.00  ------ Resolution Options
% 3.55/1.00  
% 3.55/1.00  --resolution_flag                       false
% 3.55/1.00  --res_lit_sel                           adaptive
% 3.55/1.00  --res_lit_sel_side                      none
% 3.55/1.00  --res_ordering                          kbo
% 3.55/1.00  --res_to_prop_solver                    active
% 3.55/1.00  --res_prop_simpl_new                    false
% 3.55/1.00  --res_prop_simpl_given                  true
% 3.55/1.00  --res_passive_queue_type                priority_queues
% 3.55/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.55/1.00  --res_passive_queues_freq               [15;5]
% 3.55/1.00  --res_forward_subs                      full
% 3.55/1.00  --res_backward_subs                     full
% 3.55/1.00  --res_forward_subs_resolution           true
% 3.55/1.00  --res_backward_subs_resolution          true
% 3.55/1.00  --res_orphan_elimination                true
% 3.55/1.00  --res_time_limit                        2.
% 3.55/1.00  --res_out_proof                         true
% 3.55/1.00  
% 3.55/1.00  ------ Superposition Options
% 3.55/1.00  
% 3.55/1.00  --superposition_flag                    true
% 3.55/1.00  --sup_passive_queue_type                priority_queues
% 3.55/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.55/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.55/1.00  --demod_completeness_check              fast
% 3.55/1.00  --demod_use_ground                      true
% 3.55/1.00  --sup_to_prop_solver                    passive
% 3.55/1.00  --sup_prop_simpl_new                    true
% 3.55/1.00  --sup_prop_simpl_given                  true
% 3.55/1.00  --sup_fun_splitting                     true
% 3.55/1.00  --sup_smt_interval                      50000
% 3.55/1.00  
% 3.55/1.00  ------ Superposition Simplification Setup
% 3.55/1.00  
% 3.55/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.55/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.55/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.55/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.55/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.55/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.55/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.55/1.00  --sup_immed_triv                        [TrivRules]
% 3.55/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_immed_bw_main                     []
% 3.55/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.55/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.55/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.55/1.00  --sup_input_bw                          []
% 3.55/1.00  
% 3.55/1.00  ------ Combination Options
% 3.55/1.00  
% 3.55/1.00  --comb_res_mult                         3
% 3.55/1.00  --comb_sup_mult                         2
% 3.55/1.00  --comb_inst_mult                        10
% 3.55/1.00  
% 3.55/1.00  ------ Debug Options
% 3.55/1.00  
% 3.55/1.00  --dbg_backtrace                         false
% 3.55/1.00  --dbg_dump_prop_clauses                 false
% 3.55/1.00  --dbg_dump_prop_clauses_file            -
% 3.55/1.00  --dbg_out_stat                          false
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  ------ Proving...
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  % SZS status Theorem for theBenchmark.p
% 3.55/1.00  
% 3.55/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.55/1.00  
% 3.55/1.00  fof(f21,conjecture,(
% 3.55/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f22,negated_conjecture,(
% 3.55/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.55/1.00    inference(negated_conjecture,[],[f21])).
% 3.55/1.00  
% 3.55/1.00  fof(f40,plain,(
% 3.55/1.00    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.55/1.00    inference(ennf_transformation,[],[f22])).
% 3.55/1.00  
% 3.55/1.00  fof(f41,plain,(
% 3.55/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.55/1.00    inference(flattening,[],[f40])).
% 3.55/1.00  
% 3.55/1.00  fof(f50,plain,(
% 3.55/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.55/1.00    introduced(choice_axiom,[])).
% 3.55/1.00  
% 3.55/1.00  fof(f49,plain,(
% 3.55/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.55/1.00    introduced(choice_axiom,[])).
% 3.55/1.00  
% 3.55/1.00  fof(f51,plain,(
% 3.55/1.00    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.55/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f41,f50,f49])).
% 3.55/1.00  
% 3.55/1.00  fof(f85,plain,(
% 3.55/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.55/1.00    inference(cnf_transformation,[],[f51])).
% 3.55/1.00  
% 3.55/1.00  fof(f18,axiom,(
% 3.55/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f36,plain,(
% 3.55/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.55/1.00    inference(ennf_transformation,[],[f18])).
% 3.55/1.00  
% 3.55/1.00  fof(f37,plain,(
% 3.55/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.55/1.00    inference(flattening,[],[f36])).
% 3.55/1.00  
% 3.55/1.00  fof(f79,plain,(
% 3.55/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f37])).
% 3.55/1.00  
% 3.55/1.00  fof(f83,plain,(
% 3.55/1.00    v1_funct_1(sK2)),
% 3.55/1.00    inference(cnf_transformation,[],[f51])).
% 3.55/1.00  
% 3.55/1.00  fof(f17,axiom,(
% 3.55/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f34,plain,(
% 3.55/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.55/1.00    inference(ennf_transformation,[],[f17])).
% 3.55/1.00  
% 3.55/1.00  fof(f35,plain,(
% 3.55/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.55/1.00    inference(flattening,[],[f34])).
% 3.55/1.00  
% 3.55/1.00  fof(f78,plain,(
% 3.55/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f35])).
% 3.55/1.00  
% 3.55/1.00  fof(f5,axiom,(
% 3.55/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f25,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.55/1.00    inference(ennf_transformation,[],[f5])).
% 3.55/1.00  
% 3.55/1.00  fof(f60,plain,(
% 3.55/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f25])).
% 3.55/1.00  
% 3.55/1.00  fof(f12,axiom,(
% 3.55/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f70,plain,(
% 3.55/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.55/1.00    inference(cnf_transformation,[],[f12])).
% 3.55/1.00  
% 3.55/1.00  fof(f19,axiom,(
% 3.55/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f80,plain,(
% 3.55/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f19])).
% 3.55/1.00  
% 3.55/1.00  fof(f94,plain,(
% 3.55/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.55/1.00    inference(definition_unfolding,[],[f70,f80])).
% 3.55/1.00  
% 3.55/1.00  fof(f11,axiom,(
% 3.55/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f68,plain,(
% 3.55/1.00    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.55/1.00    inference(cnf_transformation,[],[f11])).
% 3.55/1.00  
% 3.55/1.00  fof(f93,plain,(
% 3.55/1.00    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.55/1.00    inference(definition_unfolding,[],[f68,f80])).
% 3.55/1.00  
% 3.55/1.00  fof(f4,axiom,(
% 3.55/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f44,plain,(
% 3.55/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.55/1.00    inference(nnf_transformation,[],[f4])).
% 3.55/1.00  
% 3.55/1.00  fof(f45,plain,(
% 3.55/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.55/1.00    inference(flattening,[],[f44])).
% 3.55/1.00  
% 3.55/1.00  fof(f57,plain,(
% 3.55/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f45])).
% 3.55/1.00  
% 3.55/1.00  fof(f58,plain,(
% 3.55/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.55/1.00    inference(cnf_transformation,[],[f45])).
% 3.55/1.00  
% 3.55/1.00  fof(f100,plain,(
% 3.55/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.55/1.00    inference(equality_resolution,[],[f58])).
% 3.55/1.00  
% 3.55/1.00  fof(f1,axiom,(
% 3.55/1.00    v1_xboole_0(k1_xboole_0)),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f52,plain,(
% 3.55/1.00    v1_xboole_0(k1_xboole_0)),
% 3.55/1.00    inference(cnf_transformation,[],[f1])).
% 3.55/1.00  
% 3.55/1.00  fof(f7,axiom,(
% 3.55/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f27,plain,(
% 3.55/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.55/1.00    inference(ennf_transformation,[],[f7])).
% 3.55/1.00  
% 3.55/1.00  fof(f46,plain,(
% 3.55/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.55/1.00    inference(nnf_transformation,[],[f27])).
% 3.55/1.00  
% 3.55/1.00  fof(f63,plain,(
% 3.55/1.00    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f46])).
% 3.55/1.00  
% 3.55/1.00  fof(f16,axiom,(
% 3.55/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f32,plain,(
% 3.55/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.55/1.00    inference(ennf_transformation,[],[f16])).
% 3.55/1.00  
% 3.55/1.00  fof(f33,plain,(
% 3.55/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.55/1.00    inference(flattening,[],[f32])).
% 3.55/1.00  
% 3.55/1.00  fof(f48,plain,(
% 3.55/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.55/1.00    inference(nnf_transformation,[],[f33])).
% 3.55/1.00  
% 3.55/1.00  fof(f76,plain,(
% 3.55/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f48])).
% 3.55/1.00  
% 3.55/1.00  fof(f102,plain,(
% 3.55/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.55/1.00    inference(equality_resolution,[],[f76])).
% 3.55/1.00  
% 3.55/1.00  fof(f90,plain,(
% 3.55/1.00    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.55/1.00    inference(cnf_transformation,[],[f51])).
% 3.55/1.00  
% 3.55/1.00  fof(f2,axiom,(
% 3.55/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f42,plain,(
% 3.55/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.55/1.00    inference(nnf_transformation,[],[f2])).
% 3.55/1.00  
% 3.55/1.00  fof(f43,plain,(
% 3.55/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.55/1.00    inference(flattening,[],[f42])).
% 3.55/1.00  
% 3.55/1.00  fof(f54,plain,(
% 3.55/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.55/1.00    inference(cnf_transformation,[],[f43])).
% 3.55/1.00  
% 3.55/1.00  fof(f97,plain,(
% 3.55/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.55/1.00    inference(equality_resolution,[],[f54])).
% 3.55/1.00  
% 3.55/1.00  fof(f3,axiom,(
% 3.55/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f24,plain,(
% 3.55/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.55/1.00    inference(ennf_transformation,[],[f3])).
% 3.55/1.00  
% 3.55/1.00  fof(f56,plain,(
% 3.55/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f24])).
% 3.55/1.00  
% 3.55/1.00  fof(f8,axiom,(
% 3.55/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f64,plain,(
% 3.55/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.55/1.00    inference(cnf_transformation,[],[f8])).
% 3.55/1.00  
% 3.55/1.00  fof(f88,plain,(
% 3.55/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.55/1.00    inference(cnf_transformation,[],[f51])).
% 3.55/1.00  
% 3.55/1.00  fof(f6,axiom,(
% 3.55/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f26,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.55/1.00    inference(ennf_transformation,[],[f6])).
% 3.55/1.00  
% 3.55/1.00  fof(f61,plain,(
% 3.55/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f26])).
% 3.55/1.00  
% 3.55/1.00  fof(f13,axiom,(
% 3.55/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f23,plain,(
% 3.55/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.55/1.00    inference(pure_predicate_removal,[],[f13])).
% 3.55/1.00  
% 3.55/1.00  fof(f29,plain,(
% 3.55/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/1.00    inference(ennf_transformation,[],[f23])).
% 3.55/1.00  
% 3.55/1.00  fof(f71,plain,(
% 3.55/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/1.00    inference(cnf_transformation,[],[f29])).
% 3.55/1.00  
% 3.55/1.00  fof(f62,plain,(
% 3.55/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f46])).
% 3.55/1.00  
% 3.55/1.00  fof(f55,plain,(
% 3.55/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f43])).
% 3.55/1.00  
% 3.55/1.00  fof(f86,plain,(
% 3.55/1.00    v1_funct_1(sK3)),
% 3.55/1.00    inference(cnf_transformation,[],[f51])).
% 3.55/1.00  
% 3.55/1.00  fof(f14,axiom,(
% 3.55/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f30,plain,(
% 3.55/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.55/1.00    inference(ennf_transformation,[],[f14])).
% 3.55/1.00  
% 3.55/1.00  fof(f31,plain,(
% 3.55/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/1.00    inference(flattening,[],[f30])).
% 3.55/1.00  
% 3.55/1.00  fof(f47,plain,(
% 3.55/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.55/1.00    inference(nnf_transformation,[],[f31])).
% 3.55/1.00  
% 3.55/1.00  fof(f72,plain,(
% 3.55/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.55/1.00    inference(cnf_transformation,[],[f47])).
% 3.55/1.00  
% 3.55/1.00  fof(f89,plain,(
% 3.55/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.55/1.00    inference(cnf_transformation,[],[f51])).
% 3.55/1.00  
% 3.55/1.00  fof(f15,axiom,(
% 3.55/1.00    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f74,plain,(
% 3.55/1.00    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.55/1.00    inference(cnf_transformation,[],[f15])).
% 3.55/1.00  
% 3.55/1.00  fof(f96,plain,(
% 3.55/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.55/1.00    inference(definition_unfolding,[],[f74,f80])).
% 3.55/1.00  
% 3.55/1.00  fof(f9,axiom,(
% 3.55/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f28,plain,(
% 3.55/1.00    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.55/1.00    inference(ennf_transformation,[],[f9])).
% 3.55/1.00  
% 3.55/1.00  fof(f65,plain,(
% 3.55/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f28])).
% 3.55/1.00  
% 3.55/1.00  fof(f10,axiom,(
% 3.55/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f67,plain,(
% 3.55/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.55/1.00    inference(cnf_transformation,[],[f10])).
% 3.55/1.00  
% 3.55/1.00  fof(f91,plain,(
% 3.55/1.00    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.55/1.00    inference(definition_unfolding,[],[f67,f80])).
% 3.55/1.00  
% 3.55/1.00  fof(f20,axiom,(
% 3.55/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.55/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.55/1.00  
% 3.55/1.00  fof(f38,plain,(
% 3.55/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.55/1.00    inference(ennf_transformation,[],[f20])).
% 3.55/1.00  
% 3.55/1.00  fof(f39,plain,(
% 3.55/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.55/1.00    inference(flattening,[],[f38])).
% 3.55/1.00  
% 3.55/1.00  fof(f81,plain,(
% 3.55/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.55/1.00    inference(cnf_transformation,[],[f39])).
% 3.55/1.00  
% 3.55/1.00  fof(f84,plain,(
% 3.55/1.00    v1_funct_2(sK2,sK0,sK1)),
% 3.55/1.00    inference(cnf_transformation,[],[f51])).
% 3.55/1.00  
% 3.55/1.00  fof(f87,plain,(
% 3.55/1.00    v1_funct_2(sK3,sK1,sK0)),
% 3.55/1.00    inference(cnf_transformation,[],[f51])).
% 3.55/1.00  
% 3.55/1.00  cnf(c_35,negated_conjecture,
% 3.55/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.55/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1076,plain,
% 3.55/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_27,plain,
% 3.55/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.55/1.00      | ~ v1_funct_1(X0)
% 3.55/1.00      | ~ v1_funct_1(X3)
% 3.55/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1082,plain,
% 3.55/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.55/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.55/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.55/1.00      | v1_funct_1(X5) != iProver_top
% 3.55/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3465,plain,
% 3.55/1.00      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.55/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.55/1.00      | v1_funct_1(X2) != iProver_top
% 3.55/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1076,c_1082]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_37,negated_conjecture,
% 3.55/1.00      ( v1_funct_1(sK2) ),
% 3.55/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_38,plain,
% 3.55/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3697,plain,
% 3.55/1.00      ( v1_funct_1(X2) != iProver_top
% 3.55/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.55/1.00      | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_3465,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3698,plain,
% 3.55/1.00      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 3.55/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.55/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_3697]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3705,plain,
% 3.55/1.00      ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2)
% 3.55/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1076,c_3698]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3766,plain,
% 3.55/1.00      ( k1_partfun1(sK0,sK1,sK0,sK1,sK2,sK2) = k5_relat_1(sK2,sK2) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_3705,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_25,plain,
% 3.55/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.55/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.55/1.00      | ~ v1_funct_1(X0)
% 3.55/1.00      | ~ v1_funct_1(X3) ),
% 3.55/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1084,plain,
% 3.55/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.55/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 3.55/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 3.55/1.00      | v1_funct_1(X0) != iProver_top
% 3.55/1.00      | v1_funct_1(X3) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3862,plain,
% 3.55/1.00      ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top
% 3.55/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.55/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_3766,c_1084]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_40,plain,
% 3.55/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_5945,plain,
% 3.55/1.00      ( m1_subset_1(k5_relat_1(sK2,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_3862,c_38,c_40]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_8,plain,
% 3.55/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.55/1.00      | ~ v1_xboole_0(X1)
% 3.55/1.00      | v1_xboole_0(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1091,plain,
% 3.55/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.55/1.00      | v1_xboole_0(X1) != iProver_top
% 3.55/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_5949,plain,
% 3.55/1.00      ( v1_xboole_0(k5_relat_1(sK2,sK2)) = iProver_top
% 3.55/1.00      | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_5945,c_1091]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_17,plain,
% 3.55/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.55/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_82,plain,
% 3.55/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_84,plain,
% 3.55/1.00      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_82]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_16,plain,
% 3.55/1.00      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.55/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7,plain,
% 3.55/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.55/1.00      | k1_xboole_0 = X1
% 3.55/1.00      | k1_xboole_0 = X0 ),
% 3.55/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_101,plain,
% 3.55/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.55/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_6,plain,
% 3.55/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.55/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_102,plain,
% 3.55/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_0,plain,
% 3.55/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_113,plain,
% 3.55/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10,plain,
% 3.55/1.00      ( v5_relat_1(X0,X1)
% 3.55/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.55/1.00      | ~ v1_relat_1(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_23,plain,
% 3.55/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.55/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.55/1.00      | ~ v1_relat_1(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_30,negated_conjecture,
% 3.55/1.00      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.55/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_376,plain,
% 3.55/1.00      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.55/1.00      | ~ v2_funct_1(sK2)
% 3.55/1.00      | ~ v1_relat_1(X0)
% 3.55/1.00      | k2_relat_1(X0) != sK0
% 3.55/1.00      | sK3 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_30]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_377,plain,
% 3.55/1.00      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.55/1.00      | ~ v2_funct_1(sK2)
% 3.55/1.00      | ~ v1_relat_1(sK3)
% 3.55/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_376]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_430,plain,
% 3.55/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.55/1.00      | ~ v2_funct_1(sK2)
% 3.55/1.00      | ~ v1_relat_1(X0)
% 3.55/1.00      | ~ v1_relat_1(sK3)
% 3.55/1.00      | k2_relat_1(sK3) != X1
% 3.55/1.00      | k2_relat_1(sK3) != sK0
% 3.55/1.00      | sK3 != X0 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_10,c_377]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_431,plain,
% 3.55/1.00      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 3.55/1.00      | ~ v2_funct_1(sK2)
% 3.55/1.00      | ~ v1_relat_1(sK3)
% 3.55/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_430]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_2,plain,
% 3.55/1.00      ( r1_tarski(X0,X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_441,plain,
% 3.55/1.00      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 3.55/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_431,c_2]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_442,plain,
% 3.55/1.00      ( k2_relat_1(sK3) != sK0
% 3.55/1.00      | v2_funct_1(sK2) != iProver_top
% 3.55/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_441]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_633,plain,
% 3.55/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.55/1.00      theory(equality) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1145,plain,
% 3.55/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_633]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1146,plain,
% 3.55/1.00      ( sK2 != X0
% 3.55/1.00      | v2_funct_1(X0) != iProver_top
% 3.55/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1145]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1148,plain,
% 3.55/1.00      ( sK2 != k1_xboole_0
% 3.55/1.00      | v2_funct_1(sK2) = iProver_top
% 3.55/1.00      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1146]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1204,plain,
% 3.55/1.00      ( v2_funct_1(X0)
% 3.55/1.00      | ~ v2_funct_1(k6_partfun1(X1))
% 3.55/1.00      | X0 != k6_partfun1(X1) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_633]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1205,plain,
% 3.55/1.00      ( X0 != k6_partfun1(X1)
% 3.55/1.00      | v2_funct_1(X0) = iProver_top
% 3.55/1.00      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1204]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1207,plain,
% 3.55/1.00      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.55/1.00      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.55/1.00      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1205]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_623,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1362,plain,
% 3.55/1.00      ( X0 != X1 | X0 = k6_partfun1(X2) | k6_partfun1(X2) != X1 ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_623]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1363,plain,
% 3.55/1.00      ( k6_partfun1(k1_xboole_0) != k1_xboole_0
% 3.55/1.00      | k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.55/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1362]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_4,plain,
% 3.55/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.55/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1444,plain,
% 3.55/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK2) | sK2 = X0 ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1445,plain,
% 3.55/1.00      ( sK2 = X0
% 3.55/1.00      | v1_xboole_0(X0) != iProver_top
% 3.55/1.00      | v1_xboole_0(sK2) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1444]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1447,plain,
% 3.55/1.00      ( sK2 = k1_xboole_0
% 3.55/1.00      | v1_xboole_0(sK2) != iProver_top
% 3.55/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1445]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1400,plain,
% 3.55/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
% 3.55/1.00      | ~ v1_xboole_0(X0)
% 3.55/1.00      | v1_xboole_0(sK2) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1713,plain,
% 3.55/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.55/1.00      | ~ v1_xboole_0(k2_zfmisc_1(sK0,sK1))
% 3.55/1.00      | v1_xboole_0(sK2) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_1400]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1714,plain,
% 3.55/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.55/1.00      | v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.55/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1713]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_12,plain,
% 3.55/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.55/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1089,plain,
% 3.55/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_32,negated_conjecture,
% 3.55/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.55/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1079,plain,
% 3.55/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_9,plain,
% 3.55/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.55/1.00      | ~ v1_relat_1(X1)
% 3.55/1.00      | v1_relat_1(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1090,plain,
% 3.55/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.55/1.00      | v1_relat_1(X1) != iProver_top
% 3.55/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_2423,plain,
% 3.55/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.55/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1079,c_1090]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_2429,plain,
% 3.55/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1089,c_2423]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_2424,plain,
% 3.55/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.55/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1076,c_1090]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_2602,plain,
% 3.55/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1089,c_2424]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_19,plain,
% 3.55/1.00      ( v5_relat_1(X0,X1)
% 3.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.55/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_11,plain,
% 3.55/1.00      ( ~ v5_relat_1(X0,X1)
% 3.55/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.55/1.00      | ~ v1_relat_1(X0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_397,plain,
% 3.55/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.55/1.00      | ~ v1_relat_1(X0) ),
% 3.55/1.00      inference(resolution,[status(thm)],[c_19,c_11]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1072,plain,
% 3.55/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.55/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.55/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_397]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_2606,plain,
% 3.55/1.00      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.55/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1079,c_1072]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_2971,plain,
% 3.55/1.00      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_2606,c_2429]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1,plain,
% 3.55/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.55/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1094,plain,
% 3.55/1.00      ( X0 = X1
% 3.55/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.55/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_2975,plain,
% 3.55/1.00      ( k2_relat_1(sK3) = sK0
% 3.55/1.00      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_2971,c_1094]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3464,plain,
% 3.55/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.55/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.55/1.00      | v1_funct_1(X2) != iProver_top
% 3.55/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1079,c_1082]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_34,negated_conjecture,
% 3.55/1.00      ( v1_funct_1(sK3) ),
% 3.55/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_41,plain,
% 3.55/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3660,plain,
% 3.55/1.00      ( v1_funct_1(X2) != iProver_top
% 3.55/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.55/1.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_3464,c_41]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3661,plain,
% 3.55/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.55/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.55/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_3660]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3668,plain,
% 3.55/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.55/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1076,c_3661]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_21,plain,
% 3.55/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.55/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.55/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.55/1.00      | X3 = X2 ),
% 3.55/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_31,negated_conjecture,
% 3.55/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.55/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_358,plain,
% 3.55/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/1.00      | X3 = X0
% 3.55/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.55/1.00      | k6_partfun1(sK0) != X3
% 3.55/1.00      | sK0 != X2
% 3.55/1.00      | sK0 != X1 ),
% 3.55/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_359,plain,
% 3.55/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.55/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.55/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.55/1.00      inference(unflattening,[status(thm)],[c_358]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_22,plain,
% 3.55/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.55/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_367,plain,
% 3.55/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.55/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.55/1.00      inference(forward_subsumption_resolution,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_359,c_22]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1073,plain,
% 3.55/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.55/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_367]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1132,plain,
% 3.55/1.00      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.55/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.55/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.55/1.00      | ~ v1_funct_1(sK2)
% 3.55/1.00      | ~ v1_funct_1(sK3) ),
% 3.55/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1462,plain,
% 3.55/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_1073,c_37,c_35,c_34,c_32,c_367,c_1132]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3671,plain,
% 3.55/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.55/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.55/1.00      inference(light_normalisation,[status(thm)],[c_3668,c_1462]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3853,plain,
% 3.55/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_3671,c_38]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_13,plain,
% 3.55/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.55/1.00      | ~ v1_relat_1(X0)
% 3.55/1.00      | ~ v1_relat_1(X1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1088,plain,
% 3.55/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.55/1.00      | v1_relat_1(X0) != iProver_top
% 3.55/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3855,plain,
% 3.55/1.00      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 3.55/1.00      | v1_relat_1(sK2) != iProver_top
% 3.55/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_3853,c_1088]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_14,plain,
% 3.55/1.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.55/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3856,plain,
% 3.55/1.00      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 3.55/1.00      | v1_relat_1(sK2) != iProver_top
% 3.55/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.55/1.00      inference(demodulation,[status(thm)],[c_3855,c_14]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10988,plain,
% 3.55/1.00      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_5949,c_40,c_84,c_16,c_101,c_102,c_113,c_442,c_1148,
% 3.55/1.00                 c_1207,c_1363,c_1447,c_1714,c_2429,c_2602,c_2975,c_3856]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1087,plain,
% 3.55/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_29,plain,
% 3.55/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.55/1.00      | ~ v1_funct_2(X3,X4,X1)
% 3.55/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.55/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.55/1.00      | ~ v1_funct_1(X0)
% 3.55/1.00      | ~ v1_funct_1(X3)
% 3.55/1.00      | v2_funct_1(X3)
% 3.55/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.55/1.00      | k1_xboole_0 = X2 ),
% 3.55/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_1080,plain,
% 3.55/1.00      ( k1_xboole_0 = X0
% 3.55/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.55/1.00      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.55/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.55/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.55/1.00      | v1_funct_1(X1) != iProver_top
% 3.55/1.00      | v1_funct_1(X3) != iProver_top
% 3.55/1.00      | v2_funct_1(X3) = iProver_top
% 3.55/1.00      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_3391,plain,
% 3.55/1.00      ( sK0 = k1_xboole_0
% 3.55/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.55/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.55/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.55/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.55/1.00      | v1_funct_1(sK2) != iProver_top
% 3.55/1.00      | v1_funct_1(sK3) != iProver_top
% 3.55/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.55/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1462,c_1080]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_36,negated_conjecture,
% 3.55/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.55/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_39,plain,
% 3.55/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_33,negated_conjecture,
% 3.55/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.55/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_42,plain,
% 3.55/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_43,plain,
% 3.55/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.55/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7948,plain,
% 3.55/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top | sK0 = k1_xboole_0 ),
% 3.55/1.00      inference(global_propositional_subsumption,
% 3.55/1.00                [status(thm)],
% 3.55/1.00                [c_3391,c_38,c_39,c_40,c_41,c_42,c_43,c_442,c_2429,
% 3.55/1.00                 c_2602,c_2975,c_3856]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7949,plain,
% 3.55/1.00      ( sK0 = k1_xboole_0 | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 3.55/1.00      inference(renaming,[status(thm)],[c_7948]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_7952,plain,
% 3.55/1.00      ( sK0 = k1_xboole_0 ),
% 3.55/1.00      inference(superposition,[status(thm)],[c_1087,c_7949]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10992,plain,
% 3.55/1.00      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,sK1)) != iProver_top ),
% 3.55/1.00      inference(light_normalisation,[status(thm)],[c_10988,c_7952]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(c_10993,plain,
% 3.55/1.00      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.55/1.00      inference(demodulation,[status(thm)],[c_10992,c_6]) ).
% 3.55/1.00  
% 3.55/1.00  cnf(contradiction,plain,
% 3.55/1.00      ( $false ),
% 3.55/1.00      inference(minisat,[status(thm)],[c_10993,c_113]) ).
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.55/1.00  
% 3.55/1.00  ------                               Statistics
% 3.55/1.00  
% 3.55/1.00  ------ General
% 3.55/1.00  
% 3.55/1.00  abstr_ref_over_cycles:                  0
% 3.55/1.00  abstr_ref_under_cycles:                 0
% 3.55/1.00  gc_basic_clause_elim:                   0
% 3.55/1.00  forced_gc_time:                         0
% 3.55/1.00  parsing_time:                           0.009
% 3.55/1.00  unif_index_cands_time:                  0.
% 3.55/1.00  unif_index_add_time:                    0.
% 3.55/1.00  orderings_time:                         0.
% 3.55/1.00  out_proof_time:                         0.011
% 3.55/1.00  total_time:                             0.367
% 3.55/1.00  num_of_symbols:                         53
% 3.55/1.00  num_of_terms:                           15133
% 3.55/1.00  
% 3.55/1.00  ------ Preprocessing
% 3.55/1.00  
% 3.55/1.00  num_of_splits:                          0
% 3.55/1.00  num_of_split_atoms:                     0
% 3.55/1.00  num_of_reused_defs:                     0
% 3.55/1.00  num_eq_ax_congr_red:                    7
% 3.55/1.00  num_of_sem_filtered_clauses:            1
% 3.55/1.00  num_of_subtypes:                        0
% 3.55/1.00  monotx_restored_types:                  0
% 3.55/1.00  sat_num_of_epr_types:                   0
% 3.55/1.00  sat_num_of_non_cyclic_types:            0
% 3.55/1.00  sat_guarded_non_collapsed_types:        0
% 3.55/1.00  num_pure_diseq_elim:                    0
% 3.55/1.00  simp_replaced_by:                       0
% 3.55/1.00  res_preprocessed:                       161
% 3.55/1.00  prep_upred:                             0
% 3.55/1.00  prep_unflattend:                        15
% 3.55/1.00  smt_new_axioms:                         0
% 3.55/1.00  pred_elim_cands:                        7
% 3.55/1.00  pred_elim:                              3
% 3.55/1.00  pred_elim_cl:                           6
% 3.55/1.00  pred_elim_cycles:                       5
% 3.55/1.00  merged_defs:                            0
% 3.55/1.00  merged_defs_ncl:                        0
% 3.55/1.00  bin_hyper_res:                          0
% 3.55/1.00  prep_cycles:                            4
% 3.55/1.00  pred_elim_time:                         0.002
% 3.55/1.00  splitting_time:                         0.
% 3.55/1.00  sem_filter_time:                        0.
% 3.55/1.00  monotx_time:                            0.
% 3.55/1.00  subtype_inf_time:                       0.
% 3.55/1.00  
% 3.55/1.00  ------ Problem properties
% 3.55/1.00  
% 3.55/1.00  clauses:                                31
% 3.55/1.00  conjectures:                            6
% 3.55/1.00  epr:                                    8
% 3.55/1.00  horn:                                   29
% 3.55/1.00  ground:                                 10
% 3.55/1.00  unary:                                  17
% 3.55/1.00  binary:                                 1
% 3.55/1.00  lits:                                   75
% 3.55/1.00  lits_eq:                                14
% 3.55/1.00  fd_pure:                                0
% 3.55/1.00  fd_pseudo:                              0
% 3.55/1.00  fd_cond:                                2
% 3.55/1.00  fd_pseudo_cond:                         2
% 3.55/1.00  ac_symbols:                             0
% 3.55/1.00  
% 3.55/1.00  ------ Propositional Solver
% 3.55/1.00  
% 3.55/1.00  prop_solver_calls:                      33
% 3.55/1.00  prop_fast_solver_calls:                 1415
% 3.55/1.00  smt_solver_calls:                       0
% 3.55/1.00  smt_fast_solver_calls:                  0
% 3.55/1.00  prop_num_of_clauses:                    5530
% 3.55/1.00  prop_preprocess_simplified:             13458
% 3.55/1.00  prop_fo_subsumed:                       74
% 3.55/1.00  prop_solver_time:                       0.
% 3.55/1.00  smt_solver_time:                        0.
% 3.55/1.00  smt_fast_solver_time:                   0.
% 3.55/1.00  prop_fast_solver_time:                  0.
% 3.55/1.00  prop_unsat_core_time:                   0.
% 3.55/1.00  
% 3.55/1.00  ------ QBF
% 3.55/1.00  
% 3.55/1.00  qbf_q_res:                              0
% 3.55/1.00  qbf_num_tautologies:                    0
% 3.55/1.00  qbf_prep_cycles:                        0
% 3.55/1.00  
% 3.55/1.00  ------ BMC1
% 3.55/1.00  
% 3.55/1.00  bmc1_current_bound:                     -1
% 3.55/1.00  bmc1_last_solved_bound:                 -1
% 3.55/1.00  bmc1_unsat_core_size:                   -1
% 3.55/1.00  bmc1_unsat_core_parents_size:           -1
% 3.55/1.00  bmc1_merge_next_fun:                    0
% 3.55/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.55/1.00  
% 3.55/1.00  ------ Instantiation
% 3.55/1.00  
% 3.55/1.00  inst_num_of_clauses:                    1638
% 3.55/1.00  inst_num_in_passive:                    856
% 3.55/1.00  inst_num_in_active:                     636
% 3.55/1.00  inst_num_in_unprocessed:                146
% 3.55/1.00  inst_num_of_loops:                      670
% 3.55/1.00  inst_num_of_learning_restarts:          0
% 3.55/1.00  inst_num_moves_active_passive:          30
% 3.55/1.00  inst_lit_activity:                      0
% 3.55/1.00  inst_lit_activity_moves:                0
% 3.55/1.00  inst_num_tautologies:                   0
% 3.55/1.00  inst_num_prop_implied:                  0
% 3.55/1.00  inst_num_existing_simplified:           0
% 3.55/1.00  inst_num_eq_res_simplified:             0
% 3.55/1.00  inst_num_child_elim:                    0
% 3.55/1.00  inst_num_of_dismatching_blockings:      333
% 3.55/1.00  inst_num_of_non_proper_insts:           1517
% 3.55/1.00  inst_num_of_duplicates:                 0
% 3.55/1.00  inst_inst_num_from_inst_to_res:         0
% 3.55/1.00  inst_dismatching_checking_time:         0.
% 3.55/1.00  
% 3.55/1.00  ------ Resolution
% 3.55/1.00  
% 3.55/1.00  res_num_of_clauses:                     0
% 3.55/1.00  res_num_in_passive:                     0
% 3.55/1.00  res_num_in_active:                      0
% 3.55/1.00  res_num_of_loops:                       165
% 3.55/1.00  res_forward_subset_subsumed:            95
% 3.55/1.00  res_backward_subset_subsumed:           2
% 3.55/1.00  res_forward_subsumed:                   0
% 3.55/1.00  res_backward_subsumed:                  1
% 3.55/1.00  res_forward_subsumption_resolution:     2
% 3.55/1.00  res_backward_subsumption_resolution:    0
% 3.55/1.00  res_clause_to_clause_subsumption:       1279
% 3.55/1.00  res_orphan_elimination:                 0
% 3.55/1.00  res_tautology_del:                      74
% 3.55/1.00  res_num_eq_res_simplified:              0
% 3.55/1.00  res_num_sel_changes:                    0
% 3.55/1.00  res_moves_from_active_to_pass:          0
% 3.55/1.00  
% 3.55/1.00  ------ Superposition
% 3.55/1.00  
% 3.55/1.00  sup_time_total:                         0.
% 3.55/1.00  sup_time_generating:                    0.
% 3.55/1.00  sup_time_sim_full:                      0.
% 3.55/1.00  sup_time_sim_immed:                     0.
% 3.55/1.00  
% 3.55/1.00  sup_num_of_clauses:                     265
% 3.55/1.00  sup_num_in_active:                      113
% 3.55/1.00  sup_num_in_passive:                     152
% 3.55/1.00  sup_num_of_loops:                       132
% 3.55/1.00  sup_fw_superposition:                   177
% 3.55/1.00  sup_bw_superposition:                   97
% 3.55/1.00  sup_immediate_simplified:               80
% 3.55/1.00  sup_given_eliminated:                   2
% 3.55/1.00  comparisons_done:                       0
% 3.55/1.00  comparisons_avoided:                    0
% 3.55/1.00  
% 3.55/1.00  ------ Simplifications
% 3.55/1.00  
% 3.55/1.00  
% 3.55/1.00  sim_fw_subset_subsumed:                 2
% 3.55/1.00  sim_bw_subset_subsumed:                 29
% 3.55/1.00  sim_fw_subsumed:                        5
% 3.55/1.00  sim_bw_subsumed:                        2
% 3.55/1.00  sim_fw_subsumption_res:                 0
% 3.55/1.00  sim_bw_subsumption_res:                 0
% 3.55/1.00  sim_tautology_del:                      4
% 3.55/1.00  sim_eq_tautology_del:                   3
% 3.55/1.00  sim_eq_res_simp:                        1
% 3.55/1.00  sim_fw_demodulated:                     40
% 3.55/1.00  sim_bw_demodulated:                     4
% 3.55/1.00  sim_light_normalised:                   61
% 3.55/1.00  sim_joinable_taut:                      0
% 3.55/1.00  sim_joinable_simp:                      0
% 3.55/1.00  sim_ac_normalised:                      0
% 3.55/1.00  sim_smt_subsumption:                    0
% 3.55/1.00  
%------------------------------------------------------------------------------
