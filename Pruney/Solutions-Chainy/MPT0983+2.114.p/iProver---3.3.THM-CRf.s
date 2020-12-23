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
% DateTime   : Thu Dec  3 12:02:09 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :  186 ( 503 expanded)
%              Number of clauses        :  103 ( 159 expanded)
%              Number of leaves         :   24 ( 122 expanded)
%              Depth                    :   16
%              Number of atoms          :  584 (2843 expanded)
%              Number of equality atoms :  194 ( 266 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f54,plain,(
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

fof(f53,plain,
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

fof(f55,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f54,f53])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f55])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f90,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f55])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f36])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f93,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f55])).

fof(f19,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f82,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f81,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f95,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f72,f84])).

fof(f14,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f74,f84])).

fof(f22,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f85,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f91,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f48])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f79])).

fof(f94,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f99,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1196,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1199,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1202,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3661,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_1202])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_41,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_3808,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3661,c_41])).

cnf(c_3809,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3808])).

cnf(c_3817,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_3809])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_31,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_31])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_26,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_402,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_394,c_26])).

cnf(c_1193,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1257,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_1597,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1193,c_37,c_35,c_34,c_32,c_402,c_1257])).

cnf(c_3819,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3817,c_1597])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3922,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3819,c_38])).

cnf(c_14,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1208,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3924,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3922,c_1208])).

cnf(c_15,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_3925,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3924,c_15])).

cnf(c_17,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1207,plain,
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
    inference(cnf_transformation,[],[f85])).

cnf(c_1200,plain,
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

cnf(c_3302,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1597,c_1200])).

cnf(c_36,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_42,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_82,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_84,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_82])).

cnf(c_8,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_101,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_103,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_101])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_117,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_695,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1270,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_1271,plain,
    ( sK2 != X0
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1270])).

cnf(c_1273,plain,
    ( sK2 != k1_xboole_0
    | v2_funct_1(sK2) = iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1271])).

cnf(c_1329,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_695])).

cnf(c_1330,plain,
    ( X0 != k6_partfun1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1329])).

cnf(c_1332,plain,
    ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1330])).

cnf(c_6,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1474,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k6_partfun1(X1))
    | X0 = k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1475,plain,
    ( X0 = k6_partfun1(X1)
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1474])).

cnf(c_1477,plain,
    ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
    | v1_xboole_0(k6_partfun1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1475])).

cnf(c_1583,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK2)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1585,plain,
    ( ~ v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1583])).

cnf(c_686,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2318,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_2320,plain,
    ( v1_xboole_0(sK0)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2318])).

cnf(c_1203,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1211,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3360,plain,
    ( v1_xboole_0(k2_zfmisc_1(X0,X0)) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_1211])).

cnf(c_3364,plain,
    ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3360])).

cnf(c_1212,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3362,plain,
    ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1211])).

cnf(c_3472,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1212,c_3362])).

cnf(c_3474,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(sK0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3472])).

cnf(c_3563,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3302,c_38,c_39,c_40,c_41,c_42,c_43,c_84,c_103,c_0,c_117,c_1273,c_1332,c_1477,c_1585,c_2320,c_3364,c_3474])).

cnf(c_3567,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_3563])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1209,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1210,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2430,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1210])).

cnf(c_2801,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_2430])).

cnf(c_2429,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_1210])).

cnf(c_2597,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1209,c_2429])).

cnf(c_19,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_432,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_12])).

cnf(c_1192,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_432])).

cnf(c_2325,plain,
    ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1199,c_1192])).

cnf(c_2,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1217,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2434,plain,
    ( k2_relat_1(sK3) = sK0
    | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2325,c_1217])).

cnf(c_11,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_22,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_30,negated_conjecture,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_411,plain,
    ( ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_412,plain,
    ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_411])).

cnf(c_465,plain,
    ( ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != X1
    | k2_relat_1(sK3) != sK0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_412])).

cnf(c_466,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_476,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_466,c_3])).

cnf(c_477,plain,
    ( k2_relat_1(sK3) != sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3925,c_3567,c_2801,c_2597,c_2434,c_477])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:05:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.41/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.00  
% 3.41/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.41/1.00  
% 3.41/1.00  ------  iProver source info
% 3.41/1.00  
% 3.41/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.41/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.41/1.00  git: non_committed_changes: false
% 3.41/1.00  git: last_make_outside_of_git: false
% 3.41/1.00  
% 3.41/1.00  ------ 
% 3.41/1.00  
% 3.41/1.00  ------ Input Options
% 3.41/1.00  
% 3.41/1.00  --out_options                           all
% 3.41/1.00  --tptp_safe_out                         true
% 3.41/1.00  --problem_path                          ""
% 3.41/1.00  --include_path                          ""
% 3.41/1.00  --clausifier                            res/vclausify_rel
% 3.41/1.00  --clausifier_options                    ""
% 3.41/1.00  --stdin                                 false
% 3.41/1.00  --stats_out                             all
% 3.41/1.00  
% 3.41/1.00  ------ General Options
% 3.41/1.00  
% 3.41/1.00  --fof                                   false
% 3.41/1.00  --time_out_real                         305.
% 3.41/1.00  --time_out_virtual                      -1.
% 3.41/1.00  --symbol_type_check                     false
% 3.41/1.00  --clausify_out                          false
% 3.41/1.00  --sig_cnt_out                           false
% 3.41/1.00  --trig_cnt_out                          false
% 3.41/1.00  --trig_cnt_out_tolerance                1.
% 3.41/1.00  --trig_cnt_out_sk_spl                   false
% 3.41/1.00  --abstr_cl_out                          false
% 3.41/1.00  
% 3.41/1.00  ------ Global Options
% 3.41/1.00  
% 3.41/1.00  --schedule                              default
% 3.41/1.00  --add_important_lit                     false
% 3.41/1.00  --prop_solver_per_cl                    1000
% 3.41/1.00  --min_unsat_core                        false
% 3.41/1.00  --soft_assumptions                      false
% 3.41/1.00  --soft_lemma_size                       3
% 3.41/1.00  --prop_impl_unit_size                   0
% 3.41/1.00  --prop_impl_unit                        []
% 3.41/1.00  --share_sel_clauses                     true
% 3.41/1.00  --reset_solvers                         false
% 3.41/1.00  --bc_imp_inh                            [conj_cone]
% 3.41/1.00  --conj_cone_tolerance                   3.
% 3.41/1.00  --extra_neg_conj                        none
% 3.41/1.00  --large_theory_mode                     true
% 3.41/1.00  --prolific_symb_bound                   200
% 3.41/1.00  --lt_threshold                          2000
% 3.41/1.00  --clause_weak_htbl                      true
% 3.41/1.00  --gc_record_bc_elim                     false
% 3.41/1.00  
% 3.41/1.00  ------ Preprocessing Options
% 3.41/1.00  
% 3.41/1.00  --preprocessing_flag                    true
% 3.41/1.00  --time_out_prep_mult                    0.1
% 3.41/1.00  --splitting_mode                        input
% 3.41/1.00  --splitting_grd                         true
% 3.41/1.00  --splitting_cvd                         false
% 3.41/1.00  --splitting_cvd_svl                     false
% 3.41/1.00  --splitting_nvd                         32
% 3.41/1.00  --sub_typing                            true
% 3.41/1.00  --prep_gs_sim                           true
% 3.41/1.00  --prep_unflatten                        true
% 3.41/1.00  --prep_res_sim                          true
% 3.41/1.00  --prep_upred                            true
% 3.41/1.00  --prep_sem_filter                       exhaustive
% 3.41/1.00  --prep_sem_filter_out                   false
% 3.41/1.00  --pred_elim                             true
% 3.41/1.00  --res_sim_input                         true
% 3.41/1.00  --eq_ax_congr_red                       true
% 3.41/1.00  --pure_diseq_elim                       true
% 3.41/1.00  --brand_transform                       false
% 3.41/1.00  --non_eq_to_eq                          false
% 3.41/1.00  --prep_def_merge                        true
% 3.41/1.00  --prep_def_merge_prop_impl              false
% 3.41/1.00  --prep_def_merge_mbd                    true
% 3.41/1.00  --prep_def_merge_tr_red                 false
% 3.41/1.00  --prep_def_merge_tr_cl                  false
% 3.41/1.00  --smt_preprocessing                     true
% 3.41/1.00  --smt_ac_axioms                         fast
% 3.41/1.00  --preprocessed_out                      false
% 3.41/1.00  --preprocessed_stats                    false
% 3.41/1.00  
% 3.41/1.00  ------ Abstraction refinement Options
% 3.41/1.00  
% 3.41/1.00  --abstr_ref                             []
% 3.41/1.00  --abstr_ref_prep                        false
% 3.41/1.00  --abstr_ref_until_sat                   false
% 3.41/1.00  --abstr_ref_sig_restrict                funpre
% 3.41/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/1.00  --abstr_ref_under                       []
% 3.41/1.00  
% 3.41/1.00  ------ SAT Options
% 3.41/1.00  
% 3.41/1.00  --sat_mode                              false
% 3.41/1.00  --sat_fm_restart_options                ""
% 3.41/1.00  --sat_gr_def                            false
% 3.41/1.00  --sat_epr_types                         true
% 3.41/1.00  --sat_non_cyclic_types                  false
% 3.41/1.00  --sat_finite_models                     false
% 3.41/1.00  --sat_fm_lemmas                         false
% 3.41/1.00  --sat_fm_prep                           false
% 3.41/1.00  --sat_fm_uc_incr                        true
% 3.41/1.00  --sat_out_model                         small
% 3.41/1.00  --sat_out_clauses                       false
% 3.41/1.00  
% 3.41/1.00  ------ QBF Options
% 3.41/1.00  
% 3.41/1.00  --qbf_mode                              false
% 3.41/1.00  --qbf_elim_univ                         false
% 3.41/1.00  --qbf_dom_inst                          none
% 3.41/1.00  --qbf_dom_pre_inst                      false
% 3.41/1.00  --qbf_sk_in                             false
% 3.41/1.00  --qbf_pred_elim                         true
% 3.41/1.00  --qbf_split                             512
% 3.41/1.00  
% 3.41/1.00  ------ BMC1 Options
% 3.41/1.00  
% 3.41/1.00  --bmc1_incremental                      false
% 3.41/1.00  --bmc1_axioms                           reachable_all
% 3.41/1.00  --bmc1_min_bound                        0
% 3.41/1.00  --bmc1_max_bound                        -1
% 3.41/1.00  --bmc1_max_bound_default                -1
% 3.41/1.00  --bmc1_symbol_reachability              true
% 3.41/1.00  --bmc1_property_lemmas                  false
% 3.41/1.00  --bmc1_k_induction                      false
% 3.41/1.00  --bmc1_non_equiv_states                 false
% 3.41/1.00  --bmc1_deadlock                         false
% 3.41/1.00  --bmc1_ucm                              false
% 3.41/1.00  --bmc1_add_unsat_core                   none
% 3.41/1.00  --bmc1_unsat_core_children              false
% 3.41/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/1.00  --bmc1_out_stat                         full
% 3.41/1.00  --bmc1_ground_init                      false
% 3.41/1.00  --bmc1_pre_inst_next_state              false
% 3.41/1.00  --bmc1_pre_inst_state                   false
% 3.41/1.00  --bmc1_pre_inst_reach_state             false
% 3.41/1.00  --bmc1_out_unsat_core                   false
% 3.41/1.00  --bmc1_aig_witness_out                  false
% 3.41/1.00  --bmc1_verbose                          false
% 3.41/1.00  --bmc1_dump_clauses_tptp                false
% 3.41/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.41/1.00  --bmc1_dump_file                        -
% 3.41/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.41/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.41/1.00  --bmc1_ucm_extend_mode                  1
% 3.41/1.00  --bmc1_ucm_init_mode                    2
% 3.41/1.00  --bmc1_ucm_cone_mode                    none
% 3.41/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.41/1.00  --bmc1_ucm_relax_model                  4
% 3.41/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.41/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/1.00  --bmc1_ucm_layered_model                none
% 3.41/1.00  --bmc1_ucm_max_lemma_size               10
% 3.41/1.00  
% 3.41/1.00  ------ AIG Options
% 3.41/1.00  
% 3.41/1.00  --aig_mode                              false
% 3.41/1.00  
% 3.41/1.00  ------ Instantiation Options
% 3.41/1.00  
% 3.41/1.00  --instantiation_flag                    true
% 3.41/1.00  --inst_sos_flag                         true
% 3.41/1.00  --inst_sos_phase                        true
% 3.41/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/1.00  --inst_lit_sel_side                     num_symb
% 3.41/1.00  --inst_solver_per_active                1400
% 3.41/1.00  --inst_solver_calls_frac                1.
% 3.41/1.00  --inst_passive_queue_type               priority_queues
% 3.41/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/1.00  --inst_passive_queues_freq              [25;2]
% 3.41/1.00  --inst_dismatching                      true
% 3.41/1.00  --inst_eager_unprocessed_to_passive     true
% 3.41/1.00  --inst_prop_sim_given                   true
% 3.41/1.00  --inst_prop_sim_new                     false
% 3.41/1.00  --inst_subs_new                         false
% 3.41/1.00  --inst_eq_res_simp                      false
% 3.41/1.00  --inst_subs_given                       false
% 3.41/1.00  --inst_orphan_elimination               true
% 3.41/1.00  --inst_learning_loop_flag               true
% 3.41/1.00  --inst_learning_start                   3000
% 3.41/1.00  --inst_learning_factor                  2
% 3.41/1.00  --inst_start_prop_sim_after_learn       3
% 3.41/1.00  --inst_sel_renew                        solver
% 3.41/1.00  --inst_lit_activity_flag                true
% 3.41/1.00  --inst_restr_to_given                   false
% 3.41/1.00  --inst_activity_threshold               500
% 3.41/1.00  --inst_out_proof                        true
% 3.41/1.00  
% 3.41/1.00  ------ Resolution Options
% 3.41/1.00  
% 3.41/1.00  --resolution_flag                       true
% 3.41/1.00  --res_lit_sel                           adaptive
% 3.41/1.00  --res_lit_sel_side                      none
% 3.41/1.00  --res_ordering                          kbo
% 3.41/1.00  --res_to_prop_solver                    active
% 3.41/1.00  --res_prop_simpl_new                    false
% 3.41/1.00  --res_prop_simpl_given                  true
% 3.41/1.00  --res_passive_queue_type                priority_queues
% 3.41/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/1.00  --res_passive_queues_freq               [15;5]
% 3.41/1.00  --res_forward_subs                      full
% 3.41/1.00  --res_backward_subs                     full
% 3.41/1.00  --res_forward_subs_resolution           true
% 3.41/1.00  --res_backward_subs_resolution          true
% 3.41/1.00  --res_orphan_elimination                true
% 3.41/1.00  --res_time_limit                        2.
% 3.41/1.00  --res_out_proof                         true
% 3.41/1.00  
% 3.41/1.00  ------ Superposition Options
% 3.41/1.00  
% 3.41/1.00  --superposition_flag                    true
% 3.41/1.00  --sup_passive_queue_type                priority_queues
% 3.41/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.41/1.00  --demod_completeness_check              fast
% 3.41/1.00  --demod_use_ground                      true
% 3.41/1.00  --sup_to_prop_solver                    passive
% 3.41/1.00  --sup_prop_simpl_new                    true
% 3.41/1.00  --sup_prop_simpl_given                  true
% 3.41/1.00  --sup_fun_splitting                     true
% 3.41/1.00  --sup_smt_interval                      50000
% 3.41/1.00  
% 3.41/1.00  ------ Superposition Simplification Setup
% 3.41/1.00  
% 3.41/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.41/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.41/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.41/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.41/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.41/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.41/1.00  --sup_immed_triv                        [TrivRules]
% 3.41/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/1.00  --sup_immed_bw_main                     []
% 3.41/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.41/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/1.00  --sup_input_bw                          []
% 3.41/1.00  
% 3.41/1.00  ------ Combination Options
% 3.41/1.00  
% 3.41/1.00  --comb_res_mult                         3
% 3.41/1.00  --comb_sup_mult                         2
% 3.41/1.00  --comb_inst_mult                        10
% 3.41/1.00  
% 3.41/1.00  ------ Debug Options
% 3.41/1.00  
% 3.41/1.00  --dbg_backtrace                         false
% 3.41/1.00  --dbg_dump_prop_clauses                 false
% 3.41/1.00  --dbg_dump_prop_clauses_file            -
% 3.41/1.00  --dbg_out_stat                          false
% 3.41/1.00  ------ Parsing...
% 3.41/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.41/1.00  
% 3.41/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.41/1.00  
% 3.41/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.41/1.00  
% 3.41/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.41/1.00  ------ Proving...
% 3.41/1.00  ------ Problem Properties 
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  clauses                                 31
% 3.41/1.00  conjectures                             6
% 3.41/1.00  EPR                                     10
% 3.41/1.00  Horn                                    30
% 3.41/1.00  unary                                   15
% 3.41/1.00  binary                                  4
% 3.41/1.00  lits                                    76
% 3.41/1.00  lits eq                                 9
% 3.41/1.00  fd_pure                                 0
% 3.41/1.00  fd_pseudo                               0
% 3.41/1.00  fd_cond                                 2
% 3.41/1.00  fd_pseudo_cond                          2
% 3.41/1.00  AC symbols                              0
% 3.41/1.00  
% 3.41/1.00  ------ Schedule dynamic 5 is on 
% 3.41/1.00  
% 3.41/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  ------ 
% 3.41/1.00  Current options:
% 3.41/1.00  ------ 
% 3.41/1.00  
% 3.41/1.00  ------ Input Options
% 3.41/1.00  
% 3.41/1.00  --out_options                           all
% 3.41/1.00  --tptp_safe_out                         true
% 3.41/1.00  --problem_path                          ""
% 3.41/1.00  --include_path                          ""
% 3.41/1.00  --clausifier                            res/vclausify_rel
% 3.41/1.00  --clausifier_options                    ""
% 3.41/1.00  --stdin                                 false
% 3.41/1.00  --stats_out                             all
% 3.41/1.00  
% 3.41/1.00  ------ General Options
% 3.41/1.00  
% 3.41/1.00  --fof                                   false
% 3.41/1.00  --time_out_real                         305.
% 3.41/1.00  --time_out_virtual                      -1.
% 3.41/1.00  --symbol_type_check                     false
% 3.41/1.00  --clausify_out                          false
% 3.41/1.00  --sig_cnt_out                           false
% 3.41/1.00  --trig_cnt_out                          false
% 3.41/1.00  --trig_cnt_out_tolerance                1.
% 3.41/1.00  --trig_cnt_out_sk_spl                   false
% 3.41/1.00  --abstr_cl_out                          false
% 3.41/1.00  
% 3.41/1.00  ------ Global Options
% 3.41/1.00  
% 3.41/1.00  --schedule                              default
% 3.41/1.00  --add_important_lit                     false
% 3.41/1.00  --prop_solver_per_cl                    1000
% 3.41/1.00  --min_unsat_core                        false
% 3.41/1.00  --soft_assumptions                      false
% 3.41/1.00  --soft_lemma_size                       3
% 3.41/1.00  --prop_impl_unit_size                   0
% 3.41/1.00  --prop_impl_unit                        []
% 3.41/1.00  --share_sel_clauses                     true
% 3.41/1.00  --reset_solvers                         false
% 3.41/1.00  --bc_imp_inh                            [conj_cone]
% 3.41/1.00  --conj_cone_tolerance                   3.
% 3.41/1.00  --extra_neg_conj                        none
% 3.41/1.00  --large_theory_mode                     true
% 3.41/1.00  --prolific_symb_bound                   200
% 3.41/1.00  --lt_threshold                          2000
% 3.41/1.00  --clause_weak_htbl                      true
% 3.41/1.00  --gc_record_bc_elim                     false
% 3.41/1.00  
% 3.41/1.00  ------ Preprocessing Options
% 3.41/1.00  
% 3.41/1.00  --preprocessing_flag                    true
% 3.41/1.00  --time_out_prep_mult                    0.1
% 3.41/1.00  --splitting_mode                        input
% 3.41/1.00  --splitting_grd                         true
% 3.41/1.00  --splitting_cvd                         false
% 3.41/1.00  --splitting_cvd_svl                     false
% 3.41/1.00  --splitting_nvd                         32
% 3.41/1.00  --sub_typing                            true
% 3.41/1.00  --prep_gs_sim                           true
% 3.41/1.00  --prep_unflatten                        true
% 3.41/1.00  --prep_res_sim                          true
% 3.41/1.00  --prep_upred                            true
% 3.41/1.00  --prep_sem_filter                       exhaustive
% 3.41/1.00  --prep_sem_filter_out                   false
% 3.41/1.00  --pred_elim                             true
% 3.41/1.00  --res_sim_input                         true
% 3.41/1.00  --eq_ax_congr_red                       true
% 3.41/1.00  --pure_diseq_elim                       true
% 3.41/1.00  --brand_transform                       false
% 3.41/1.00  --non_eq_to_eq                          false
% 3.41/1.00  --prep_def_merge                        true
% 3.41/1.00  --prep_def_merge_prop_impl              false
% 3.41/1.00  --prep_def_merge_mbd                    true
% 3.41/1.00  --prep_def_merge_tr_red                 false
% 3.41/1.00  --prep_def_merge_tr_cl                  false
% 3.41/1.00  --smt_preprocessing                     true
% 3.41/1.00  --smt_ac_axioms                         fast
% 3.41/1.00  --preprocessed_out                      false
% 3.41/1.00  --preprocessed_stats                    false
% 3.41/1.00  
% 3.41/1.00  ------ Abstraction refinement Options
% 3.41/1.00  
% 3.41/1.00  --abstr_ref                             []
% 3.41/1.00  --abstr_ref_prep                        false
% 3.41/1.00  --abstr_ref_until_sat                   false
% 3.41/1.00  --abstr_ref_sig_restrict                funpre
% 3.41/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.41/1.00  --abstr_ref_under                       []
% 3.41/1.00  
% 3.41/1.00  ------ SAT Options
% 3.41/1.00  
% 3.41/1.00  --sat_mode                              false
% 3.41/1.00  --sat_fm_restart_options                ""
% 3.41/1.00  --sat_gr_def                            false
% 3.41/1.00  --sat_epr_types                         true
% 3.41/1.00  --sat_non_cyclic_types                  false
% 3.41/1.00  --sat_finite_models                     false
% 3.41/1.00  --sat_fm_lemmas                         false
% 3.41/1.00  --sat_fm_prep                           false
% 3.41/1.00  --sat_fm_uc_incr                        true
% 3.41/1.00  --sat_out_model                         small
% 3.41/1.00  --sat_out_clauses                       false
% 3.41/1.00  
% 3.41/1.00  ------ QBF Options
% 3.41/1.00  
% 3.41/1.00  --qbf_mode                              false
% 3.41/1.00  --qbf_elim_univ                         false
% 3.41/1.00  --qbf_dom_inst                          none
% 3.41/1.00  --qbf_dom_pre_inst                      false
% 3.41/1.00  --qbf_sk_in                             false
% 3.41/1.00  --qbf_pred_elim                         true
% 3.41/1.00  --qbf_split                             512
% 3.41/1.00  
% 3.41/1.00  ------ BMC1 Options
% 3.41/1.00  
% 3.41/1.00  --bmc1_incremental                      false
% 3.41/1.00  --bmc1_axioms                           reachable_all
% 3.41/1.00  --bmc1_min_bound                        0
% 3.41/1.00  --bmc1_max_bound                        -1
% 3.41/1.00  --bmc1_max_bound_default                -1
% 3.41/1.00  --bmc1_symbol_reachability              true
% 3.41/1.00  --bmc1_property_lemmas                  false
% 3.41/1.00  --bmc1_k_induction                      false
% 3.41/1.00  --bmc1_non_equiv_states                 false
% 3.41/1.00  --bmc1_deadlock                         false
% 3.41/1.00  --bmc1_ucm                              false
% 3.41/1.00  --bmc1_add_unsat_core                   none
% 3.41/1.00  --bmc1_unsat_core_children              false
% 3.41/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.41/1.00  --bmc1_out_stat                         full
% 3.41/1.00  --bmc1_ground_init                      false
% 3.41/1.00  --bmc1_pre_inst_next_state              false
% 3.41/1.00  --bmc1_pre_inst_state                   false
% 3.41/1.00  --bmc1_pre_inst_reach_state             false
% 3.41/1.00  --bmc1_out_unsat_core                   false
% 3.41/1.00  --bmc1_aig_witness_out                  false
% 3.41/1.00  --bmc1_verbose                          false
% 3.41/1.00  --bmc1_dump_clauses_tptp                false
% 3.41/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.41/1.00  --bmc1_dump_file                        -
% 3.41/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.41/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.41/1.00  --bmc1_ucm_extend_mode                  1
% 3.41/1.00  --bmc1_ucm_init_mode                    2
% 3.41/1.00  --bmc1_ucm_cone_mode                    none
% 3.41/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.41/1.00  --bmc1_ucm_relax_model                  4
% 3.41/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.41/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.41/1.00  --bmc1_ucm_layered_model                none
% 3.41/1.00  --bmc1_ucm_max_lemma_size               10
% 3.41/1.00  
% 3.41/1.00  ------ AIG Options
% 3.41/1.00  
% 3.41/1.00  --aig_mode                              false
% 3.41/1.00  
% 3.41/1.00  ------ Instantiation Options
% 3.41/1.00  
% 3.41/1.00  --instantiation_flag                    true
% 3.41/1.00  --inst_sos_flag                         true
% 3.41/1.00  --inst_sos_phase                        true
% 3.41/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.41/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.41/1.00  --inst_lit_sel_side                     none
% 3.41/1.00  --inst_solver_per_active                1400
% 3.41/1.00  --inst_solver_calls_frac                1.
% 3.41/1.00  --inst_passive_queue_type               priority_queues
% 3.41/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.41/1.00  --inst_passive_queues_freq              [25;2]
% 3.41/1.00  --inst_dismatching                      true
% 3.41/1.00  --inst_eager_unprocessed_to_passive     true
% 3.41/1.00  --inst_prop_sim_given                   true
% 3.41/1.00  --inst_prop_sim_new                     false
% 3.41/1.00  --inst_subs_new                         false
% 3.41/1.00  --inst_eq_res_simp                      false
% 3.41/1.00  --inst_subs_given                       false
% 3.41/1.00  --inst_orphan_elimination               true
% 3.41/1.00  --inst_learning_loop_flag               true
% 3.41/1.00  --inst_learning_start                   3000
% 3.41/1.00  --inst_learning_factor                  2
% 3.41/1.00  --inst_start_prop_sim_after_learn       3
% 3.41/1.00  --inst_sel_renew                        solver
% 3.41/1.00  --inst_lit_activity_flag                true
% 3.41/1.00  --inst_restr_to_given                   false
% 3.41/1.00  --inst_activity_threshold               500
% 3.41/1.00  --inst_out_proof                        true
% 3.41/1.00  
% 3.41/1.00  ------ Resolution Options
% 3.41/1.00  
% 3.41/1.00  --resolution_flag                       false
% 3.41/1.00  --res_lit_sel                           adaptive
% 3.41/1.00  --res_lit_sel_side                      none
% 3.41/1.00  --res_ordering                          kbo
% 3.41/1.00  --res_to_prop_solver                    active
% 3.41/1.00  --res_prop_simpl_new                    false
% 3.41/1.00  --res_prop_simpl_given                  true
% 3.41/1.00  --res_passive_queue_type                priority_queues
% 3.41/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.41/1.00  --res_passive_queues_freq               [15;5]
% 3.41/1.00  --res_forward_subs                      full
% 3.41/1.00  --res_backward_subs                     full
% 3.41/1.00  --res_forward_subs_resolution           true
% 3.41/1.00  --res_backward_subs_resolution          true
% 3.41/1.00  --res_orphan_elimination                true
% 3.41/1.00  --res_time_limit                        2.
% 3.41/1.00  --res_out_proof                         true
% 3.41/1.00  
% 3.41/1.00  ------ Superposition Options
% 3.41/1.00  
% 3.41/1.00  --superposition_flag                    true
% 3.41/1.00  --sup_passive_queue_type                priority_queues
% 3.41/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.41/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.41/1.00  --demod_completeness_check              fast
% 3.41/1.00  --demod_use_ground                      true
% 3.41/1.00  --sup_to_prop_solver                    passive
% 3.41/1.00  --sup_prop_simpl_new                    true
% 3.41/1.00  --sup_prop_simpl_given                  true
% 3.41/1.00  --sup_fun_splitting                     true
% 3.41/1.00  --sup_smt_interval                      50000
% 3.41/1.00  
% 3.41/1.00  ------ Superposition Simplification Setup
% 3.41/1.00  
% 3.41/1.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.41/1.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.41/1.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.41/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.41/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.41/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.41/1.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.41/1.00  --sup_immed_triv                        [TrivRules]
% 3.41/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/1.00  --sup_immed_bw_main                     []
% 3.41/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.41/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.41/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.41/1.00  --sup_input_bw                          []
% 3.41/1.00  
% 3.41/1.00  ------ Combination Options
% 3.41/1.00  
% 3.41/1.00  --comb_res_mult                         3
% 3.41/1.00  --comb_sup_mult                         2
% 3.41/1.00  --comb_inst_mult                        10
% 3.41/1.00  
% 3.41/1.00  ------ Debug Options
% 3.41/1.00  
% 3.41/1.00  --dbg_backtrace                         false
% 3.41/1.00  --dbg_dump_prop_clauses                 false
% 3.41/1.00  --dbg_dump_prop_clauses_file            -
% 3.41/1.00  --dbg_out_stat                          false
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  ------ Proving...
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  % SZS status Theorem for theBenchmark.p
% 3.41/1.00  
% 3.41/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.41/1.00  
% 3.41/1.00  fof(f23,conjecture,(
% 3.41/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f24,negated_conjecture,(
% 3.41/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 3.41/1.00    inference(negated_conjecture,[],[f23])).
% 3.41/1.00  
% 3.41/1.00  fof(f46,plain,(
% 3.41/1.00    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.41/1.00    inference(ennf_transformation,[],[f24])).
% 3.41/1.00  
% 3.41/1.00  fof(f47,plain,(
% 3.41/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.41/1.00    inference(flattening,[],[f46])).
% 3.41/1.00  
% 3.41/1.00  fof(f54,plain,(
% 3.41/1.00    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.41/1.00    introduced(choice_axiom,[])).
% 3.41/1.00  
% 3.41/1.00  fof(f53,plain,(
% 3.41/1.00    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.41/1.00    introduced(choice_axiom,[])).
% 3.41/1.00  
% 3.41/1.00  fof(f55,plain,(
% 3.41/1.00    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.41/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f54,f53])).
% 3.41/1.00  
% 3.41/1.00  fof(f89,plain,(
% 3.41/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.41/1.00    inference(cnf_transformation,[],[f55])).
% 3.41/1.00  
% 3.41/1.00  fof(f92,plain,(
% 3.41/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.41/1.00    inference(cnf_transformation,[],[f55])).
% 3.41/1.00  
% 3.41/1.00  fof(f20,axiom,(
% 3.41/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f42,plain,(
% 3.41/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.41/1.00    inference(ennf_transformation,[],[f20])).
% 3.41/1.00  
% 3.41/1.00  fof(f43,plain,(
% 3.41/1.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.41/1.00    inference(flattening,[],[f42])).
% 3.41/1.00  
% 3.41/1.00  fof(f83,plain,(
% 3.41/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f43])).
% 3.41/1.00  
% 3.41/1.00  fof(f90,plain,(
% 3.41/1.00    v1_funct_1(sK3)),
% 3.41/1.00    inference(cnf_transformation,[],[f55])).
% 3.41/1.00  
% 3.41/1.00  fof(f16,axiom,(
% 3.41/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f36,plain,(
% 3.41/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.41/1.00    inference(ennf_transformation,[],[f16])).
% 3.41/1.00  
% 3.41/1.00  fof(f37,plain,(
% 3.41/1.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/1.00    inference(flattening,[],[f36])).
% 3.41/1.00  
% 3.41/1.00  fof(f51,plain,(
% 3.41/1.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/1.00    inference(nnf_transformation,[],[f37])).
% 3.41/1.00  
% 3.41/1.00  fof(f76,plain,(
% 3.41/1.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.41/1.00    inference(cnf_transformation,[],[f51])).
% 3.41/1.00  
% 3.41/1.00  fof(f93,plain,(
% 3.41/1.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.41/1.00    inference(cnf_transformation,[],[f55])).
% 3.41/1.00  
% 3.41/1.00  fof(f19,axiom,(
% 3.41/1.00    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f25,plain,(
% 3.41/1.00    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.41/1.00    inference(pure_predicate_removal,[],[f19])).
% 3.41/1.00  
% 3.41/1.00  fof(f82,plain,(
% 3.41/1.00    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.41/1.00    inference(cnf_transformation,[],[f25])).
% 3.41/1.00  
% 3.41/1.00  fof(f87,plain,(
% 3.41/1.00    v1_funct_1(sK2)),
% 3.41/1.00    inference(cnf_transformation,[],[f55])).
% 3.41/1.00  
% 3.41/1.00  fof(f18,axiom,(
% 3.41/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f40,plain,(
% 3.41/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.41/1.00    inference(ennf_transformation,[],[f18])).
% 3.41/1.00  
% 3.41/1.00  fof(f41,plain,(
% 3.41/1.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.41/1.00    inference(flattening,[],[f40])).
% 3.41/1.00  
% 3.41/1.00  fof(f81,plain,(
% 3.41/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f41])).
% 3.41/1.00  
% 3.41/1.00  fof(f12,axiom,(
% 3.41/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f34,plain,(
% 3.41/1.00    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.41/1.00    inference(ennf_transformation,[],[f12])).
% 3.41/1.00  
% 3.41/1.00  fof(f70,plain,(
% 3.41/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f34])).
% 3.41/1.00  
% 3.41/1.00  fof(f13,axiom,(
% 3.41/1.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f72,plain,(
% 3.41/1.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.41/1.00    inference(cnf_transformation,[],[f13])).
% 3.41/1.00  
% 3.41/1.00  fof(f21,axiom,(
% 3.41/1.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f84,plain,(
% 3.41/1.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f21])).
% 3.41/1.00  
% 3.41/1.00  fof(f95,plain,(
% 3.41/1.00    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.41/1.00    inference(definition_unfolding,[],[f72,f84])).
% 3.41/1.00  
% 3.41/1.00  fof(f14,axiom,(
% 3.41/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f74,plain,(
% 3.41/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.41/1.00    inference(cnf_transformation,[],[f14])).
% 3.41/1.00  
% 3.41/1.00  fof(f97,plain,(
% 3.41/1.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.41/1.00    inference(definition_unfolding,[],[f74,f84])).
% 3.41/1.00  
% 3.41/1.00  fof(f22,axiom,(
% 3.41/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f44,plain,(
% 3.41/1.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.41/1.00    inference(ennf_transformation,[],[f22])).
% 3.41/1.00  
% 3.41/1.00  fof(f45,plain,(
% 3.41/1.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.41/1.00    inference(flattening,[],[f44])).
% 3.41/1.00  
% 3.41/1.00  fof(f85,plain,(
% 3.41/1.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f45])).
% 3.41/1.00  
% 3.41/1.00  fof(f88,plain,(
% 3.41/1.00    v1_funct_2(sK2,sK0,sK1)),
% 3.41/1.00    inference(cnf_transformation,[],[f55])).
% 3.41/1.00  
% 3.41/1.00  fof(f91,plain,(
% 3.41/1.00    v1_funct_2(sK3,sK1,sK0)),
% 3.41/1.00    inference(cnf_transformation,[],[f55])).
% 3.41/1.00  
% 3.41/1.00  fof(f7,axiom,(
% 3.41/1.00    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f30,plain,(
% 3.41/1.00    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.41/1.00    inference(ennf_transformation,[],[f7])).
% 3.41/1.00  
% 3.41/1.00  fof(f64,plain,(
% 3.41/1.00    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f30])).
% 3.41/1.00  
% 3.41/1.00  fof(f1,axiom,(
% 3.41/1.00    v1_xboole_0(k1_xboole_0)),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f56,plain,(
% 3.41/1.00    v1_xboole_0(k1_xboole_0)),
% 3.41/1.00    inference(cnf_transformation,[],[f1])).
% 3.41/1.00  
% 3.41/1.00  fof(f5,axiom,(
% 3.41/1.00    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f28,plain,(
% 3.41/1.00    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.41/1.00    inference(ennf_transformation,[],[f5])).
% 3.41/1.00  
% 3.41/1.00  fof(f62,plain,(
% 3.41/1.00    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f28])).
% 3.41/1.00  
% 3.41/1.00  fof(f8,axiom,(
% 3.41/1.00    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f31,plain,(
% 3.41/1.00    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 3.41/1.00    inference(ennf_transformation,[],[f8])).
% 3.41/1.00  
% 3.41/1.00  fof(f65,plain,(
% 3.41/1.00    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f31])).
% 3.41/1.00  
% 3.41/1.00  fof(f11,axiom,(
% 3.41/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f69,plain,(
% 3.41/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.41/1.00    inference(cnf_transformation,[],[f11])).
% 3.41/1.00  
% 3.41/1.00  fof(f9,axiom,(
% 3.41/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f32,plain,(
% 3.41/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.41/1.00    inference(ennf_transformation,[],[f9])).
% 3.41/1.00  
% 3.41/1.00  fof(f66,plain,(
% 3.41/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f32])).
% 3.41/1.00  
% 3.41/1.00  fof(f15,axiom,(
% 3.41/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f26,plain,(
% 3.41/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.41/1.00    inference(pure_predicate_removal,[],[f15])).
% 3.41/1.00  
% 3.41/1.00  fof(f35,plain,(
% 3.41/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.41/1.00    inference(ennf_transformation,[],[f26])).
% 3.41/1.00  
% 3.41/1.00  fof(f75,plain,(
% 3.41/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.41/1.00    inference(cnf_transformation,[],[f35])).
% 3.41/1.00  
% 3.41/1.00  fof(f10,axiom,(
% 3.41/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f33,plain,(
% 3.41/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.41/1.00    inference(ennf_transformation,[],[f10])).
% 3.41/1.00  
% 3.41/1.00  fof(f50,plain,(
% 3.41/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.41/1.00    inference(nnf_transformation,[],[f33])).
% 3.41/1.00  
% 3.41/1.00  fof(f67,plain,(
% 3.41/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f50])).
% 3.41/1.00  
% 3.41/1.00  fof(f3,axiom,(
% 3.41/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f48,plain,(
% 3.41/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.41/1.00    inference(nnf_transformation,[],[f3])).
% 3.41/1.00  
% 3.41/1.00  fof(f49,plain,(
% 3.41/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.41/1.00    inference(flattening,[],[f48])).
% 3.41/1.00  
% 3.41/1.00  fof(f60,plain,(
% 3.41/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f49])).
% 3.41/1.00  
% 3.41/1.00  fof(f68,plain,(
% 3.41/1.00    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f50])).
% 3.41/1.00  
% 3.41/1.00  fof(f17,axiom,(
% 3.41/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 3.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.41/1.00  
% 3.41/1.00  fof(f38,plain,(
% 3.41/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.41/1.00    inference(ennf_transformation,[],[f17])).
% 3.41/1.00  
% 3.41/1.00  fof(f39,plain,(
% 3.41/1.00    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.41/1.00    inference(flattening,[],[f38])).
% 3.41/1.00  
% 3.41/1.00  fof(f52,plain,(
% 3.41/1.00    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.41/1.00    inference(nnf_transformation,[],[f39])).
% 3.41/1.00  
% 3.41/1.00  fof(f79,plain,(
% 3.41/1.00    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.41/1.00    inference(cnf_transformation,[],[f52])).
% 3.41/1.00  
% 3.41/1.00  fof(f102,plain,(
% 3.41/1.00    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 3.41/1.00    inference(equality_resolution,[],[f79])).
% 3.41/1.00  
% 3.41/1.00  fof(f94,plain,(
% 3.41/1.00    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 3.41/1.00    inference(cnf_transformation,[],[f55])).
% 3.41/1.00  
% 3.41/1.00  fof(f59,plain,(
% 3.41/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.41/1.00    inference(cnf_transformation,[],[f49])).
% 3.41/1.00  
% 3.41/1.00  fof(f99,plain,(
% 3.41/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.41/1.00    inference(equality_resolution,[],[f59])).
% 3.41/1.00  
% 3.41/1.00  cnf(c_35,negated_conjecture,
% 3.41/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.41/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1196,plain,
% 3.41/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_32,negated_conjecture,
% 3.41/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.41/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1199,plain,
% 3.41/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_27,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.41/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.41/1.00      | ~ v1_funct_1(X0)
% 3.41/1.00      | ~ v1_funct_1(X3)
% 3.41/1.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1202,plain,
% 3.41/1.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.41/1.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.41/1.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.41/1.00      | v1_funct_1(X5) != iProver_top
% 3.41/1.00      | v1_funct_1(X4) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3661,plain,
% 3.41/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.41/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.41/1.00      | v1_funct_1(X2) != iProver_top
% 3.41/1.00      | v1_funct_1(sK3) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1199,c_1202]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_34,negated_conjecture,
% 3.41/1.00      ( v1_funct_1(sK3) ),
% 3.41/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_41,plain,
% 3.41/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3808,plain,
% 3.41/1.00      ( v1_funct_1(X2) != iProver_top
% 3.41/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.41/1.00      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.41/1.00      inference(global_propositional_subsumption,
% 3.41/1.00                [status(thm)],
% 3.41/1.00                [c_3661,c_41]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3809,plain,
% 3.41/1.00      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.41/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.41/1.00      | v1_funct_1(X2) != iProver_top ),
% 3.41/1.00      inference(renaming,[status(thm)],[c_3808]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3817,plain,
% 3.41/1.00      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.41/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1196,c_3809]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_21,plain,
% 3.41/1.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.41/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.41/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.41/1.00      | X3 = X2 ),
% 3.41/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_31,negated_conjecture,
% 3.41/1.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.41/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_393,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.41/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.41/1.00      | X3 = X0
% 3.41/1.00      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.41/1.00      | k6_partfun1(sK0) != X3
% 3.41/1.00      | sK0 != X2
% 3.41/1.00      | sK0 != X1 ),
% 3.41/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_31]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_394,plain,
% 3.41/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.41/1.00      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.41/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.41/1.00      inference(unflattening,[status(thm)],[c_393]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_26,plain,
% 3.41/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.41/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_402,plain,
% 3.41/1.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.41/1.00      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.41/1.00      inference(forward_subsumption_resolution,
% 3.41/1.00                [status(thm)],
% 3.41/1.00                [c_394,c_26]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1193,plain,
% 3.41/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.41/1.00      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_37,negated_conjecture,
% 3.41/1.00      ( v1_funct_1(sK2) ),
% 3.41/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_24,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.41/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.41/1.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.41/1.00      | ~ v1_funct_1(X0)
% 3.41/1.00      | ~ v1_funct_1(X3) ),
% 3.41/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1257,plain,
% 3.41/1.00      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.41/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.41/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.41/1.00      | ~ v1_funct_1(sK2)
% 3.41/1.00      | ~ v1_funct_1(sK3) ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_24]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1597,plain,
% 3.41/1.00      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.41/1.00      inference(global_propositional_subsumption,
% 3.41/1.00                [status(thm)],
% 3.41/1.00                [c_1193,c_37,c_35,c_34,c_32,c_402,c_1257]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3819,plain,
% 3.41/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.41/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.41/1.00      inference(light_normalisation,[status(thm)],[c_3817,c_1597]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_38,plain,
% 3.41/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3922,plain,
% 3.41/1.00      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.41/1.00      inference(global_propositional_subsumption,
% 3.41/1.00                [status(thm)],
% 3.41/1.00                [c_3819,c_38]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_14,plain,
% 3.41/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 3.41/1.00      | ~ v1_relat_1(X0)
% 3.41/1.00      | ~ v1_relat_1(X1) ),
% 3.41/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1208,plain,
% 3.41/1.00      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 3.41/1.00      | v1_relat_1(X0) != iProver_top
% 3.41/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3924,plain,
% 3.41/1.00      ( r1_tarski(k2_relat_1(k6_partfun1(sK0)),k2_relat_1(sK3)) = iProver_top
% 3.41/1.00      | v1_relat_1(sK2) != iProver_top
% 3.41/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_3922,c_1208]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_15,plain,
% 3.41/1.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.41/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3925,plain,
% 3.41/1.00      ( r1_tarski(sK0,k2_relat_1(sK3)) = iProver_top
% 3.41/1.00      | v1_relat_1(sK2) != iProver_top
% 3.41/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.41/1.00      inference(demodulation,[status(thm)],[c_3924,c_15]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_17,plain,
% 3.41/1.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.41/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1207,plain,
% 3.41/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_29,plain,
% 3.41/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.41/1.00      | ~ v1_funct_2(X3,X4,X1)
% 3.41/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.41/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.41/1.00      | ~ v1_funct_1(X0)
% 3.41/1.00      | ~ v1_funct_1(X3)
% 3.41/1.00      | v2_funct_1(X3)
% 3.41/1.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.41/1.00      | k1_xboole_0 = X2 ),
% 3.41/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1200,plain,
% 3.41/1.00      ( k1_xboole_0 = X0
% 3.41/1.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.41/1.00      | v1_funct_2(X3,X4,X2) != iProver_top
% 3.41/1.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 3.41/1.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.41/1.00      | v1_funct_1(X1) != iProver_top
% 3.41/1.00      | v1_funct_1(X3) != iProver_top
% 3.41/1.00      | v2_funct_1(X3) = iProver_top
% 3.41/1.00      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3302,plain,
% 3.41/1.00      ( sK0 = k1_xboole_0
% 3.41/1.00      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.41/1.00      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.41/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.41/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.41/1.00      | v1_funct_1(sK2) != iProver_top
% 3.41/1.00      | v1_funct_1(sK3) != iProver_top
% 3.41/1.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.41/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1597,c_1200]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_36,negated_conjecture,
% 3.41/1.00      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.41/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_39,plain,
% 3.41/1.00      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_40,plain,
% 3.41/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_33,negated_conjecture,
% 3.41/1.00      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_42,plain,
% 3.41/1.00      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_43,plain,
% 3.41/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_82,plain,
% 3.41/1.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_84,plain,
% 3.41/1.00      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_82]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_8,plain,
% 3.41/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.41/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_101,plain,
% 3.41/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.41/1.00      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_103,plain,
% 3.41/1.00      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 3.41/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_101]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_0,plain,
% 3.41/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_117,plain,
% 3.41/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_695,plain,
% 3.41/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.41/1.00      theory(equality) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1270,plain,
% 3.41/1.00      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_695]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1271,plain,
% 3.41/1.00      ( sK2 != X0
% 3.41/1.00      | v2_funct_1(X0) != iProver_top
% 3.41/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_1270]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1273,plain,
% 3.41/1.00      ( sK2 != k1_xboole_0
% 3.41/1.00      | v2_funct_1(sK2) = iProver_top
% 3.41/1.00      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_1271]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1329,plain,
% 3.41/1.00      ( v2_funct_1(X0)
% 3.41/1.00      | ~ v2_funct_1(k6_partfun1(X1))
% 3.41/1.00      | X0 != k6_partfun1(X1) ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_695]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1330,plain,
% 3.41/1.00      ( X0 != k6_partfun1(X1)
% 3.41/1.00      | v2_funct_1(X0) = iProver_top
% 3.41/1.00      | v2_funct_1(k6_partfun1(X1)) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_1329]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1332,plain,
% 3.41/1.00      ( k1_xboole_0 != k6_partfun1(k1_xboole_0)
% 3.41/1.00      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.41/1.00      | v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_1330]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_6,plain,
% 3.41/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.41/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1474,plain,
% 3.41/1.00      ( ~ v1_xboole_0(X0)
% 3.41/1.00      | ~ v1_xboole_0(k6_partfun1(X1))
% 3.41/1.00      | X0 = k6_partfun1(X1) ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1475,plain,
% 3.41/1.00      ( X0 = k6_partfun1(X1)
% 3.41/1.00      | v1_xboole_0(X0) != iProver_top
% 3.41/1.00      | v1_xboole_0(k6_partfun1(X1)) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_1474]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1477,plain,
% 3.41/1.00      ( k1_xboole_0 = k6_partfun1(k1_xboole_0)
% 3.41/1.00      | v1_xboole_0(k6_partfun1(k1_xboole_0)) != iProver_top
% 3.41/1.00      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_1475]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1583,plain,
% 3.41/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK2) | sK2 = X0 ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1585,plain,
% 3.41/1.00      ( ~ v1_xboole_0(sK2)
% 3.41/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.41/1.00      | sK2 = k1_xboole_0 ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_1583]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_686,plain,
% 3.41/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.41/1.00      theory(equality) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2318,plain,
% 3.41/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK0) | sK0 != X0 ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_686]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2320,plain,
% 3.41/1.00      ( v1_xboole_0(sK0)
% 3.41/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.41/1.00      | sK0 != k1_xboole_0 ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_2318]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1203,plain,
% 3.41/1.00      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_9,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.41/1.00      | ~ v1_xboole_0(X1)
% 3.41/1.00      | v1_xboole_0(X0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1211,plain,
% 3.41/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.41/1.00      | v1_xboole_0(X1) != iProver_top
% 3.41/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3360,plain,
% 3.41/1.00      ( v1_xboole_0(k2_zfmisc_1(X0,X0)) != iProver_top
% 3.41/1.00      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1203,c_1211]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3364,plain,
% 3.41/1.00      ( v1_xboole_0(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.41/1.00      | v1_xboole_0(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 3.41/1.00      inference(instantiation,[status(thm)],[c_3360]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1212,plain,
% 3.41/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.41/1.00      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3362,plain,
% 3.41/1.00      ( v1_xboole_0(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.41/1.00      | v1_xboole_0(sK2) = iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1196,c_1211]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3472,plain,
% 3.41/1.00      ( v1_xboole_0(sK2) = iProver_top
% 3.41/1.00      | v1_xboole_0(sK0) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1212,c_3362]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3474,plain,
% 3.41/1.00      ( v1_xboole_0(sK2) | ~ v1_xboole_0(sK0) ),
% 3.41/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3472]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3563,plain,
% 3.41/1.00      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.41/1.00      | v2_funct_1(sK2) = iProver_top ),
% 3.41/1.00      inference(global_propositional_subsumption,
% 3.41/1.00                [status(thm)],
% 3.41/1.00                [c_3302,c_38,c_39,c_40,c_41,c_42,c_43,c_84,c_103,c_0,
% 3.41/1.00                 c_117,c_1273,c_1332,c_1477,c_1585,c_2320,c_3364,c_3474]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3567,plain,
% 3.41/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1207,c_3563]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_13,plain,
% 3.41/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.41/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1209,plain,
% 3.41/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_10,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.41/1.00      | ~ v1_relat_1(X1)
% 3.41/1.00      | v1_relat_1(X0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1210,plain,
% 3.41/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.41/1.00      | v1_relat_1(X1) != iProver_top
% 3.41/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2430,plain,
% 3.41/1.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 3.41/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1196,c_1210]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2801,plain,
% 3.41/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1209,c_2430]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2429,plain,
% 3.41/1.00      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 3.41/1.00      | v1_relat_1(sK3) = iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1199,c_1210]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2597,plain,
% 3.41/1.00      ( v1_relat_1(sK3) = iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1209,c_2429]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_19,plain,
% 3.41/1.00      ( v5_relat_1(X0,X1)
% 3.41/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.41/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_12,plain,
% 3.41/1.00      ( ~ v5_relat_1(X0,X1)
% 3.41/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.41/1.00      | ~ v1_relat_1(X0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_432,plain,
% 3.41/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.41/1.00      | r1_tarski(k2_relat_1(X0),X2)
% 3.41/1.00      | ~ v1_relat_1(X0) ),
% 3.41/1.00      inference(resolution,[status(thm)],[c_19,c_12]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1192,plain,
% 3.41/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.41/1.00      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.41/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_432]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2325,plain,
% 3.41/1.00      ( r1_tarski(k2_relat_1(sK3),sK0) = iProver_top
% 3.41/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_1199,c_1192]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2,plain,
% 3.41/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.41/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_1217,plain,
% 3.41/1.00      ( X0 = X1
% 3.41/1.00      | r1_tarski(X0,X1) != iProver_top
% 3.41/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_2434,plain,
% 3.41/1.00      ( k2_relat_1(sK3) = sK0
% 3.41/1.00      | r1_tarski(sK0,k2_relat_1(sK3)) != iProver_top
% 3.41/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.41/1.00      inference(superposition,[status(thm)],[c_2325,c_1217]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_11,plain,
% 3.41/1.00      ( v5_relat_1(X0,X1)
% 3.41/1.00      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.41/1.00      | ~ v1_relat_1(X0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_22,plain,
% 3.41/1.00      ( v2_funct_2(X0,k2_relat_1(X0))
% 3.41/1.00      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.41/1.00      | ~ v1_relat_1(X0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_30,negated_conjecture,
% 3.41/1.00      ( ~ v2_funct_2(sK3,sK0) | ~ v2_funct_1(sK2) ),
% 3.41/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_411,plain,
% 3.41/1.00      ( ~ v5_relat_1(X0,k2_relat_1(X0))
% 3.41/1.00      | ~ v2_funct_1(sK2)
% 3.41/1.00      | ~ v1_relat_1(X0)
% 3.41/1.00      | k2_relat_1(X0) != sK0
% 3.41/1.00      | sK3 != X0 ),
% 3.41/1.00      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_412,plain,
% 3.41/1.00      ( ~ v5_relat_1(sK3,k2_relat_1(sK3))
% 3.41/1.00      | ~ v2_funct_1(sK2)
% 3.41/1.00      | ~ v1_relat_1(sK3)
% 3.41/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.41/1.00      inference(unflattening,[status(thm)],[c_411]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_465,plain,
% 3.41/1.00      ( ~ r1_tarski(k2_relat_1(X0),X1)
% 3.41/1.00      | ~ v2_funct_1(sK2)
% 3.41/1.00      | ~ v1_relat_1(X0)
% 3.41/1.00      | ~ v1_relat_1(sK3)
% 3.41/1.00      | k2_relat_1(sK3) != X1
% 3.41/1.00      | k2_relat_1(sK3) != sK0
% 3.41/1.00      | sK3 != X0 ),
% 3.41/1.00      inference(resolution_lifted,[status(thm)],[c_11,c_412]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_466,plain,
% 3.41/1.00      ( ~ r1_tarski(k2_relat_1(sK3),k2_relat_1(sK3))
% 3.41/1.00      | ~ v2_funct_1(sK2)
% 3.41/1.00      | ~ v1_relat_1(sK3)
% 3.41/1.00      | k2_relat_1(sK3) != sK0 ),
% 3.41/1.00      inference(unflattening,[status(thm)],[c_465]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_3,plain,
% 3.41/1.00      ( r1_tarski(X0,X0) ),
% 3.41/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_476,plain,
% 3.41/1.00      ( ~ v2_funct_1(sK2) | ~ v1_relat_1(sK3) | k2_relat_1(sK3) != sK0 ),
% 3.41/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_466,c_3]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(c_477,plain,
% 3.41/1.00      ( k2_relat_1(sK3) != sK0
% 3.41/1.00      | v2_funct_1(sK2) != iProver_top
% 3.41/1.00      | v1_relat_1(sK3) != iProver_top ),
% 3.41/1.00      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 3.41/1.00  
% 3.41/1.00  cnf(contradiction,plain,
% 3.41/1.00      ( $false ),
% 3.41/1.00      inference(minisat,
% 3.41/1.00                [status(thm)],
% 3.41/1.00                [c_3925,c_3567,c_2801,c_2597,c_2434,c_477]) ).
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.41/1.00  
% 3.41/1.00  ------                               Statistics
% 3.41/1.00  
% 3.41/1.00  ------ General
% 3.41/1.00  
% 3.41/1.00  abstr_ref_over_cycles:                  0
% 3.41/1.00  abstr_ref_under_cycles:                 0
% 3.41/1.00  gc_basic_clause_elim:                   0
% 3.41/1.00  forced_gc_time:                         0
% 3.41/1.00  parsing_time:                           0.009
% 3.41/1.00  unif_index_cands_time:                  0.
% 3.41/1.00  unif_index_add_time:                    0.
% 3.41/1.00  orderings_time:                         0.
% 3.41/1.00  out_proof_time:                         0.01
% 3.41/1.00  total_time:                             0.209
% 3.41/1.00  num_of_symbols:                         53
% 3.41/1.00  num_of_terms:                           5886
% 3.41/1.00  
% 3.41/1.00  ------ Preprocessing
% 3.41/1.00  
% 3.41/1.00  num_of_splits:                          0
% 3.41/1.00  num_of_split_atoms:                     0
% 3.41/1.00  num_of_reused_defs:                     0
% 3.41/1.00  num_eq_ax_congr_red:                    7
% 3.41/1.00  num_of_sem_filtered_clauses:            1
% 3.41/1.00  num_of_subtypes:                        0
% 3.41/1.00  monotx_restored_types:                  0
% 3.41/1.00  sat_num_of_epr_types:                   0
% 3.41/1.00  sat_num_of_non_cyclic_types:            0
% 3.41/1.00  sat_guarded_non_collapsed_types:        0
% 3.41/1.00  num_pure_diseq_elim:                    0
% 3.41/1.00  simp_replaced_by:                       0
% 3.41/1.00  res_preprocessed:                       161
% 3.41/1.00  prep_upred:                             0
% 3.41/1.00  prep_unflattend:                        15
% 3.41/1.00  smt_new_axioms:                         0
% 3.41/1.00  pred_elim_cands:                        7
% 3.41/1.00  pred_elim:                              3
% 3.41/1.00  pred_elim_cl:                           6
% 3.41/1.00  pred_elim_cycles:                       5
% 3.41/1.00  merged_defs:                            0
% 3.41/1.00  merged_defs_ncl:                        0
% 3.41/1.00  bin_hyper_res:                          0
% 3.41/1.00  prep_cycles:                            4
% 3.41/1.00  pred_elim_time:                         0.003
% 3.41/1.00  splitting_time:                         0.
% 3.41/1.00  sem_filter_time:                        0.
% 3.41/1.00  monotx_time:                            0.
% 3.41/1.00  subtype_inf_time:                       0.
% 3.41/1.00  
% 3.41/1.00  ------ Problem properties
% 3.41/1.00  
% 3.41/1.00  clauses:                                31
% 3.41/1.00  conjectures:                            6
% 3.41/1.00  epr:                                    10
% 3.41/1.00  horn:                                   30
% 3.41/1.00  ground:                                 9
% 3.41/1.00  unary:                                  15
% 3.41/1.00  binary:                                 4
% 3.41/1.00  lits:                                   76
% 3.41/1.00  lits_eq:                                9
% 3.41/1.00  fd_pure:                                0
% 3.41/1.00  fd_pseudo:                              0
% 3.41/1.00  fd_cond:                                2
% 3.41/1.00  fd_pseudo_cond:                         2
% 3.41/1.00  ac_symbols:                             0
% 3.41/1.00  
% 3.41/1.00  ------ Propositional Solver
% 3.41/1.00  
% 3.41/1.00  prop_solver_calls:                      30
% 3.41/1.00  prop_fast_solver_calls:                 1016
% 3.41/1.00  smt_solver_calls:                       0
% 3.41/1.00  smt_fast_solver_calls:                  0
% 3.41/1.00  prop_num_of_clauses:                    1814
% 3.41/1.00  prop_preprocess_simplified:             6253
% 3.41/1.00  prop_fo_subsumed:                       20
% 3.41/1.00  prop_solver_time:                       0.
% 3.41/1.00  smt_solver_time:                        0.
% 3.41/1.00  smt_fast_solver_time:                   0.
% 3.41/1.00  prop_fast_solver_time:                  0.
% 3.41/1.00  prop_unsat_core_time:                   0.
% 3.41/1.00  
% 3.41/1.00  ------ QBF
% 3.41/1.00  
% 3.41/1.00  qbf_q_res:                              0
% 3.41/1.00  qbf_num_tautologies:                    0
% 3.41/1.00  qbf_prep_cycles:                        0
% 3.41/1.00  
% 3.41/1.00  ------ BMC1
% 3.41/1.00  
% 3.41/1.00  bmc1_current_bound:                     -1
% 3.41/1.00  bmc1_last_solved_bound:                 -1
% 3.41/1.00  bmc1_unsat_core_size:                   -1
% 3.41/1.00  bmc1_unsat_core_parents_size:           -1
% 3.41/1.00  bmc1_merge_next_fun:                    0
% 3.41/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.41/1.00  
% 3.41/1.00  ------ Instantiation
% 3.41/1.00  
% 3.41/1.00  inst_num_of_clauses:                    447
% 3.41/1.00  inst_num_in_passive:                    85
% 3.41/1.00  inst_num_in_active:                     278
% 3.41/1.00  inst_num_in_unprocessed:                84
% 3.41/1.00  inst_num_of_loops:                      290
% 3.41/1.00  inst_num_of_learning_restarts:          0
% 3.41/1.00  inst_num_moves_active_passive:          8
% 3.41/1.00  inst_lit_activity:                      0
% 3.41/1.00  inst_lit_activity_moves:                0
% 3.41/1.00  inst_num_tautologies:                   0
% 3.41/1.00  inst_num_prop_implied:                  0
% 3.41/1.00  inst_num_existing_simplified:           0
% 3.41/1.00  inst_num_eq_res_simplified:             0
% 3.41/1.00  inst_num_child_elim:                    0
% 3.41/1.00  inst_num_of_dismatching_blockings:      76
% 3.41/1.00  inst_num_of_non_proper_insts:           597
% 3.41/1.00  inst_num_of_duplicates:                 0
% 3.41/1.00  inst_inst_num_from_inst_to_res:         0
% 3.41/1.00  inst_dismatching_checking_time:         0.
% 3.41/1.00  
% 3.41/1.00  ------ Resolution
% 3.41/1.00  
% 3.41/1.00  res_num_of_clauses:                     0
% 3.41/1.00  res_num_in_passive:                     0
% 3.41/1.00  res_num_in_active:                      0
% 3.41/1.00  res_num_of_loops:                       165
% 3.41/1.00  res_forward_subset_subsumed:            14
% 3.41/1.00  res_backward_subset_subsumed:           0
% 3.41/1.00  res_forward_subsumed:                   0
% 3.41/1.00  res_backward_subsumed:                  1
% 3.41/1.00  res_forward_subsumption_resolution:     2
% 3.41/1.00  res_backward_subsumption_resolution:    0
% 3.41/1.00  res_clause_to_clause_subsumption:       162
% 3.41/1.00  res_orphan_elimination:                 0
% 3.41/1.00  res_tautology_del:                      27
% 3.41/1.00  res_num_eq_res_simplified:              0
% 3.41/1.00  res_num_sel_changes:                    0
% 3.41/1.00  res_moves_from_active_to_pass:          0
% 3.41/1.00  
% 3.41/1.00  ------ Superposition
% 3.41/1.00  
% 3.41/1.00  sup_time_total:                         0.
% 3.41/1.00  sup_time_generating:                    0.
% 3.41/1.00  sup_time_sim_full:                      0.
% 3.41/1.00  sup_time_sim_immed:                     0.
% 3.41/1.00  
% 3.41/1.00  sup_num_of_clauses:                     88
% 3.41/1.00  sup_num_in_active:                      54
% 3.41/1.00  sup_num_in_passive:                     34
% 3.41/1.00  sup_num_of_loops:                       56
% 3.41/1.00  sup_fw_superposition:                   41
% 3.41/1.00  sup_bw_superposition:                   26
% 3.41/1.00  sup_immediate_simplified:               7
% 3.41/1.00  sup_given_eliminated:                   0
% 3.41/1.00  comparisons_done:                       0
% 3.41/1.00  comparisons_avoided:                    0
% 3.41/1.00  
% 3.41/1.00  ------ Simplifications
% 3.41/1.00  
% 3.41/1.00  
% 3.41/1.00  sim_fw_subset_subsumed:                 2
% 3.41/1.00  sim_bw_subset_subsumed:                 0
% 3.41/1.00  sim_fw_subsumed:                        2
% 3.41/1.00  sim_bw_subsumed:                        3
% 3.41/1.00  sim_fw_subsumption_res:                 0
% 3.41/1.00  sim_bw_subsumption_res:                 0
% 3.41/1.00  sim_tautology_del:                      1
% 3.41/1.00  sim_eq_tautology_del:                   2
% 3.41/1.00  sim_eq_res_simp:                        0
% 3.41/1.00  sim_fw_demodulated:                     3
% 3.41/1.00  sim_bw_demodulated:                     0
% 3.41/1.00  sim_light_normalised:                   2
% 3.41/1.00  sim_joinable_taut:                      0
% 3.41/1.00  sim_joinable_simp:                      0
% 3.41/1.00  sim_ac_normalised:                      0
% 3.41/1.00  sim_smt_subsumption:                    0
% 3.41/1.00  
%------------------------------------------------------------------------------
