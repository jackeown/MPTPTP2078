%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:57 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :  185 ( 770 expanded)
%              Number of clauses        :  102 ( 216 expanded)
%              Number of leaves         :   21 ( 177 expanded)
%              Depth                    :   21
%              Number of atoms          :  561 (5391 expanded)
%              Number of equality atoms :  236 (2081 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f21,plain,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(pure_predicate_removal,[],[f20])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f52,f51])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f43])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f83,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f78,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f41])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f80])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f56,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f64,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f94,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f64,f80])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f70,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f95,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f70,f80])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_partfun1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f63,f80])).

fof(f90,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1045,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1047,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1048,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4223,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1048])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_4445,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4223,c_38])).

cnf(c_4446,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4445])).

cnf(c_4454,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_4446])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_30,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_30])).

cnf(c_367,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_366])).

cnf(c_24,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_46,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_369,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_367,c_46])).

cnf(c_1042,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_369])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1108,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1627,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1042,c_35,c_34,c_33,c_32,c_46,c_367,c_1108])).

cnf(c_4455,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4454,c_1627])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4734,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4455,c_36])).

cnf(c_5,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1059,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4737,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4734,c_1059])).

cnf(c_8,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_4738,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4737,c_8])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_39,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1121,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1175,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1121])).

cnf(c_1176,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1175])).

cnf(c_1324,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1325,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1324])).

cnf(c_4908,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4738,c_37,c_39,c_1176,c_1325])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_18,c_4])).

cnf(c_347,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_343,c_17])).

cnf(c_348,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_347])).

cnf(c_1043,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_1765,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1043])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1061,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2531,plain,
    ( k1_relat_1(sK2) = sK0
    | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1765,c_1061])).

cnf(c_4914,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(superposition,[status(thm)],[c_4908,c_2531])).

cnf(c_1044,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1054,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1056,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1935,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_1056])).

cnf(c_4208,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1935])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_425,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_426,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_428,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_426,c_35])).

cnf(c_1038,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_428])).

cnf(c_1298,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1038,c_35,c_34,c_426,c_1175])).

cnf(c_4210,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4208,c_1298])).

cnf(c_4780,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4210,c_37,c_1176])).

cnf(c_29113,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4914,c_4780])).

cnf(c_1053,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1678,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1053])).

cnf(c_1679,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1053])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1058,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3223,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1054,c_1058])).

cnf(c_10061,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_3223])).

cnf(c_10390,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10061,c_37,c_1176])).

cnf(c_10391,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10390])).

cnf(c_10397,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1679,c_10391])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1052,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1853,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1045,c_1052])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1854,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1853,c_31])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_397,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_398,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_400,plain,
    ( ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_398,c_35])).

cnf(c_1040,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_400])).

cnf(c_1525,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1040,c_35,c_34,c_398,c_1175])).

cnf(c_1857,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_1854,c_1525])).

cnf(c_10404,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10397,c_1857])).

cnf(c_10432,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_1678,c_10404])).

cnf(c_1764,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1043])).

cnf(c_9,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1057,plain,
    ( k5_relat_1(k6_partfun1(X0),X1) = X1
    | r1_tarski(k1_relat_1(X1),X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2670,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1764,c_1057])).

cnf(c_2822,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2670,c_39,c_1325])).

cnf(c_10440,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_10432,c_2822,c_4734])).

cnf(c_29119,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_29113,c_10440])).

cnf(c_26,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f90])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_29119,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:37:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  % Running in FOF mode
% 7.66/1.53  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/1.53  
% 7.66/1.53  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.66/1.53  
% 7.66/1.53  ------  iProver source info
% 7.66/1.53  
% 7.66/1.53  git: date: 2020-06-30 10:37:57 +0100
% 7.66/1.53  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.66/1.53  git: non_committed_changes: false
% 7.66/1.53  git: last_make_outside_of_git: false
% 7.66/1.53  
% 7.66/1.53  ------ 
% 7.66/1.53  
% 7.66/1.53  ------ Input Options
% 7.66/1.53  
% 7.66/1.53  --out_options                           all
% 7.66/1.53  --tptp_safe_out                         true
% 7.66/1.53  --problem_path                          ""
% 7.66/1.53  --include_path                          ""
% 7.66/1.53  --clausifier                            res/vclausify_rel
% 7.66/1.53  --clausifier_options                    ""
% 7.66/1.53  --stdin                                 false
% 7.66/1.53  --stats_out                             all
% 7.66/1.53  
% 7.66/1.53  ------ General Options
% 7.66/1.53  
% 7.66/1.53  --fof                                   false
% 7.66/1.53  --time_out_real                         305.
% 7.66/1.53  --time_out_virtual                      -1.
% 7.66/1.53  --symbol_type_check                     false
% 7.66/1.53  --clausify_out                          false
% 7.66/1.53  --sig_cnt_out                           false
% 7.66/1.53  --trig_cnt_out                          false
% 7.66/1.53  --trig_cnt_out_tolerance                1.
% 7.66/1.53  --trig_cnt_out_sk_spl                   false
% 7.66/1.53  --abstr_cl_out                          false
% 7.66/1.53  
% 7.66/1.53  ------ Global Options
% 7.66/1.53  
% 7.66/1.53  --schedule                              default
% 7.66/1.53  --add_important_lit                     false
% 7.66/1.53  --prop_solver_per_cl                    1000
% 7.66/1.53  --min_unsat_core                        false
% 7.66/1.53  --soft_assumptions                      false
% 7.66/1.53  --soft_lemma_size                       3
% 7.66/1.53  --prop_impl_unit_size                   0
% 7.66/1.53  --prop_impl_unit                        []
% 7.66/1.53  --share_sel_clauses                     true
% 7.66/1.53  --reset_solvers                         false
% 7.66/1.53  --bc_imp_inh                            [conj_cone]
% 7.66/1.53  --conj_cone_tolerance                   3.
% 7.66/1.53  --extra_neg_conj                        none
% 7.66/1.53  --large_theory_mode                     true
% 7.66/1.53  --prolific_symb_bound                   200
% 7.66/1.53  --lt_threshold                          2000
% 7.66/1.53  --clause_weak_htbl                      true
% 7.66/1.53  --gc_record_bc_elim                     false
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing Options
% 7.66/1.53  
% 7.66/1.53  --preprocessing_flag                    true
% 7.66/1.53  --time_out_prep_mult                    0.1
% 7.66/1.53  --splitting_mode                        input
% 7.66/1.53  --splitting_grd                         true
% 7.66/1.53  --splitting_cvd                         false
% 7.66/1.53  --splitting_cvd_svl                     false
% 7.66/1.53  --splitting_nvd                         32
% 7.66/1.53  --sub_typing                            true
% 7.66/1.53  --prep_gs_sim                           true
% 7.66/1.53  --prep_unflatten                        true
% 7.66/1.53  --prep_res_sim                          true
% 7.66/1.53  --prep_upred                            true
% 7.66/1.53  --prep_sem_filter                       exhaustive
% 7.66/1.53  --prep_sem_filter_out                   false
% 7.66/1.53  --pred_elim                             true
% 7.66/1.53  --res_sim_input                         true
% 7.66/1.53  --eq_ax_congr_red                       true
% 7.66/1.53  --pure_diseq_elim                       true
% 7.66/1.53  --brand_transform                       false
% 7.66/1.53  --non_eq_to_eq                          false
% 7.66/1.53  --prep_def_merge                        true
% 7.66/1.53  --prep_def_merge_prop_impl              false
% 7.66/1.53  --prep_def_merge_mbd                    true
% 7.66/1.53  --prep_def_merge_tr_red                 false
% 7.66/1.53  --prep_def_merge_tr_cl                  false
% 7.66/1.53  --smt_preprocessing                     true
% 7.66/1.53  --smt_ac_axioms                         fast
% 7.66/1.53  --preprocessed_out                      false
% 7.66/1.53  --preprocessed_stats                    false
% 7.66/1.53  
% 7.66/1.53  ------ Abstraction refinement Options
% 7.66/1.53  
% 7.66/1.53  --abstr_ref                             []
% 7.66/1.53  --abstr_ref_prep                        false
% 7.66/1.53  --abstr_ref_until_sat                   false
% 7.66/1.53  --abstr_ref_sig_restrict                funpre
% 7.66/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.53  --abstr_ref_under                       []
% 7.66/1.53  
% 7.66/1.53  ------ SAT Options
% 7.66/1.53  
% 7.66/1.53  --sat_mode                              false
% 7.66/1.53  --sat_fm_restart_options                ""
% 7.66/1.53  --sat_gr_def                            false
% 7.66/1.53  --sat_epr_types                         true
% 7.66/1.53  --sat_non_cyclic_types                  false
% 7.66/1.53  --sat_finite_models                     false
% 7.66/1.53  --sat_fm_lemmas                         false
% 7.66/1.53  --sat_fm_prep                           false
% 7.66/1.53  --sat_fm_uc_incr                        true
% 7.66/1.53  --sat_out_model                         small
% 7.66/1.53  --sat_out_clauses                       false
% 7.66/1.53  
% 7.66/1.53  ------ QBF Options
% 7.66/1.53  
% 7.66/1.53  --qbf_mode                              false
% 7.66/1.53  --qbf_elim_univ                         false
% 7.66/1.53  --qbf_dom_inst                          none
% 7.66/1.53  --qbf_dom_pre_inst                      false
% 7.66/1.53  --qbf_sk_in                             false
% 7.66/1.53  --qbf_pred_elim                         true
% 7.66/1.53  --qbf_split                             512
% 7.66/1.53  
% 7.66/1.53  ------ BMC1 Options
% 7.66/1.53  
% 7.66/1.53  --bmc1_incremental                      false
% 7.66/1.53  --bmc1_axioms                           reachable_all
% 7.66/1.53  --bmc1_min_bound                        0
% 7.66/1.53  --bmc1_max_bound                        -1
% 7.66/1.53  --bmc1_max_bound_default                -1
% 7.66/1.53  --bmc1_symbol_reachability              true
% 7.66/1.53  --bmc1_property_lemmas                  false
% 7.66/1.53  --bmc1_k_induction                      false
% 7.66/1.53  --bmc1_non_equiv_states                 false
% 7.66/1.53  --bmc1_deadlock                         false
% 7.66/1.53  --bmc1_ucm                              false
% 7.66/1.53  --bmc1_add_unsat_core                   none
% 7.66/1.53  --bmc1_unsat_core_children              false
% 7.66/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.53  --bmc1_out_stat                         full
% 7.66/1.53  --bmc1_ground_init                      false
% 7.66/1.53  --bmc1_pre_inst_next_state              false
% 7.66/1.53  --bmc1_pre_inst_state                   false
% 7.66/1.53  --bmc1_pre_inst_reach_state             false
% 7.66/1.53  --bmc1_out_unsat_core                   false
% 7.66/1.53  --bmc1_aig_witness_out                  false
% 7.66/1.53  --bmc1_verbose                          false
% 7.66/1.53  --bmc1_dump_clauses_tptp                false
% 7.66/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.53  --bmc1_dump_file                        -
% 7.66/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.53  --bmc1_ucm_extend_mode                  1
% 7.66/1.53  --bmc1_ucm_init_mode                    2
% 7.66/1.53  --bmc1_ucm_cone_mode                    none
% 7.66/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.53  --bmc1_ucm_relax_model                  4
% 7.66/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.53  --bmc1_ucm_layered_model                none
% 7.66/1.53  --bmc1_ucm_max_lemma_size               10
% 7.66/1.53  
% 7.66/1.53  ------ AIG Options
% 7.66/1.53  
% 7.66/1.53  --aig_mode                              false
% 7.66/1.53  
% 7.66/1.53  ------ Instantiation Options
% 7.66/1.53  
% 7.66/1.53  --instantiation_flag                    true
% 7.66/1.53  --inst_sos_flag                         true
% 7.66/1.53  --inst_sos_phase                        true
% 7.66/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.53  --inst_lit_sel_side                     num_symb
% 7.66/1.53  --inst_solver_per_active                1400
% 7.66/1.53  --inst_solver_calls_frac                1.
% 7.66/1.53  --inst_passive_queue_type               priority_queues
% 7.66/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.53  --inst_passive_queues_freq              [25;2]
% 7.66/1.53  --inst_dismatching                      true
% 7.66/1.53  --inst_eager_unprocessed_to_passive     true
% 7.66/1.53  --inst_prop_sim_given                   true
% 7.66/1.53  --inst_prop_sim_new                     false
% 7.66/1.53  --inst_subs_new                         false
% 7.66/1.53  --inst_eq_res_simp                      false
% 7.66/1.53  --inst_subs_given                       false
% 7.66/1.53  --inst_orphan_elimination               true
% 7.66/1.53  --inst_learning_loop_flag               true
% 7.66/1.53  --inst_learning_start                   3000
% 7.66/1.53  --inst_learning_factor                  2
% 7.66/1.53  --inst_start_prop_sim_after_learn       3
% 7.66/1.53  --inst_sel_renew                        solver
% 7.66/1.53  --inst_lit_activity_flag                true
% 7.66/1.53  --inst_restr_to_given                   false
% 7.66/1.53  --inst_activity_threshold               500
% 7.66/1.53  --inst_out_proof                        true
% 7.66/1.53  
% 7.66/1.53  ------ Resolution Options
% 7.66/1.53  
% 7.66/1.53  --resolution_flag                       true
% 7.66/1.53  --res_lit_sel                           adaptive
% 7.66/1.53  --res_lit_sel_side                      none
% 7.66/1.53  --res_ordering                          kbo
% 7.66/1.53  --res_to_prop_solver                    active
% 7.66/1.53  --res_prop_simpl_new                    false
% 7.66/1.53  --res_prop_simpl_given                  true
% 7.66/1.53  --res_passive_queue_type                priority_queues
% 7.66/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.53  --res_passive_queues_freq               [15;5]
% 7.66/1.53  --res_forward_subs                      full
% 7.66/1.53  --res_backward_subs                     full
% 7.66/1.53  --res_forward_subs_resolution           true
% 7.66/1.53  --res_backward_subs_resolution          true
% 7.66/1.53  --res_orphan_elimination                true
% 7.66/1.53  --res_time_limit                        2.
% 7.66/1.53  --res_out_proof                         true
% 7.66/1.53  
% 7.66/1.53  ------ Superposition Options
% 7.66/1.53  
% 7.66/1.53  --superposition_flag                    true
% 7.66/1.53  --sup_passive_queue_type                priority_queues
% 7.66/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.53  --demod_completeness_check              fast
% 7.66/1.53  --demod_use_ground                      true
% 7.66/1.53  --sup_to_prop_solver                    passive
% 7.66/1.53  --sup_prop_simpl_new                    true
% 7.66/1.53  --sup_prop_simpl_given                  true
% 7.66/1.53  --sup_fun_splitting                     true
% 7.66/1.53  --sup_smt_interval                      50000
% 7.66/1.53  
% 7.66/1.53  ------ Superposition Simplification Setup
% 7.66/1.53  
% 7.66/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.66/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.66/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.66/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.66/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.66/1.53  --sup_immed_triv                        [TrivRules]
% 7.66/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_immed_bw_main                     []
% 7.66/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.66/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_input_bw                          []
% 7.66/1.53  
% 7.66/1.53  ------ Combination Options
% 7.66/1.53  
% 7.66/1.53  --comb_res_mult                         3
% 7.66/1.53  --comb_sup_mult                         2
% 7.66/1.53  --comb_inst_mult                        10
% 7.66/1.53  
% 7.66/1.53  ------ Debug Options
% 7.66/1.53  
% 7.66/1.53  --dbg_backtrace                         false
% 7.66/1.53  --dbg_dump_prop_clauses                 false
% 7.66/1.53  --dbg_dump_prop_clauses_file            -
% 7.66/1.53  --dbg_out_stat                          false
% 7.66/1.53  ------ Parsing...
% 7.66/1.53  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.66/1.53  ------ Proving...
% 7.66/1.53  ------ Problem Properties 
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  clauses                                 30
% 7.66/1.53  conjectures                             8
% 7.66/1.53  EPR                                     6
% 7.66/1.53  Horn                                    30
% 7.66/1.53  unary                                   12
% 7.66/1.53  binary                                  9
% 7.66/1.53  lits                                    64
% 7.66/1.53  lits eq                                 17
% 7.66/1.53  fd_pure                                 0
% 7.66/1.53  fd_pseudo                               0
% 7.66/1.53  fd_cond                                 0
% 7.66/1.53  fd_pseudo_cond                          1
% 7.66/1.53  AC symbols                              0
% 7.66/1.53  
% 7.66/1.53  ------ Schedule dynamic 5 is on 
% 7.66/1.53  
% 7.66/1.53  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  ------ 
% 7.66/1.53  Current options:
% 7.66/1.53  ------ 
% 7.66/1.53  
% 7.66/1.53  ------ Input Options
% 7.66/1.53  
% 7.66/1.53  --out_options                           all
% 7.66/1.53  --tptp_safe_out                         true
% 7.66/1.53  --problem_path                          ""
% 7.66/1.53  --include_path                          ""
% 7.66/1.53  --clausifier                            res/vclausify_rel
% 7.66/1.53  --clausifier_options                    ""
% 7.66/1.53  --stdin                                 false
% 7.66/1.53  --stats_out                             all
% 7.66/1.53  
% 7.66/1.53  ------ General Options
% 7.66/1.53  
% 7.66/1.53  --fof                                   false
% 7.66/1.53  --time_out_real                         305.
% 7.66/1.53  --time_out_virtual                      -1.
% 7.66/1.53  --symbol_type_check                     false
% 7.66/1.53  --clausify_out                          false
% 7.66/1.53  --sig_cnt_out                           false
% 7.66/1.53  --trig_cnt_out                          false
% 7.66/1.53  --trig_cnt_out_tolerance                1.
% 7.66/1.53  --trig_cnt_out_sk_spl                   false
% 7.66/1.53  --abstr_cl_out                          false
% 7.66/1.53  
% 7.66/1.53  ------ Global Options
% 7.66/1.53  
% 7.66/1.53  --schedule                              default
% 7.66/1.53  --add_important_lit                     false
% 7.66/1.53  --prop_solver_per_cl                    1000
% 7.66/1.53  --min_unsat_core                        false
% 7.66/1.53  --soft_assumptions                      false
% 7.66/1.53  --soft_lemma_size                       3
% 7.66/1.53  --prop_impl_unit_size                   0
% 7.66/1.53  --prop_impl_unit                        []
% 7.66/1.53  --share_sel_clauses                     true
% 7.66/1.53  --reset_solvers                         false
% 7.66/1.53  --bc_imp_inh                            [conj_cone]
% 7.66/1.53  --conj_cone_tolerance                   3.
% 7.66/1.53  --extra_neg_conj                        none
% 7.66/1.53  --large_theory_mode                     true
% 7.66/1.53  --prolific_symb_bound                   200
% 7.66/1.53  --lt_threshold                          2000
% 7.66/1.53  --clause_weak_htbl                      true
% 7.66/1.53  --gc_record_bc_elim                     false
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing Options
% 7.66/1.53  
% 7.66/1.53  --preprocessing_flag                    true
% 7.66/1.53  --time_out_prep_mult                    0.1
% 7.66/1.53  --splitting_mode                        input
% 7.66/1.53  --splitting_grd                         true
% 7.66/1.53  --splitting_cvd                         false
% 7.66/1.53  --splitting_cvd_svl                     false
% 7.66/1.53  --splitting_nvd                         32
% 7.66/1.53  --sub_typing                            true
% 7.66/1.53  --prep_gs_sim                           true
% 7.66/1.53  --prep_unflatten                        true
% 7.66/1.53  --prep_res_sim                          true
% 7.66/1.53  --prep_upred                            true
% 7.66/1.53  --prep_sem_filter                       exhaustive
% 7.66/1.53  --prep_sem_filter_out                   false
% 7.66/1.53  --pred_elim                             true
% 7.66/1.53  --res_sim_input                         true
% 7.66/1.53  --eq_ax_congr_red                       true
% 7.66/1.53  --pure_diseq_elim                       true
% 7.66/1.53  --brand_transform                       false
% 7.66/1.53  --non_eq_to_eq                          false
% 7.66/1.53  --prep_def_merge                        true
% 7.66/1.53  --prep_def_merge_prop_impl              false
% 7.66/1.53  --prep_def_merge_mbd                    true
% 7.66/1.53  --prep_def_merge_tr_red                 false
% 7.66/1.53  --prep_def_merge_tr_cl                  false
% 7.66/1.53  --smt_preprocessing                     true
% 7.66/1.53  --smt_ac_axioms                         fast
% 7.66/1.53  --preprocessed_out                      false
% 7.66/1.53  --preprocessed_stats                    false
% 7.66/1.53  
% 7.66/1.53  ------ Abstraction refinement Options
% 7.66/1.53  
% 7.66/1.53  --abstr_ref                             []
% 7.66/1.53  --abstr_ref_prep                        false
% 7.66/1.53  --abstr_ref_until_sat                   false
% 7.66/1.53  --abstr_ref_sig_restrict                funpre
% 7.66/1.53  --abstr_ref_af_restrict_to_split_sk     false
% 7.66/1.53  --abstr_ref_under                       []
% 7.66/1.53  
% 7.66/1.53  ------ SAT Options
% 7.66/1.53  
% 7.66/1.53  --sat_mode                              false
% 7.66/1.53  --sat_fm_restart_options                ""
% 7.66/1.53  --sat_gr_def                            false
% 7.66/1.53  --sat_epr_types                         true
% 7.66/1.53  --sat_non_cyclic_types                  false
% 7.66/1.53  --sat_finite_models                     false
% 7.66/1.53  --sat_fm_lemmas                         false
% 7.66/1.53  --sat_fm_prep                           false
% 7.66/1.53  --sat_fm_uc_incr                        true
% 7.66/1.53  --sat_out_model                         small
% 7.66/1.53  --sat_out_clauses                       false
% 7.66/1.53  
% 7.66/1.53  ------ QBF Options
% 7.66/1.53  
% 7.66/1.53  --qbf_mode                              false
% 7.66/1.53  --qbf_elim_univ                         false
% 7.66/1.53  --qbf_dom_inst                          none
% 7.66/1.53  --qbf_dom_pre_inst                      false
% 7.66/1.53  --qbf_sk_in                             false
% 7.66/1.53  --qbf_pred_elim                         true
% 7.66/1.53  --qbf_split                             512
% 7.66/1.53  
% 7.66/1.53  ------ BMC1 Options
% 7.66/1.53  
% 7.66/1.53  --bmc1_incremental                      false
% 7.66/1.53  --bmc1_axioms                           reachable_all
% 7.66/1.53  --bmc1_min_bound                        0
% 7.66/1.53  --bmc1_max_bound                        -1
% 7.66/1.53  --bmc1_max_bound_default                -1
% 7.66/1.53  --bmc1_symbol_reachability              true
% 7.66/1.53  --bmc1_property_lemmas                  false
% 7.66/1.53  --bmc1_k_induction                      false
% 7.66/1.53  --bmc1_non_equiv_states                 false
% 7.66/1.53  --bmc1_deadlock                         false
% 7.66/1.53  --bmc1_ucm                              false
% 7.66/1.53  --bmc1_add_unsat_core                   none
% 7.66/1.53  --bmc1_unsat_core_children              false
% 7.66/1.53  --bmc1_unsat_core_extrapolate_axioms    false
% 7.66/1.53  --bmc1_out_stat                         full
% 7.66/1.53  --bmc1_ground_init                      false
% 7.66/1.53  --bmc1_pre_inst_next_state              false
% 7.66/1.53  --bmc1_pre_inst_state                   false
% 7.66/1.53  --bmc1_pre_inst_reach_state             false
% 7.66/1.53  --bmc1_out_unsat_core                   false
% 7.66/1.53  --bmc1_aig_witness_out                  false
% 7.66/1.53  --bmc1_verbose                          false
% 7.66/1.53  --bmc1_dump_clauses_tptp                false
% 7.66/1.53  --bmc1_dump_unsat_core_tptp             false
% 7.66/1.53  --bmc1_dump_file                        -
% 7.66/1.53  --bmc1_ucm_expand_uc_limit              128
% 7.66/1.53  --bmc1_ucm_n_expand_iterations          6
% 7.66/1.53  --bmc1_ucm_extend_mode                  1
% 7.66/1.53  --bmc1_ucm_init_mode                    2
% 7.66/1.53  --bmc1_ucm_cone_mode                    none
% 7.66/1.53  --bmc1_ucm_reduced_relation_type        0
% 7.66/1.53  --bmc1_ucm_relax_model                  4
% 7.66/1.53  --bmc1_ucm_full_tr_after_sat            true
% 7.66/1.53  --bmc1_ucm_expand_neg_assumptions       false
% 7.66/1.53  --bmc1_ucm_layered_model                none
% 7.66/1.53  --bmc1_ucm_max_lemma_size               10
% 7.66/1.53  
% 7.66/1.53  ------ AIG Options
% 7.66/1.53  
% 7.66/1.53  --aig_mode                              false
% 7.66/1.53  
% 7.66/1.53  ------ Instantiation Options
% 7.66/1.53  
% 7.66/1.53  --instantiation_flag                    true
% 7.66/1.53  --inst_sos_flag                         true
% 7.66/1.53  --inst_sos_phase                        true
% 7.66/1.53  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.66/1.53  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.66/1.53  --inst_lit_sel_side                     none
% 7.66/1.53  --inst_solver_per_active                1400
% 7.66/1.53  --inst_solver_calls_frac                1.
% 7.66/1.53  --inst_passive_queue_type               priority_queues
% 7.66/1.53  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.66/1.53  --inst_passive_queues_freq              [25;2]
% 7.66/1.53  --inst_dismatching                      true
% 7.66/1.53  --inst_eager_unprocessed_to_passive     true
% 7.66/1.53  --inst_prop_sim_given                   true
% 7.66/1.53  --inst_prop_sim_new                     false
% 7.66/1.53  --inst_subs_new                         false
% 7.66/1.53  --inst_eq_res_simp                      false
% 7.66/1.53  --inst_subs_given                       false
% 7.66/1.53  --inst_orphan_elimination               true
% 7.66/1.53  --inst_learning_loop_flag               true
% 7.66/1.53  --inst_learning_start                   3000
% 7.66/1.53  --inst_learning_factor                  2
% 7.66/1.53  --inst_start_prop_sim_after_learn       3
% 7.66/1.53  --inst_sel_renew                        solver
% 7.66/1.53  --inst_lit_activity_flag                true
% 7.66/1.53  --inst_restr_to_given                   false
% 7.66/1.53  --inst_activity_threshold               500
% 7.66/1.53  --inst_out_proof                        true
% 7.66/1.53  
% 7.66/1.53  ------ Resolution Options
% 7.66/1.53  
% 7.66/1.53  --resolution_flag                       false
% 7.66/1.53  --res_lit_sel                           adaptive
% 7.66/1.53  --res_lit_sel_side                      none
% 7.66/1.53  --res_ordering                          kbo
% 7.66/1.53  --res_to_prop_solver                    active
% 7.66/1.53  --res_prop_simpl_new                    false
% 7.66/1.53  --res_prop_simpl_given                  true
% 7.66/1.53  --res_passive_queue_type                priority_queues
% 7.66/1.53  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.66/1.53  --res_passive_queues_freq               [15;5]
% 7.66/1.53  --res_forward_subs                      full
% 7.66/1.53  --res_backward_subs                     full
% 7.66/1.53  --res_forward_subs_resolution           true
% 7.66/1.53  --res_backward_subs_resolution          true
% 7.66/1.53  --res_orphan_elimination                true
% 7.66/1.53  --res_time_limit                        2.
% 7.66/1.53  --res_out_proof                         true
% 7.66/1.53  
% 7.66/1.53  ------ Superposition Options
% 7.66/1.53  
% 7.66/1.53  --superposition_flag                    true
% 7.66/1.53  --sup_passive_queue_type                priority_queues
% 7.66/1.53  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.66/1.53  --sup_passive_queues_freq               [8;1;4]
% 7.66/1.53  --demod_completeness_check              fast
% 7.66/1.53  --demod_use_ground                      true
% 7.66/1.53  --sup_to_prop_solver                    passive
% 7.66/1.53  --sup_prop_simpl_new                    true
% 7.66/1.53  --sup_prop_simpl_given                  true
% 7.66/1.53  --sup_fun_splitting                     true
% 7.66/1.53  --sup_smt_interval                      50000
% 7.66/1.53  
% 7.66/1.53  ------ Superposition Simplification Setup
% 7.66/1.53  
% 7.66/1.53  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.66/1.53  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.66/1.53  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.66/1.53  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.66/1.53  --sup_full_triv                         [TrivRules;PropSubs]
% 7.66/1.53  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.66/1.53  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.66/1.53  --sup_immed_triv                        [TrivRules]
% 7.66/1.53  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_immed_bw_main                     []
% 7.66/1.53  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.66/1.53  --sup_input_triv                        [Unflattening;TrivRules]
% 7.66/1.53  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.66/1.53  --sup_input_bw                          []
% 7.66/1.53  
% 7.66/1.53  ------ Combination Options
% 7.66/1.53  
% 7.66/1.53  --comb_res_mult                         3
% 7.66/1.53  --comb_sup_mult                         2
% 7.66/1.53  --comb_inst_mult                        10
% 7.66/1.53  
% 7.66/1.53  ------ Debug Options
% 7.66/1.53  
% 7.66/1.53  --dbg_backtrace                         false
% 7.66/1.53  --dbg_dump_prop_clauses                 false
% 7.66/1.53  --dbg_dump_prop_clauses_file            -
% 7.66/1.53  --dbg_out_stat                          false
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  ------ Proving...
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  % SZS status Theorem for theBenchmark.p
% 7.66/1.53  
% 7.66/1.53  % SZS output start CNFRefutation for theBenchmark.p
% 7.66/1.53  
% 7.66/1.53  fof(f19,conjecture,(
% 7.66/1.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f20,negated_conjecture,(
% 7.66/1.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.66/1.53    inference(negated_conjecture,[],[f19])).
% 7.66/1.53  
% 7.66/1.53  fof(f21,plain,(
% 7.66/1.53    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.66/1.53    inference(pure_predicate_removal,[],[f20])).
% 7.66/1.53  
% 7.66/1.53  fof(f45,plain,(
% 7.66/1.53    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 7.66/1.53    inference(ennf_transformation,[],[f21])).
% 7.66/1.53  
% 7.66/1.53  fof(f46,plain,(
% 7.66/1.53    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 7.66/1.53    inference(flattening,[],[f45])).
% 7.66/1.53  
% 7.66/1.53  fof(f52,plain,(
% 7.66/1.53    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(sK3))) )),
% 7.66/1.53    introduced(choice_axiom,[])).
% 7.66/1.53  
% 7.66/1.53  fof(f51,plain,(
% 7.66/1.53    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2))),
% 7.66/1.53    introduced(choice_axiom,[])).
% 7.66/1.53  
% 7.66/1.53  fof(f53,plain,(
% 7.66/1.53    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_1(sK2)),
% 7.66/1.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f52,f51])).
% 7.66/1.53  
% 7.66/1.53  fof(f82,plain,(
% 7.66/1.53    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.66/1.53    inference(cnf_transformation,[],[f53])).
% 7.66/1.53  
% 7.66/1.53  fof(f84,plain,(
% 7.66/1.53    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.66/1.53    inference(cnf_transformation,[],[f53])).
% 7.66/1.53  
% 7.66/1.53  fof(f17,axiom,(
% 7.66/1.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f43,plain,(
% 7.66/1.53    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.66/1.53    inference(ennf_transformation,[],[f17])).
% 7.66/1.53  
% 7.66/1.53  fof(f44,plain,(
% 7.66/1.53    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.66/1.53    inference(flattening,[],[f43])).
% 7.66/1.53  
% 7.66/1.53  fof(f79,plain,(
% 7.66/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f44])).
% 7.66/1.53  
% 7.66/1.53  fof(f83,plain,(
% 7.66/1.53    v1_funct_1(sK3)),
% 7.66/1.53    inference(cnf_transformation,[],[f53])).
% 7.66/1.53  
% 7.66/1.53  fof(f14,axiom,(
% 7.66/1.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f39,plain,(
% 7.66/1.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.66/1.53    inference(ennf_transformation,[],[f14])).
% 7.66/1.53  
% 7.66/1.53  fof(f40,plain,(
% 7.66/1.53    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.66/1.53    inference(flattening,[],[f39])).
% 7.66/1.53  
% 7.66/1.53  fof(f50,plain,(
% 7.66/1.53    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.66/1.53    inference(nnf_transformation,[],[f40])).
% 7.66/1.53  
% 7.66/1.53  fof(f74,plain,(
% 7.66/1.53    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.66/1.53    inference(cnf_transformation,[],[f50])).
% 7.66/1.53  
% 7.66/1.53  fof(f86,plain,(
% 7.66/1.53    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.66/1.53    inference(cnf_transformation,[],[f53])).
% 7.66/1.53  
% 7.66/1.53  fof(f16,axiom,(
% 7.66/1.53    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f22,plain,(
% 7.66/1.53    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.66/1.53    inference(pure_predicate_removal,[],[f16])).
% 7.66/1.53  
% 7.66/1.53  fof(f78,plain,(
% 7.66/1.53    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.66/1.53    inference(cnf_transformation,[],[f22])).
% 7.66/1.53  
% 7.66/1.53  fof(f81,plain,(
% 7.66/1.53    v1_funct_1(sK2)),
% 7.66/1.53    inference(cnf_transformation,[],[f53])).
% 7.66/1.53  
% 7.66/1.53  fof(f15,axiom,(
% 7.66/1.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f41,plain,(
% 7.66/1.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.66/1.53    inference(ennf_transformation,[],[f15])).
% 7.66/1.53  
% 7.66/1.53  fof(f42,plain,(
% 7.66/1.53    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.66/1.53    inference(flattening,[],[f41])).
% 7.66/1.53  
% 7.66/1.53  fof(f77,plain,(
% 7.66/1.53    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f42])).
% 7.66/1.53  
% 7.66/1.53  fof(f3,axiom,(
% 7.66/1.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f25,plain,(
% 7.66/1.53    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.66/1.53    inference(ennf_transformation,[],[f3])).
% 7.66/1.53  
% 7.66/1.53  fof(f59,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f25])).
% 7.66/1.53  
% 7.66/1.53  fof(f5,axiom,(
% 7.66/1.53    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f61,plain,(
% 7.66/1.53    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.66/1.53    inference(cnf_transformation,[],[f5])).
% 7.66/1.53  
% 7.66/1.53  fof(f18,axiom,(
% 7.66/1.53    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f80,plain,(
% 7.66/1.53    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f18])).
% 7.66/1.53  
% 7.66/1.53  fof(f92,plain,(
% 7.66/1.53    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.66/1.53    inference(definition_unfolding,[],[f61,f80])).
% 7.66/1.53  
% 7.66/1.53  fof(f11,axiom,(
% 7.66/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f36,plain,(
% 7.66/1.53    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.66/1.53    inference(ennf_transformation,[],[f11])).
% 7.66/1.53  
% 7.66/1.53  fof(f71,plain,(
% 7.66/1.53    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.66/1.53    inference(cnf_transformation,[],[f36])).
% 7.66/1.53  
% 7.66/1.53  fof(f12,axiom,(
% 7.66/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f23,plain,(
% 7.66/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 7.66/1.53    inference(pure_predicate_removal,[],[f12])).
% 7.66/1.53  
% 7.66/1.53  fof(f37,plain,(
% 7.66/1.53    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.66/1.53    inference(ennf_transformation,[],[f23])).
% 7.66/1.53  
% 7.66/1.53  fof(f72,plain,(
% 7.66/1.53    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.66/1.53    inference(cnf_transformation,[],[f37])).
% 7.66/1.53  
% 7.66/1.53  fof(f2,axiom,(
% 7.66/1.53    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f24,plain,(
% 7.66/1.53    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.66/1.53    inference(ennf_transformation,[],[f2])).
% 7.66/1.53  
% 7.66/1.53  fof(f49,plain,(
% 7.66/1.53    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.66/1.53    inference(nnf_transformation,[],[f24])).
% 7.66/1.53  
% 7.66/1.53  fof(f57,plain,(
% 7.66/1.53    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f49])).
% 7.66/1.53  
% 7.66/1.53  fof(f1,axiom,(
% 7.66/1.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f47,plain,(
% 7.66/1.53    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.66/1.53    inference(nnf_transformation,[],[f1])).
% 7.66/1.53  
% 7.66/1.53  fof(f48,plain,(
% 7.66/1.53    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.66/1.53    inference(flattening,[],[f47])).
% 7.66/1.53  
% 7.66/1.53  fof(f56,plain,(
% 7.66/1.53    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f48])).
% 7.66/1.53  
% 7.66/1.53  fof(f8,axiom,(
% 7.66/1.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f30,plain,(
% 7.66/1.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.66/1.53    inference(ennf_transformation,[],[f8])).
% 7.66/1.53  
% 7.66/1.53  fof(f31,plain,(
% 7.66/1.53    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.66/1.53    inference(flattening,[],[f30])).
% 7.66/1.53  
% 7.66/1.53  fof(f65,plain,(
% 7.66/1.53    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f31])).
% 7.66/1.53  
% 7.66/1.53  fof(f7,axiom,(
% 7.66/1.53    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f29,plain,(
% 7.66/1.53    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.66/1.53    inference(ennf_transformation,[],[f7])).
% 7.66/1.53  
% 7.66/1.53  fof(f64,plain,(
% 7.66/1.53    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f29])).
% 7.66/1.53  
% 7.66/1.53  fof(f94,plain,(
% 7.66/1.53    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.66/1.53    inference(definition_unfolding,[],[f64,f80])).
% 7.66/1.53  
% 7.66/1.53  fof(f9,axiom,(
% 7.66/1.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f32,plain,(
% 7.66/1.53    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.66/1.53    inference(ennf_transformation,[],[f9])).
% 7.66/1.53  
% 7.66/1.53  fof(f33,plain,(
% 7.66/1.53    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.66/1.53    inference(flattening,[],[f32])).
% 7.66/1.53  
% 7.66/1.53  fof(f68,plain,(
% 7.66/1.53    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f33])).
% 7.66/1.53  
% 7.66/1.53  fof(f87,plain,(
% 7.66/1.53    v2_funct_1(sK2)),
% 7.66/1.53    inference(cnf_transformation,[],[f53])).
% 7.66/1.53  
% 7.66/1.53  fof(f4,axiom,(
% 7.66/1.53    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f26,plain,(
% 7.66/1.53    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.66/1.53    inference(ennf_transformation,[],[f4])).
% 7.66/1.53  
% 7.66/1.53  fof(f60,plain,(
% 7.66/1.53    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f26])).
% 7.66/1.53  
% 7.66/1.53  fof(f13,axiom,(
% 7.66/1.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f38,plain,(
% 7.66/1.53    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.66/1.53    inference(ennf_transformation,[],[f13])).
% 7.66/1.53  
% 7.66/1.53  fof(f73,plain,(
% 7.66/1.53    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.66/1.53    inference(cnf_transformation,[],[f38])).
% 7.66/1.53  
% 7.66/1.53  fof(f85,plain,(
% 7.66/1.53    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.66/1.53    inference(cnf_transformation,[],[f53])).
% 7.66/1.53  
% 7.66/1.53  fof(f10,axiom,(
% 7.66/1.53    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f34,plain,(
% 7.66/1.53    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.66/1.53    inference(ennf_transformation,[],[f10])).
% 7.66/1.53  
% 7.66/1.53  fof(f35,plain,(
% 7.66/1.53    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.66/1.53    inference(flattening,[],[f34])).
% 7.66/1.53  
% 7.66/1.53  fof(f70,plain,(
% 7.66/1.53    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f35])).
% 7.66/1.53  
% 7.66/1.53  fof(f95,plain,(
% 7.66/1.53    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.66/1.53    inference(definition_unfolding,[],[f70,f80])).
% 7.66/1.53  
% 7.66/1.53  fof(f6,axiom,(
% 7.66/1.53    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 7.66/1.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.66/1.53  
% 7.66/1.53  fof(f27,plain,(
% 7.66/1.53    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.66/1.53    inference(ennf_transformation,[],[f6])).
% 7.66/1.53  
% 7.66/1.53  fof(f28,plain,(
% 7.66/1.53    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.66/1.53    inference(flattening,[],[f27])).
% 7.66/1.53  
% 7.66/1.53  fof(f63,plain,(
% 7.66/1.53    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.66/1.53    inference(cnf_transformation,[],[f28])).
% 7.66/1.53  
% 7.66/1.53  fof(f93,plain,(
% 7.66/1.53    ( ! [X0,X1] : (k5_relat_1(k6_partfun1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 7.66/1.53    inference(definition_unfolding,[],[f63,f80])).
% 7.66/1.53  
% 7.66/1.53  fof(f90,plain,(
% 7.66/1.53    k2_funct_1(sK2) != sK3),
% 7.66/1.53    inference(cnf_transformation,[],[f53])).
% 7.66/1.53  
% 7.66/1.53  cnf(c_34,negated_conjecture,
% 7.66/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.66/1.53      inference(cnf_transformation,[],[f82]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1045,plain,
% 7.66/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_32,negated_conjecture,
% 7.66/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.66/1.53      inference(cnf_transformation,[],[f84]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1047,plain,
% 7.66/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_25,plain,
% 7.66/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.66/1.53      | ~ v1_funct_1(X0)
% 7.66/1.53      | ~ v1_funct_1(X3)
% 7.66/1.53      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f79]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1048,plain,
% 7.66/1.53      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.66/1.53      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.66/1.53      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.66/1.53      | v1_funct_1(X5) != iProver_top
% 7.66/1.53      | v1_funct_1(X4) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4223,plain,
% 7.66/1.53      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.66/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.66/1.53      | v1_funct_1(X2) != iProver_top
% 7.66/1.53      | v1_funct_1(sK3) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1047,c_1048]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_33,negated_conjecture,
% 7.66/1.53      ( v1_funct_1(sK3) ),
% 7.66/1.53      inference(cnf_transformation,[],[f83]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_38,plain,
% 7.66/1.53      ( v1_funct_1(sK3) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4445,plain,
% 7.66/1.53      ( v1_funct_1(X2) != iProver_top
% 7.66/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.66/1.53      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_4223,c_38]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4446,plain,
% 7.66/1.53      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.66/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.66/1.53      | v1_funct_1(X2) != iProver_top ),
% 7.66/1.53      inference(renaming,[status(thm)],[c_4445]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4454,plain,
% 7.66/1.53      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.66/1.53      | v1_funct_1(sK2) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1045,c_4446]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_21,plain,
% 7.66/1.53      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.66/1.53      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.66/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.66/1.53      | X3 = X2 ),
% 7.66/1.53      inference(cnf_transformation,[],[f74]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_30,negated_conjecture,
% 7.66/1.53      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.66/1.53      inference(cnf_transformation,[],[f86]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_366,plain,
% 7.66/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.53      | X3 = X0
% 7.66/1.53      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.66/1.53      | k6_partfun1(sK0) != X3
% 7.66/1.53      | sK0 != X2
% 7.66/1.53      | sK0 != X1 ),
% 7.66/1.53      inference(resolution_lifted,[status(thm)],[c_21,c_30]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_367,plain,
% 7.66/1.53      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.66/1.53      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.66/1.53      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.66/1.53      inference(unflattening,[status(thm)],[c_366]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_24,plain,
% 7.66/1.53      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.66/1.53      inference(cnf_transformation,[],[f78]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_46,plain,
% 7.66/1.53      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_24]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_369,plain,
% 7.66/1.53      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.66/1.53      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_367,c_46]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1042,plain,
% 7.66/1.53      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.66/1.53      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_369]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_35,negated_conjecture,
% 7.66/1.53      ( v1_funct_1(sK2) ),
% 7.66/1.53      inference(cnf_transformation,[],[f81]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_22,plain,
% 7.66/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.53      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.66/1.53      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.66/1.53      | ~ v1_funct_1(X0)
% 7.66/1.53      | ~ v1_funct_1(X3) ),
% 7.66/1.53      inference(cnf_transformation,[],[f77]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1108,plain,
% 7.66/1.53      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.66/1.53      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.66/1.53      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.66/1.53      | ~ v1_funct_1(sK3)
% 7.66/1.53      | ~ v1_funct_1(sK2) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_22]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1627,plain,
% 7.66/1.53      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_1042,c_35,c_34,c_33,c_32,c_46,c_367,c_1108]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4455,plain,
% 7.66/1.53      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.66/1.53      | v1_funct_1(sK2) != iProver_top ),
% 7.66/1.53      inference(light_normalisation,[status(thm)],[c_4454,c_1627]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_36,plain,
% 7.66/1.53      ( v1_funct_1(sK2) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4734,plain,
% 7.66/1.53      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_4455,c_36]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_5,plain,
% 7.66/1.53      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
% 7.66/1.53      | ~ v1_relat_1(X1)
% 7.66/1.53      | ~ v1_relat_1(X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f59]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1059,plain,
% 7.66/1.53      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) = iProver_top
% 7.66/1.53      | v1_relat_1(X0) != iProver_top
% 7.66/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4737,plain,
% 7.66/1.53      ( r1_tarski(k1_relat_1(k6_partfun1(sK0)),k1_relat_1(sK2)) = iProver_top
% 7.66/1.53      | v1_relat_1(sK3) != iProver_top
% 7.66/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_4734,c_1059]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_8,plain,
% 7.66/1.53      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.66/1.53      inference(cnf_transformation,[],[f92]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4738,plain,
% 7.66/1.53      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top
% 7.66/1.53      | v1_relat_1(sK3) != iProver_top
% 7.66/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.53      inference(demodulation,[status(thm)],[c_4737,c_8]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_37,plain,
% 7.66/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_39,plain,
% 7.66/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_17,plain,
% 7.66/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.53      | v1_relat_1(X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f71]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1121,plain,
% 7.66/1.53      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.66/1.53      | v1_relat_1(sK2) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_17]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1175,plain,
% 7.66/1.53      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.66/1.53      | v1_relat_1(sK2) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_1121]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1176,plain,
% 7.66/1.53      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.66/1.53      | v1_relat_1(sK2) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_1175]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1324,plain,
% 7.66/1.53      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.66/1.53      | v1_relat_1(sK3) ),
% 7.66/1.53      inference(instantiation,[status(thm)],[c_17]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1325,plain,
% 7.66/1.53      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.66/1.53      | v1_relat_1(sK3) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_1324]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4908,plain,
% 7.66/1.53      ( r1_tarski(sK0,k1_relat_1(sK2)) = iProver_top ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_4738,c_37,c_39,c_1176,c_1325]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_18,plain,
% 7.66/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.53      | v4_relat_1(X0,X1) ),
% 7.66/1.53      inference(cnf_transformation,[],[f72]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4,plain,
% 7.66/1.53      ( ~ v4_relat_1(X0,X1)
% 7.66/1.53      | r1_tarski(k1_relat_1(X0),X1)
% 7.66/1.53      | ~ v1_relat_1(X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f57]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_343,plain,
% 7.66/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.53      | r1_tarski(k1_relat_1(X0),X1)
% 7.66/1.53      | ~ v1_relat_1(X0) ),
% 7.66/1.53      inference(resolution,[status(thm)],[c_18,c_4]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_347,plain,
% 7.66/1.53      ( r1_tarski(k1_relat_1(X0),X1)
% 7.66/1.53      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_343,c_17]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_348,plain,
% 7.66/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.53      | r1_tarski(k1_relat_1(X0),X1) ),
% 7.66/1.53      inference(renaming,[status(thm)],[c_347]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1043,plain,
% 7.66/1.53      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.66/1.53      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1765,plain,
% 7.66/1.53      ( r1_tarski(k1_relat_1(sK2),sK0) = iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1045,c_1043]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_0,plain,
% 7.66/1.53      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.66/1.53      inference(cnf_transformation,[],[f56]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1061,plain,
% 7.66/1.53      ( X0 = X1
% 7.66/1.53      | r1_tarski(X0,X1) != iProver_top
% 7.66/1.53      | r1_tarski(X1,X0) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2531,plain,
% 7.66/1.53      ( k1_relat_1(sK2) = sK0
% 7.66/1.53      | r1_tarski(sK0,k1_relat_1(sK2)) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1765,c_1061]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4914,plain,
% 7.66/1.53      ( k1_relat_1(sK2) = sK0 ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_4908,c_2531]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1044,plain,
% 7.66/1.53      ( v1_funct_1(sK2) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_12,plain,
% 7.66/1.53      ( ~ v1_funct_1(X0)
% 7.66/1.53      | ~ v1_relat_1(X0)
% 7.66/1.53      | v1_relat_1(k2_funct_1(X0)) ),
% 7.66/1.53      inference(cnf_transformation,[],[f65]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1054,plain,
% 7.66/1.53      ( v1_funct_1(X0) != iProver_top
% 7.66/1.53      | v1_relat_1(X0) != iProver_top
% 7.66/1.53      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10,plain,
% 7.66/1.53      ( ~ v1_relat_1(X0)
% 7.66/1.53      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 7.66/1.53      inference(cnf_transformation,[],[f94]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1056,plain,
% 7.66/1.53      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 7.66/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1935,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 7.66/1.53      | v1_funct_1(X0) != iProver_top
% 7.66/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1054,c_1056]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4208,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 7.66/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1044,c_1935]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_13,plain,
% 7.66/1.53      ( ~ v2_funct_1(X0)
% 7.66/1.53      | ~ v1_funct_1(X0)
% 7.66/1.53      | ~ v1_relat_1(X0)
% 7.66/1.53      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f68]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_29,negated_conjecture,
% 7.66/1.53      ( v2_funct_1(sK2) ),
% 7.66/1.53      inference(cnf_transformation,[],[f87]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_425,plain,
% 7.66/1.53      ( ~ v1_funct_1(X0)
% 7.66/1.53      | ~ v1_relat_1(X0)
% 7.66/1.53      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.66/1.53      | sK2 != X0 ),
% 7.66/1.53      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_426,plain,
% 7.66/1.53      ( ~ v1_funct_1(sK2)
% 7.66/1.53      | ~ v1_relat_1(sK2)
% 7.66/1.53      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.66/1.53      inference(unflattening,[status(thm)],[c_425]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_428,plain,
% 7.66/1.53      ( ~ v1_relat_1(sK2)
% 7.66/1.53      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_426,c_35]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1038,plain,
% 7.66/1.53      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.66/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_428]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1298,plain,
% 7.66/1.53      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_1038,c_35,c_34,c_426,c_1175]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4210,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2)
% 7.66/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.53      inference(light_normalisation,[status(thm)],[c_4208,c_1298]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_4780,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k1_relat_1(sK2))) = k2_funct_1(sK2) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_4210,c_37,c_1176]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_29113,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 7.66/1.53      inference(demodulation,[status(thm)],[c_4914,c_4780]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1053,plain,
% 7.66/1.53      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.66/1.53      | v1_relat_1(X0) = iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1678,plain,
% 7.66/1.53      ( v1_relat_1(sK3) = iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1047,c_1053]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1679,plain,
% 7.66/1.53      ( v1_relat_1(sK2) = iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1045,c_1053]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_6,plain,
% 7.66/1.53      ( ~ v1_relat_1(X0)
% 7.66/1.53      | ~ v1_relat_1(X1)
% 7.66/1.53      | ~ v1_relat_1(X2)
% 7.66/1.53      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 7.66/1.53      inference(cnf_transformation,[],[f60]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1058,plain,
% 7.66/1.53      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.66/1.53      | v1_relat_1(X1) != iProver_top
% 7.66/1.53      | v1_relat_1(X0) != iProver_top
% 7.66/1.53      | v1_relat_1(X2) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_3223,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.66/1.53      | v1_funct_1(X0) != iProver_top
% 7.66/1.53      | v1_relat_1(X0) != iProver_top
% 7.66/1.53      | v1_relat_1(X1) != iProver_top
% 7.66/1.53      | v1_relat_1(X2) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1054,c_1058]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10061,plain,
% 7.66/1.53      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.66/1.53      | v1_relat_1(X0) != iProver_top
% 7.66/1.53      | v1_relat_1(X1) != iProver_top
% 7.66/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1044,c_3223]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10390,plain,
% 7.66/1.53      ( v1_relat_1(X1) != iProver_top
% 7.66/1.53      | v1_relat_1(X0) != iProver_top
% 7.66/1.53      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_10061,c_37,c_1176]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10391,plain,
% 7.66/1.53      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.66/1.53      | v1_relat_1(X0) != iProver_top
% 7.66/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.66/1.53      inference(renaming,[status(thm)],[c_10390]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10397,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 7.66/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1679,c_10391]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_19,plain,
% 7.66/1.53      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.66/1.53      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.66/1.53      inference(cnf_transformation,[],[f73]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1052,plain,
% 7.66/1.53      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.66/1.53      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1853,plain,
% 7.66/1.53      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1045,c_1052]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_31,negated_conjecture,
% 7.66/1.53      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.66/1.53      inference(cnf_transformation,[],[f85]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1854,plain,
% 7.66/1.53      ( k2_relat_1(sK2) = sK1 ),
% 7.66/1.53      inference(light_normalisation,[status(thm)],[c_1853,c_31]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_15,plain,
% 7.66/1.53      ( ~ v2_funct_1(X0)
% 7.66/1.53      | ~ v1_funct_1(X0)
% 7.66/1.53      | ~ v1_relat_1(X0)
% 7.66/1.53      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 7.66/1.53      inference(cnf_transformation,[],[f95]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_397,plain,
% 7.66/1.53      ( ~ v1_funct_1(X0)
% 7.66/1.53      | ~ v1_relat_1(X0)
% 7.66/1.53      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 7.66/1.53      | sK2 != X0 ),
% 7.66/1.53      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_398,plain,
% 7.66/1.53      ( ~ v1_funct_1(sK2)
% 7.66/1.53      | ~ v1_relat_1(sK2)
% 7.66/1.53      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.66/1.53      inference(unflattening,[status(thm)],[c_397]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_400,plain,
% 7.66/1.53      ( ~ v1_relat_1(sK2)
% 7.66/1.53      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_398,c_35]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1040,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 7.66/1.53      | v1_relat_1(sK2) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_400]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1525,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_1040,c_35,c_34,c_398,c_1175]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1857,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.66/1.53      inference(demodulation,[status(thm)],[c_1854,c_1525]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10404,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.66/1.53      | v1_relat_1(X0) != iProver_top ),
% 7.66/1.53      inference(light_normalisation,[status(thm)],[c_10397,c_1857]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10432,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1678,c_10404]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1764,plain,
% 7.66/1.53      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1047,c_1043]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_9,plain,
% 7.66/1.53      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 7.66/1.53      | ~ v1_relat_1(X0)
% 7.66/1.53      | k5_relat_1(k6_partfun1(X1),X0) = X0 ),
% 7.66/1.53      inference(cnf_transformation,[],[f93]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_1057,plain,
% 7.66/1.53      ( k5_relat_1(k6_partfun1(X0),X1) = X1
% 7.66/1.53      | r1_tarski(k1_relat_1(X1),X0) != iProver_top
% 7.66/1.53      | v1_relat_1(X1) != iProver_top ),
% 7.66/1.53      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2670,plain,
% 7.66/1.53      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3
% 7.66/1.53      | v1_relat_1(sK3) != iProver_top ),
% 7.66/1.53      inference(superposition,[status(thm)],[c_1764,c_1057]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_2822,plain,
% 7.66/1.53      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 7.66/1.53      inference(global_propositional_subsumption,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_2670,c_39,c_1325]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_10440,plain,
% 7.66/1.53      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = sK3 ),
% 7.66/1.53      inference(light_normalisation,
% 7.66/1.53                [status(thm)],
% 7.66/1.53                [c_10432,c_2822,c_4734]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_29119,plain,
% 7.66/1.53      ( k2_funct_1(sK2) = sK3 ),
% 7.66/1.53      inference(light_normalisation,[status(thm)],[c_29113,c_10440]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(c_26,negated_conjecture,
% 7.66/1.53      ( k2_funct_1(sK2) != sK3 ),
% 7.66/1.53      inference(cnf_transformation,[],[f90]) ).
% 7.66/1.53  
% 7.66/1.53  cnf(contradiction,plain,
% 7.66/1.53      ( $false ),
% 7.66/1.53      inference(minisat,[status(thm)],[c_29119,c_26]) ).
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  % SZS output end CNFRefutation for theBenchmark.p
% 7.66/1.53  
% 7.66/1.53  ------                               Statistics
% 7.66/1.53  
% 7.66/1.53  ------ General
% 7.66/1.53  
% 7.66/1.53  abstr_ref_over_cycles:                  0
% 7.66/1.53  abstr_ref_under_cycles:                 0
% 7.66/1.53  gc_basic_clause_elim:                   0
% 7.66/1.53  forced_gc_time:                         0
% 7.66/1.53  parsing_time:                           0.007
% 7.66/1.53  unif_index_cands_time:                  0.
% 7.66/1.53  unif_index_add_time:                    0.
% 7.66/1.53  orderings_time:                         0.
% 7.66/1.53  out_proof_time:                         0.014
% 7.66/1.53  total_time:                             0.874
% 7.66/1.53  num_of_symbols:                         52
% 7.66/1.53  num_of_terms:                           34313
% 7.66/1.53  
% 7.66/1.53  ------ Preprocessing
% 7.66/1.53  
% 7.66/1.53  num_of_splits:                          0
% 7.66/1.53  num_of_split_atoms:                     0
% 7.66/1.53  num_of_reused_defs:                     0
% 7.66/1.53  num_eq_ax_congr_red:                    2
% 7.66/1.53  num_of_sem_filtered_clauses:            1
% 7.66/1.53  num_of_subtypes:                        0
% 7.66/1.53  monotx_restored_types:                  0
% 7.66/1.53  sat_num_of_epr_types:                   0
% 7.66/1.53  sat_num_of_non_cyclic_types:            0
% 7.66/1.53  sat_guarded_non_collapsed_types:        0
% 7.66/1.53  num_pure_diseq_elim:                    0
% 7.66/1.53  simp_replaced_by:                       0
% 7.66/1.53  res_preprocessed:                       156
% 7.66/1.53  prep_upred:                             0
% 7.66/1.53  prep_unflattend:                        12
% 7.66/1.53  smt_new_axioms:                         0
% 7.66/1.53  pred_elim_cands:                        4
% 7.66/1.53  pred_elim:                              3
% 7.66/1.53  pred_elim_cl:                           5
% 7.66/1.53  pred_elim_cycles:                       5
% 7.66/1.53  merged_defs:                            0
% 7.66/1.53  merged_defs_ncl:                        0
% 7.66/1.53  bin_hyper_res:                          0
% 7.66/1.53  prep_cycles:                            4
% 7.66/1.53  pred_elim_time:                         0.001
% 7.66/1.53  splitting_time:                         0.
% 7.66/1.53  sem_filter_time:                        0.
% 7.66/1.53  monotx_time:                            0.
% 7.66/1.53  subtype_inf_time:                       0.
% 7.66/1.53  
% 7.66/1.53  ------ Problem properties
% 7.66/1.53  
% 7.66/1.53  clauses:                                30
% 7.66/1.53  conjectures:                            8
% 7.66/1.53  epr:                                    6
% 7.66/1.53  horn:                                   30
% 7.66/1.53  ground:                                 13
% 7.66/1.53  unary:                                  12
% 7.66/1.53  binary:                                 9
% 7.66/1.53  lits:                                   64
% 7.66/1.53  lits_eq:                                17
% 7.66/1.53  fd_pure:                                0
% 7.66/1.53  fd_pseudo:                              0
% 7.66/1.53  fd_cond:                                0
% 7.66/1.53  fd_pseudo_cond:                         1
% 7.66/1.53  ac_symbols:                             0
% 7.66/1.53  
% 7.66/1.53  ------ Propositional Solver
% 7.66/1.53  
% 7.66/1.53  prop_solver_calls:                      35
% 7.66/1.53  prop_fast_solver_calls:                 1921
% 7.66/1.53  smt_solver_calls:                       0
% 7.66/1.53  smt_fast_solver_calls:                  0
% 7.66/1.53  prop_num_of_clauses:                    15658
% 7.66/1.53  prop_preprocess_simplified:             29627
% 7.66/1.53  prop_fo_subsumed:                       222
% 7.66/1.53  prop_solver_time:                       0.
% 7.66/1.53  smt_solver_time:                        0.
% 7.66/1.53  smt_fast_solver_time:                   0.
% 7.66/1.53  prop_fast_solver_time:                  0.
% 7.66/1.53  prop_unsat_core_time:                   0.002
% 7.66/1.53  
% 7.66/1.53  ------ QBF
% 7.66/1.53  
% 7.66/1.53  qbf_q_res:                              0
% 7.66/1.53  qbf_num_tautologies:                    0
% 7.66/1.53  qbf_prep_cycles:                        0
% 7.66/1.53  
% 7.66/1.53  ------ BMC1
% 7.66/1.53  
% 7.66/1.53  bmc1_current_bound:                     -1
% 7.66/1.53  bmc1_last_solved_bound:                 -1
% 7.66/1.53  bmc1_unsat_core_size:                   -1
% 7.66/1.53  bmc1_unsat_core_parents_size:           -1
% 7.66/1.53  bmc1_merge_next_fun:                    0
% 7.66/1.53  bmc1_unsat_core_clauses_time:           0.
% 7.66/1.53  
% 7.66/1.53  ------ Instantiation
% 7.66/1.53  
% 7.66/1.53  inst_num_of_clauses:                    4565
% 7.66/1.53  inst_num_in_passive:                    2243
% 7.66/1.53  inst_num_in_active:                     1724
% 7.66/1.53  inst_num_in_unprocessed:                598
% 7.66/1.53  inst_num_of_loops:                      1880
% 7.66/1.53  inst_num_of_learning_restarts:          0
% 7.66/1.53  inst_num_moves_active_passive:          152
% 7.66/1.53  inst_lit_activity:                      0
% 7.66/1.53  inst_lit_activity_moves:                1
% 7.66/1.53  inst_num_tautologies:                   0
% 7.66/1.53  inst_num_prop_implied:                  0
% 7.66/1.53  inst_num_existing_simplified:           0
% 7.66/1.53  inst_num_eq_res_simplified:             0
% 7.66/1.53  inst_num_child_elim:                    0
% 7.66/1.53  inst_num_of_dismatching_blockings:      1320
% 7.66/1.53  inst_num_of_non_proper_insts:           4933
% 7.66/1.53  inst_num_of_duplicates:                 0
% 7.66/1.53  inst_inst_num_from_inst_to_res:         0
% 7.66/1.53  inst_dismatching_checking_time:         0.
% 7.66/1.53  
% 7.66/1.53  ------ Resolution
% 7.66/1.53  
% 7.66/1.53  res_num_of_clauses:                     0
% 7.66/1.53  res_num_in_passive:                     0
% 7.66/1.53  res_num_in_active:                      0
% 7.66/1.53  res_num_of_loops:                       160
% 7.66/1.53  res_forward_subset_subsumed:            555
% 7.66/1.53  res_backward_subset_subsumed:           0
% 7.66/1.53  res_forward_subsumed:                   0
% 7.66/1.53  res_backward_subsumed:                  0
% 7.66/1.53  res_forward_subsumption_resolution:     0
% 7.66/1.53  res_backward_subsumption_resolution:    0
% 7.66/1.53  res_clause_to_clause_subsumption:       3403
% 7.66/1.53  res_orphan_elimination:                 0
% 7.66/1.53  res_tautology_del:                      306
% 7.66/1.53  res_num_eq_res_simplified:              0
% 7.66/1.53  res_num_sel_changes:                    0
% 7.66/1.53  res_moves_from_active_to_pass:          0
% 7.66/1.53  
% 7.66/1.53  ------ Superposition
% 7.66/1.53  
% 7.66/1.53  sup_time_total:                         0.
% 7.66/1.53  sup_time_generating:                    0.
% 7.66/1.53  sup_time_sim_full:                      0.
% 7.66/1.53  sup_time_sim_immed:                     0.
% 7.66/1.53  
% 7.66/1.53  sup_num_of_clauses:                     984
% 7.66/1.53  sup_num_in_active:                      322
% 7.66/1.53  sup_num_in_passive:                     662
% 7.66/1.53  sup_num_of_loops:                       375
% 7.66/1.53  sup_fw_superposition:                   831
% 7.66/1.53  sup_bw_superposition:                   541
% 7.66/1.53  sup_immediate_simplified:               659
% 7.66/1.53  sup_given_eliminated:                   2
% 7.66/1.53  comparisons_done:                       0
% 7.66/1.53  comparisons_avoided:                    0
% 7.66/1.53  
% 7.66/1.53  ------ Simplifications
% 7.66/1.53  
% 7.66/1.53  
% 7.66/1.53  sim_fw_subset_subsumed:                 55
% 7.66/1.53  sim_bw_subset_subsumed:                 89
% 7.66/1.53  sim_fw_subsumed:                        105
% 7.66/1.53  sim_bw_subsumed:                        0
% 7.66/1.53  sim_fw_subsumption_res:                 0
% 7.66/1.53  sim_bw_subsumption_res:                 0
% 7.66/1.53  sim_tautology_del:                      0
% 7.66/1.53  sim_eq_tautology_del:                   147
% 7.66/1.53  sim_eq_res_simp:                        0
% 7.66/1.53  sim_fw_demodulated:                     151
% 7.66/1.53  sim_bw_demodulated:                     37
% 7.66/1.53  sim_light_normalised:                   515
% 7.66/1.53  sim_joinable_taut:                      0
% 7.66/1.53  sim_joinable_simp:                      0
% 7.66/1.53  sim_ac_normalised:                      0
% 7.66/1.53  sim_smt_subsumption:                    0
% 7.66/1.53  
%------------------------------------------------------------------------------
