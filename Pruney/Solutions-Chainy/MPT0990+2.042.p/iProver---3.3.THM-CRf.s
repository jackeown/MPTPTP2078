%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:05 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.08s
% Verified   : 
% Statistics : Number of formulae       :  167 (1343 expanded)
%              Number of clauses        :   98 ( 385 expanded)
%              Number of leaves         :   19 ( 348 expanded)
%              Depth                    :   21
%              Number of atoms          :  668 (11771 expanded)
%              Number of equality atoms :  320 (4289 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( k2_funct_1(X2) != sK3
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK3,X1,X0)
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & v2_funct_1(X2)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & k2_relset_1(sK0,sK1,sK2) = sK1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f72,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
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

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f30])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f75,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f69,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f27])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f2,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f78,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f64])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f48,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f77,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1102,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1117,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2056,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1102,c_1117])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2058,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2056,c_26])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1105,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1111,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3029,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_1111])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1118,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2135,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1105,c_1118])).

cnf(c_3041,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3029,c_2135])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_37,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_23,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_619,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_644,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_620,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1444,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_1445,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1444])).

cnf(c_3255,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3041,c_37,c_23,c_644,c_1445])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1124,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3887,plain,
    ( k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_3255,c_1124])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_38,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1406,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1407,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1406])).

cnf(c_18834,plain,
    ( v1_funct_1(X0) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3887,c_36,c_38,c_1407])).

cnf(c_18835,plain,
    ( k2_relat_1(X0) != sK1
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_18834])).

cnf(c_18846,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2058,c_18835])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1107,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3373,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_1107])).

cnf(c_3428,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3373,c_36])).

cnf(c_3429,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3428])).

cnf(c_3439,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1102,c_3429])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1543,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_1818,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1543])).

cnf(c_2095,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_1818])).

cnf(c_2153,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_2095])).

cnf(c_3949,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3439,c_32,c_30,c_29,c_27,c_2153])).

cnf(c_9,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_362,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_361])).

cnf(c_18,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_370,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_362,c_18])).

cnf(c_1098,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_3952,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3949,c_1098])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1110,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3978,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3949,c_1110])).

cnf(c_4192,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3952,c_33,c_35,c_36,c_38,c_3978])).

cnf(c_18851,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18846,c_4192])).

cnf(c_1409,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1410,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1409])).

cnf(c_2,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_13934,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_13935,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13934])).

cnf(c_18980,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18851,c_33,c_35,c_1410,c_13935])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1121,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_4196,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4192,c_1121])).

cnf(c_2055,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1105,c_1117])).

cnf(c_20,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_374,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_25])).

cnf(c_375,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_457,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_375])).

cnf(c_1097,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_1607,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1097])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_34,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1864,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1607,c_33,c_34,c_35,c_36,c_37,c_38])).

cnf(c_2061,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2055,c_1864])).

cnf(c_4197,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4196,c_2058,c_2061,c_3255])).

cnf(c_4198,plain,
    ( k2_funct_1(sK3) = sK2
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4197])).

cnf(c_5435,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4198,c_33,c_35,c_36,c_38,c_1407,c_1410])).

cnf(c_18985,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_18980,c_5435])).

cnf(c_1119,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1957,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_1119])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1120,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2194,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1957,c_1120])).

cnf(c_2366,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_36])).

cnf(c_18986,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_18980,c_2366])).

cnf(c_18990,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_18985,c_18986])).

cnf(c_21,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f77])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18990,c_21])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 17:05:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 7.08/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.08/1.48  
% 7.08/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.08/1.48  
% 7.08/1.48  ------  iProver source info
% 7.08/1.48  
% 7.08/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.08/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.08/1.48  git: non_committed_changes: false
% 7.08/1.48  git: last_make_outside_of_git: false
% 7.08/1.48  
% 7.08/1.48  ------ 
% 7.08/1.48  
% 7.08/1.48  ------ Input Options
% 7.08/1.48  
% 7.08/1.48  --out_options                           all
% 7.08/1.48  --tptp_safe_out                         true
% 7.08/1.48  --problem_path                          ""
% 7.08/1.48  --include_path                          ""
% 7.08/1.48  --clausifier                            res/vclausify_rel
% 7.08/1.48  --clausifier_options                    --mode clausify
% 7.08/1.48  --stdin                                 false
% 7.08/1.48  --stats_out                             all
% 7.08/1.48  
% 7.08/1.48  ------ General Options
% 7.08/1.48  
% 7.08/1.48  --fof                                   false
% 7.08/1.48  --time_out_real                         305.
% 7.08/1.48  --time_out_virtual                      -1.
% 7.08/1.48  --symbol_type_check                     false
% 7.08/1.48  --clausify_out                          false
% 7.08/1.48  --sig_cnt_out                           false
% 7.08/1.48  --trig_cnt_out                          false
% 7.08/1.48  --trig_cnt_out_tolerance                1.
% 7.08/1.48  --trig_cnt_out_sk_spl                   false
% 7.08/1.48  --abstr_cl_out                          false
% 7.08/1.48  
% 7.08/1.48  ------ Global Options
% 7.08/1.48  
% 7.08/1.48  --schedule                              default
% 7.08/1.48  --add_important_lit                     false
% 7.08/1.48  --prop_solver_per_cl                    1000
% 7.08/1.48  --min_unsat_core                        false
% 7.08/1.48  --soft_assumptions                      false
% 7.08/1.48  --soft_lemma_size                       3
% 7.08/1.48  --prop_impl_unit_size                   0
% 7.08/1.48  --prop_impl_unit                        []
% 7.08/1.48  --share_sel_clauses                     true
% 7.08/1.48  --reset_solvers                         false
% 7.08/1.48  --bc_imp_inh                            [conj_cone]
% 7.08/1.48  --conj_cone_tolerance                   3.
% 7.08/1.48  --extra_neg_conj                        none
% 7.08/1.48  --large_theory_mode                     true
% 7.08/1.48  --prolific_symb_bound                   200
% 7.08/1.48  --lt_threshold                          2000
% 7.08/1.48  --clause_weak_htbl                      true
% 7.08/1.48  --gc_record_bc_elim                     false
% 7.08/1.48  
% 7.08/1.48  ------ Preprocessing Options
% 7.08/1.48  
% 7.08/1.48  --preprocessing_flag                    true
% 7.08/1.48  --time_out_prep_mult                    0.1
% 7.08/1.48  --splitting_mode                        input
% 7.08/1.48  --splitting_grd                         true
% 7.08/1.48  --splitting_cvd                         false
% 7.08/1.48  --splitting_cvd_svl                     false
% 7.08/1.48  --splitting_nvd                         32
% 7.08/1.48  --sub_typing                            true
% 7.08/1.48  --prep_gs_sim                           true
% 7.08/1.48  --prep_unflatten                        true
% 7.08/1.48  --prep_res_sim                          true
% 7.08/1.48  --prep_upred                            true
% 7.08/1.48  --prep_sem_filter                       exhaustive
% 7.08/1.48  --prep_sem_filter_out                   false
% 7.08/1.48  --pred_elim                             true
% 7.08/1.48  --res_sim_input                         true
% 7.08/1.48  --eq_ax_congr_red                       true
% 7.08/1.48  --pure_diseq_elim                       true
% 7.08/1.48  --brand_transform                       false
% 7.08/1.48  --non_eq_to_eq                          false
% 7.08/1.48  --prep_def_merge                        true
% 7.08/1.48  --prep_def_merge_prop_impl              false
% 7.08/1.48  --prep_def_merge_mbd                    true
% 7.08/1.48  --prep_def_merge_tr_red                 false
% 7.08/1.48  --prep_def_merge_tr_cl                  false
% 7.08/1.48  --smt_preprocessing                     true
% 7.08/1.48  --smt_ac_axioms                         fast
% 7.08/1.48  --preprocessed_out                      false
% 7.08/1.48  --preprocessed_stats                    false
% 7.08/1.48  
% 7.08/1.48  ------ Abstraction refinement Options
% 7.08/1.48  
% 7.08/1.48  --abstr_ref                             []
% 7.08/1.48  --abstr_ref_prep                        false
% 7.08/1.48  --abstr_ref_until_sat                   false
% 7.08/1.48  --abstr_ref_sig_restrict                funpre
% 7.08/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.08/1.48  --abstr_ref_under                       []
% 7.08/1.48  
% 7.08/1.48  ------ SAT Options
% 7.08/1.48  
% 7.08/1.48  --sat_mode                              false
% 7.08/1.48  --sat_fm_restart_options                ""
% 7.08/1.48  --sat_gr_def                            false
% 7.08/1.48  --sat_epr_types                         true
% 7.08/1.48  --sat_non_cyclic_types                  false
% 7.08/1.48  --sat_finite_models                     false
% 7.08/1.48  --sat_fm_lemmas                         false
% 7.08/1.48  --sat_fm_prep                           false
% 7.08/1.48  --sat_fm_uc_incr                        true
% 7.08/1.48  --sat_out_model                         small
% 7.08/1.48  --sat_out_clauses                       false
% 7.08/1.48  
% 7.08/1.48  ------ QBF Options
% 7.08/1.48  
% 7.08/1.48  --qbf_mode                              false
% 7.08/1.48  --qbf_elim_univ                         false
% 7.08/1.48  --qbf_dom_inst                          none
% 7.08/1.48  --qbf_dom_pre_inst                      false
% 7.08/1.48  --qbf_sk_in                             false
% 7.08/1.48  --qbf_pred_elim                         true
% 7.08/1.48  --qbf_split                             512
% 7.08/1.48  
% 7.08/1.48  ------ BMC1 Options
% 7.08/1.48  
% 7.08/1.48  --bmc1_incremental                      false
% 7.08/1.48  --bmc1_axioms                           reachable_all
% 7.08/1.48  --bmc1_min_bound                        0
% 7.08/1.48  --bmc1_max_bound                        -1
% 7.08/1.48  --bmc1_max_bound_default                -1
% 7.08/1.48  --bmc1_symbol_reachability              true
% 7.08/1.48  --bmc1_property_lemmas                  false
% 7.08/1.48  --bmc1_k_induction                      false
% 7.08/1.48  --bmc1_non_equiv_states                 false
% 7.08/1.48  --bmc1_deadlock                         false
% 7.08/1.48  --bmc1_ucm                              false
% 7.08/1.48  --bmc1_add_unsat_core                   none
% 7.08/1.48  --bmc1_unsat_core_children              false
% 7.08/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.08/1.48  --bmc1_out_stat                         full
% 7.08/1.48  --bmc1_ground_init                      false
% 7.08/1.48  --bmc1_pre_inst_next_state              false
% 7.08/1.48  --bmc1_pre_inst_state                   false
% 7.08/1.48  --bmc1_pre_inst_reach_state             false
% 7.08/1.48  --bmc1_out_unsat_core                   false
% 7.08/1.48  --bmc1_aig_witness_out                  false
% 7.08/1.48  --bmc1_verbose                          false
% 7.08/1.48  --bmc1_dump_clauses_tptp                false
% 7.08/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.08/1.48  --bmc1_dump_file                        -
% 7.08/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.08/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.08/1.48  --bmc1_ucm_extend_mode                  1
% 7.08/1.48  --bmc1_ucm_init_mode                    2
% 7.08/1.48  --bmc1_ucm_cone_mode                    none
% 7.08/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.08/1.48  --bmc1_ucm_relax_model                  4
% 7.08/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.08/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.08/1.48  --bmc1_ucm_layered_model                none
% 7.08/1.48  --bmc1_ucm_max_lemma_size               10
% 7.08/1.48  
% 7.08/1.48  ------ AIG Options
% 7.08/1.48  
% 7.08/1.48  --aig_mode                              false
% 7.08/1.48  
% 7.08/1.48  ------ Instantiation Options
% 7.08/1.48  
% 7.08/1.48  --instantiation_flag                    true
% 7.08/1.48  --inst_sos_flag                         false
% 7.08/1.48  --inst_sos_phase                        true
% 7.08/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.08/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.08/1.48  --inst_lit_sel_side                     num_symb
% 7.08/1.48  --inst_solver_per_active                1400
% 7.08/1.48  --inst_solver_calls_frac                1.
% 7.08/1.48  --inst_passive_queue_type               priority_queues
% 7.08/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.08/1.48  --inst_passive_queues_freq              [25;2]
% 7.08/1.48  --inst_dismatching                      true
% 7.08/1.48  --inst_eager_unprocessed_to_passive     true
% 7.08/1.48  --inst_prop_sim_given                   true
% 7.08/1.48  --inst_prop_sim_new                     false
% 7.08/1.48  --inst_subs_new                         false
% 7.08/1.48  --inst_eq_res_simp                      false
% 7.08/1.48  --inst_subs_given                       false
% 7.08/1.48  --inst_orphan_elimination               true
% 7.08/1.48  --inst_learning_loop_flag               true
% 7.08/1.48  --inst_learning_start                   3000
% 7.08/1.48  --inst_learning_factor                  2
% 7.08/1.48  --inst_start_prop_sim_after_learn       3
% 7.08/1.48  --inst_sel_renew                        solver
% 7.08/1.48  --inst_lit_activity_flag                true
% 7.08/1.48  --inst_restr_to_given                   false
% 7.08/1.48  --inst_activity_threshold               500
% 7.08/1.48  --inst_out_proof                        true
% 7.08/1.48  
% 7.08/1.48  ------ Resolution Options
% 7.08/1.48  
% 7.08/1.48  --resolution_flag                       true
% 7.08/1.48  --res_lit_sel                           adaptive
% 7.08/1.48  --res_lit_sel_side                      none
% 7.08/1.48  --res_ordering                          kbo
% 7.08/1.48  --res_to_prop_solver                    active
% 7.08/1.48  --res_prop_simpl_new                    false
% 7.08/1.48  --res_prop_simpl_given                  true
% 7.08/1.48  --res_passive_queue_type                priority_queues
% 7.08/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.08/1.48  --res_passive_queues_freq               [15;5]
% 7.08/1.48  --res_forward_subs                      full
% 7.08/1.48  --res_backward_subs                     full
% 7.08/1.48  --res_forward_subs_resolution           true
% 7.08/1.48  --res_backward_subs_resolution          true
% 7.08/1.48  --res_orphan_elimination                true
% 7.08/1.48  --res_time_limit                        2.
% 7.08/1.48  --res_out_proof                         true
% 7.08/1.48  
% 7.08/1.48  ------ Superposition Options
% 7.08/1.48  
% 7.08/1.48  --superposition_flag                    true
% 7.08/1.48  --sup_passive_queue_type                priority_queues
% 7.08/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.08/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.08/1.48  --demod_completeness_check              fast
% 7.08/1.48  --demod_use_ground                      true
% 7.08/1.48  --sup_to_prop_solver                    passive
% 7.08/1.48  --sup_prop_simpl_new                    true
% 7.08/1.48  --sup_prop_simpl_given                  true
% 7.08/1.48  --sup_fun_splitting                     false
% 7.08/1.48  --sup_smt_interval                      50000
% 7.08/1.48  
% 7.08/1.48  ------ Superposition Simplification Setup
% 7.08/1.48  
% 7.08/1.48  --sup_indices_passive                   []
% 7.08/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.08/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.48  --sup_full_bw                           [BwDemod]
% 7.08/1.48  --sup_immed_triv                        [TrivRules]
% 7.08/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.08/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.48  --sup_immed_bw_main                     []
% 7.08/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.08/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.48  
% 7.08/1.48  ------ Combination Options
% 7.08/1.48  
% 7.08/1.48  --comb_res_mult                         3
% 7.08/1.48  --comb_sup_mult                         2
% 7.08/1.48  --comb_inst_mult                        10
% 7.08/1.48  
% 7.08/1.48  ------ Debug Options
% 7.08/1.48  
% 7.08/1.48  --dbg_backtrace                         false
% 7.08/1.48  --dbg_dump_prop_clauses                 false
% 7.08/1.48  --dbg_dump_prop_clauses_file            -
% 7.08/1.48  --dbg_out_stat                          false
% 7.08/1.48  ------ Parsing...
% 7.08/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.08/1.48  
% 7.08/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.08/1.48  
% 7.08/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.08/1.48  
% 7.08/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.08/1.48  ------ Proving...
% 7.08/1.48  ------ Problem Properties 
% 7.08/1.48  
% 7.08/1.48  
% 7.08/1.48  clauses                                 32
% 7.08/1.48  conjectures                             11
% 7.08/1.48  EPR                                     7
% 7.08/1.48  Horn                                    28
% 7.08/1.48  unary                                   13
% 7.08/1.48  binary                                  4
% 7.08/1.48  lits                                    99
% 7.08/1.48  lits eq                                 27
% 7.08/1.48  fd_pure                                 0
% 7.08/1.48  fd_pseudo                               0
% 7.08/1.48  fd_cond                                 3
% 7.08/1.48  fd_pseudo_cond                          1
% 7.08/1.48  AC symbols                              0
% 7.08/1.48  
% 7.08/1.48  ------ Schedule dynamic 5 is on 
% 7.08/1.48  
% 7.08/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.08/1.48  
% 7.08/1.48  
% 7.08/1.48  ------ 
% 7.08/1.48  Current options:
% 7.08/1.48  ------ 
% 7.08/1.48  
% 7.08/1.48  ------ Input Options
% 7.08/1.48  
% 7.08/1.48  --out_options                           all
% 7.08/1.48  --tptp_safe_out                         true
% 7.08/1.48  --problem_path                          ""
% 7.08/1.48  --include_path                          ""
% 7.08/1.48  --clausifier                            res/vclausify_rel
% 7.08/1.48  --clausifier_options                    --mode clausify
% 7.08/1.48  --stdin                                 false
% 7.08/1.48  --stats_out                             all
% 7.08/1.48  
% 7.08/1.48  ------ General Options
% 7.08/1.48  
% 7.08/1.48  --fof                                   false
% 7.08/1.48  --time_out_real                         305.
% 7.08/1.48  --time_out_virtual                      -1.
% 7.08/1.48  --symbol_type_check                     false
% 7.08/1.48  --clausify_out                          false
% 7.08/1.48  --sig_cnt_out                           false
% 7.08/1.48  --trig_cnt_out                          false
% 7.08/1.48  --trig_cnt_out_tolerance                1.
% 7.08/1.48  --trig_cnt_out_sk_spl                   false
% 7.08/1.48  --abstr_cl_out                          false
% 7.08/1.48  
% 7.08/1.48  ------ Global Options
% 7.08/1.48  
% 7.08/1.48  --schedule                              default
% 7.08/1.48  --add_important_lit                     false
% 7.08/1.48  --prop_solver_per_cl                    1000
% 7.08/1.48  --min_unsat_core                        false
% 7.08/1.48  --soft_assumptions                      false
% 7.08/1.48  --soft_lemma_size                       3
% 7.08/1.48  --prop_impl_unit_size                   0
% 7.08/1.48  --prop_impl_unit                        []
% 7.08/1.48  --share_sel_clauses                     true
% 7.08/1.48  --reset_solvers                         false
% 7.08/1.48  --bc_imp_inh                            [conj_cone]
% 7.08/1.48  --conj_cone_tolerance                   3.
% 7.08/1.48  --extra_neg_conj                        none
% 7.08/1.48  --large_theory_mode                     true
% 7.08/1.48  --prolific_symb_bound                   200
% 7.08/1.48  --lt_threshold                          2000
% 7.08/1.48  --clause_weak_htbl                      true
% 7.08/1.48  --gc_record_bc_elim                     false
% 7.08/1.48  
% 7.08/1.48  ------ Preprocessing Options
% 7.08/1.48  
% 7.08/1.48  --preprocessing_flag                    true
% 7.08/1.48  --time_out_prep_mult                    0.1
% 7.08/1.48  --splitting_mode                        input
% 7.08/1.48  --splitting_grd                         true
% 7.08/1.48  --splitting_cvd                         false
% 7.08/1.48  --splitting_cvd_svl                     false
% 7.08/1.48  --splitting_nvd                         32
% 7.08/1.48  --sub_typing                            true
% 7.08/1.48  --prep_gs_sim                           true
% 7.08/1.48  --prep_unflatten                        true
% 7.08/1.48  --prep_res_sim                          true
% 7.08/1.48  --prep_upred                            true
% 7.08/1.48  --prep_sem_filter                       exhaustive
% 7.08/1.48  --prep_sem_filter_out                   false
% 7.08/1.48  --pred_elim                             true
% 7.08/1.48  --res_sim_input                         true
% 7.08/1.48  --eq_ax_congr_red                       true
% 7.08/1.48  --pure_diseq_elim                       true
% 7.08/1.48  --brand_transform                       false
% 7.08/1.48  --non_eq_to_eq                          false
% 7.08/1.48  --prep_def_merge                        true
% 7.08/1.48  --prep_def_merge_prop_impl              false
% 7.08/1.48  --prep_def_merge_mbd                    true
% 7.08/1.48  --prep_def_merge_tr_red                 false
% 7.08/1.48  --prep_def_merge_tr_cl                  false
% 7.08/1.48  --smt_preprocessing                     true
% 7.08/1.48  --smt_ac_axioms                         fast
% 7.08/1.48  --preprocessed_out                      false
% 7.08/1.48  --preprocessed_stats                    false
% 7.08/1.48  
% 7.08/1.48  ------ Abstraction refinement Options
% 7.08/1.48  
% 7.08/1.48  --abstr_ref                             []
% 7.08/1.48  --abstr_ref_prep                        false
% 7.08/1.48  --abstr_ref_until_sat                   false
% 7.08/1.48  --abstr_ref_sig_restrict                funpre
% 7.08/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.08/1.48  --abstr_ref_under                       []
% 7.08/1.48  
% 7.08/1.48  ------ SAT Options
% 7.08/1.48  
% 7.08/1.48  --sat_mode                              false
% 7.08/1.48  --sat_fm_restart_options                ""
% 7.08/1.48  --sat_gr_def                            false
% 7.08/1.48  --sat_epr_types                         true
% 7.08/1.48  --sat_non_cyclic_types                  false
% 7.08/1.48  --sat_finite_models                     false
% 7.08/1.48  --sat_fm_lemmas                         false
% 7.08/1.48  --sat_fm_prep                           false
% 7.08/1.48  --sat_fm_uc_incr                        true
% 7.08/1.48  --sat_out_model                         small
% 7.08/1.48  --sat_out_clauses                       false
% 7.08/1.48  
% 7.08/1.48  ------ QBF Options
% 7.08/1.48  
% 7.08/1.48  --qbf_mode                              false
% 7.08/1.48  --qbf_elim_univ                         false
% 7.08/1.48  --qbf_dom_inst                          none
% 7.08/1.48  --qbf_dom_pre_inst                      false
% 7.08/1.48  --qbf_sk_in                             false
% 7.08/1.48  --qbf_pred_elim                         true
% 7.08/1.48  --qbf_split                             512
% 7.08/1.48  
% 7.08/1.48  ------ BMC1 Options
% 7.08/1.48  
% 7.08/1.48  --bmc1_incremental                      false
% 7.08/1.48  --bmc1_axioms                           reachable_all
% 7.08/1.48  --bmc1_min_bound                        0
% 7.08/1.48  --bmc1_max_bound                        -1
% 7.08/1.48  --bmc1_max_bound_default                -1
% 7.08/1.48  --bmc1_symbol_reachability              true
% 7.08/1.48  --bmc1_property_lemmas                  false
% 7.08/1.48  --bmc1_k_induction                      false
% 7.08/1.48  --bmc1_non_equiv_states                 false
% 7.08/1.48  --bmc1_deadlock                         false
% 7.08/1.48  --bmc1_ucm                              false
% 7.08/1.48  --bmc1_add_unsat_core                   none
% 7.08/1.48  --bmc1_unsat_core_children              false
% 7.08/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.08/1.48  --bmc1_out_stat                         full
% 7.08/1.48  --bmc1_ground_init                      false
% 7.08/1.48  --bmc1_pre_inst_next_state              false
% 7.08/1.48  --bmc1_pre_inst_state                   false
% 7.08/1.48  --bmc1_pre_inst_reach_state             false
% 7.08/1.48  --bmc1_out_unsat_core                   false
% 7.08/1.48  --bmc1_aig_witness_out                  false
% 7.08/1.48  --bmc1_verbose                          false
% 7.08/1.48  --bmc1_dump_clauses_tptp                false
% 7.08/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.08/1.48  --bmc1_dump_file                        -
% 7.08/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.08/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.08/1.48  --bmc1_ucm_extend_mode                  1
% 7.08/1.48  --bmc1_ucm_init_mode                    2
% 7.08/1.48  --bmc1_ucm_cone_mode                    none
% 7.08/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.08/1.48  --bmc1_ucm_relax_model                  4
% 7.08/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.08/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.08/1.48  --bmc1_ucm_layered_model                none
% 7.08/1.48  --bmc1_ucm_max_lemma_size               10
% 7.08/1.48  
% 7.08/1.48  ------ AIG Options
% 7.08/1.48  
% 7.08/1.48  --aig_mode                              false
% 7.08/1.48  
% 7.08/1.48  ------ Instantiation Options
% 7.08/1.48  
% 7.08/1.48  --instantiation_flag                    true
% 7.08/1.48  --inst_sos_flag                         false
% 7.08/1.48  --inst_sos_phase                        true
% 7.08/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.08/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.08/1.48  --inst_lit_sel_side                     none
% 7.08/1.48  --inst_solver_per_active                1400
% 7.08/1.48  --inst_solver_calls_frac                1.
% 7.08/1.48  --inst_passive_queue_type               priority_queues
% 7.08/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.08/1.48  --inst_passive_queues_freq              [25;2]
% 7.08/1.48  --inst_dismatching                      true
% 7.08/1.48  --inst_eager_unprocessed_to_passive     true
% 7.08/1.48  --inst_prop_sim_given                   true
% 7.08/1.48  --inst_prop_sim_new                     false
% 7.08/1.48  --inst_subs_new                         false
% 7.08/1.48  --inst_eq_res_simp                      false
% 7.08/1.48  --inst_subs_given                       false
% 7.08/1.48  --inst_orphan_elimination               true
% 7.08/1.48  --inst_learning_loop_flag               true
% 7.08/1.48  --inst_learning_start                   3000
% 7.08/1.48  --inst_learning_factor                  2
% 7.08/1.48  --inst_start_prop_sim_after_learn       3
% 7.08/1.48  --inst_sel_renew                        solver
% 7.08/1.48  --inst_lit_activity_flag                true
% 7.08/1.48  --inst_restr_to_given                   false
% 7.08/1.48  --inst_activity_threshold               500
% 7.08/1.48  --inst_out_proof                        true
% 7.08/1.48  
% 7.08/1.48  ------ Resolution Options
% 7.08/1.48  
% 7.08/1.48  --resolution_flag                       false
% 7.08/1.48  --res_lit_sel                           adaptive
% 7.08/1.48  --res_lit_sel_side                      none
% 7.08/1.48  --res_ordering                          kbo
% 7.08/1.48  --res_to_prop_solver                    active
% 7.08/1.48  --res_prop_simpl_new                    false
% 7.08/1.48  --res_prop_simpl_given                  true
% 7.08/1.48  --res_passive_queue_type                priority_queues
% 7.08/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.08/1.48  --res_passive_queues_freq               [15;5]
% 7.08/1.48  --res_forward_subs                      full
% 7.08/1.48  --res_backward_subs                     full
% 7.08/1.48  --res_forward_subs_resolution           true
% 7.08/1.48  --res_backward_subs_resolution          true
% 7.08/1.48  --res_orphan_elimination                true
% 7.08/1.48  --res_time_limit                        2.
% 7.08/1.48  --res_out_proof                         true
% 7.08/1.48  
% 7.08/1.48  ------ Superposition Options
% 7.08/1.48  
% 7.08/1.48  --superposition_flag                    true
% 7.08/1.48  --sup_passive_queue_type                priority_queues
% 7.08/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.08/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.08/1.48  --demod_completeness_check              fast
% 7.08/1.48  --demod_use_ground                      true
% 7.08/1.48  --sup_to_prop_solver                    passive
% 7.08/1.48  --sup_prop_simpl_new                    true
% 7.08/1.48  --sup_prop_simpl_given                  true
% 7.08/1.48  --sup_fun_splitting                     false
% 7.08/1.48  --sup_smt_interval                      50000
% 7.08/1.48  
% 7.08/1.48  ------ Superposition Simplification Setup
% 7.08/1.48  
% 7.08/1.48  --sup_indices_passive                   []
% 7.08/1.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.08/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.08/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.48  --sup_full_bw                           [BwDemod]
% 7.08/1.48  --sup_immed_triv                        [TrivRules]
% 7.08/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.08/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.48  --sup_immed_bw_main                     []
% 7.08/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.08/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.08/1.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.08/1.48  
% 7.08/1.48  ------ Combination Options
% 7.08/1.48  
% 7.08/1.48  --comb_res_mult                         3
% 7.08/1.48  --comb_sup_mult                         2
% 7.08/1.48  --comb_inst_mult                        10
% 7.08/1.48  
% 7.08/1.48  ------ Debug Options
% 7.08/1.48  
% 7.08/1.48  --dbg_backtrace                         false
% 7.08/1.48  --dbg_dump_prop_clauses                 false
% 7.08/1.48  --dbg_dump_prop_clauses_file            -
% 7.08/1.48  --dbg_out_stat                          false
% 7.08/1.48  
% 7.08/1.48  
% 7.08/1.48  
% 7.08/1.48  
% 7.08/1.48  ------ Proving...
% 7.08/1.48  
% 7.08/1.48  
% 7.08/1.48  % SZS status Theorem for theBenchmark.p
% 7.08/1.48  
% 7.08/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.08/1.48  
% 7.08/1.48  fof(f15,conjecture,(
% 7.08/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f16,negated_conjecture,(
% 7.08/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.08/1.48    inference(negated_conjecture,[],[f15])).
% 7.08/1.48  
% 7.08/1.48  fof(f37,plain,(
% 7.08/1.48    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.08/1.48    inference(ennf_transformation,[],[f16])).
% 7.08/1.48  
% 7.08/1.48  fof(f38,plain,(
% 7.08/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.08/1.48    inference(flattening,[],[f37])).
% 7.08/1.48  
% 7.08/1.48  fof(f42,plain,(
% 7.08/1.48    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.08/1.48    introduced(choice_axiom,[])).
% 7.08/1.48  
% 7.08/1.48  fof(f41,plain,(
% 7.08/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.08/1.48    introduced(choice_axiom,[])).
% 7.08/1.48  
% 7.08/1.48  fof(f43,plain,(
% 7.08/1.48    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.08/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).
% 7.08/1.48  
% 7.08/1.48  fof(f68,plain,(
% 7.08/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.08/1.48    inference(cnf_transformation,[],[f43])).
% 7.08/1.48  
% 7.08/1.48  fof(f7,axiom,(
% 7.08/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f26,plain,(
% 7.08/1.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.08/1.48    inference(ennf_transformation,[],[f7])).
% 7.08/1.48  
% 7.08/1.48  fof(f51,plain,(
% 7.08/1.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.08/1.48    inference(cnf_transformation,[],[f26])).
% 7.08/1.48  
% 7.08/1.48  fof(f72,plain,(
% 7.08/1.48    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.08/1.48    inference(cnf_transformation,[],[f43])).
% 7.08/1.48  
% 7.08/1.48  fof(f71,plain,(
% 7.08/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.08/1.48    inference(cnf_transformation,[],[f43])).
% 7.08/1.48  
% 7.08/1.48  fof(f9,axiom,(
% 7.08/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f29,plain,(
% 7.08/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.08/1.48    inference(ennf_transformation,[],[f9])).
% 7.08/1.48  
% 7.08/1.48  fof(f30,plain,(
% 7.08/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.08/1.48    inference(flattening,[],[f29])).
% 7.08/1.48  
% 7.08/1.48  fof(f40,plain,(
% 7.08/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.08/1.48    inference(nnf_transformation,[],[f30])).
% 7.08/1.48  
% 7.08/1.48  fof(f54,plain,(
% 7.08/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.08/1.48    inference(cnf_transformation,[],[f40])).
% 7.08/1.48  
% 7.08/1.48  fof(f6,axiom,(
% 7.08/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f25,plain,(
% 7.08/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.08/1.48    inference(ennf_transformation,[],[f6])).
% 7.08/1.48  
% 7.08/1.48  fof(f50,plain,(
% 7.08/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.08/1.48    inference(cnf_transformation,[],[f25])).
% 7.08/1.48  
% 7.08/1.48  fof(f70,plain,(
% 7.08/1.48    v1_funct_2(sK3,sK1,sK0)),
% 7.08/1.48    inference(cnf_transformation,[],[f43])).
% 7.08/1.48  
% 7.08/1.48  fof(f75,plain,(
% 7.08/1.48    k1_xboole_0 != sK0),
% 7.08/1.48    inference(cnf_transformation,[],[f43])).
% 7.08/1.48  
% 7.08/1.48  fof(f1,axiom,(
% 7.08/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f18,plain,(
% 7.08/1.48    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.08/1.48    inference(ennf_transformation,[],[f1])).
% 7.08/1.48  
% 7.08/1.48  fof(f19,plain,(
% 7.08/1.48    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.08/1.48    inference(flattening,[],[f18])).
% 7.08/1.48  
% 7.08/1.48  fof(f45,plain,(
% 7.08/1.48    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.08/1.48    inference(cnf_transformation,[],[f19])).
% 7.08/1.48  
% 7.08/1.48  fof(f69,plain,(
% 7.08/1.48    v1_funct_1(sK3)),
% 7.08/1.48    inference(cnf_transformation,[],[f43])).
% 7.08/1.48  
% 7.08/1.48  fof(f5,axiom,(
% 7.08/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f24,plain,(
% 7.08/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.08/1.48    inference(ennf_transformation,[],[f5])).
% 7.08/1.48  
% 7.08/1.48  fof(f49,plain,(
% 7.08/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.08/1.48    inference(cnf_transformation,[],[f24])).
% 7.08/1.48  
% 7.08/1.48  fof(f12,axiom,(
% 7.08/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f33,plain,(
% 7.08/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.08/1.48    inference(ennf_transformation,[],[f12])).
% 7.08/1.48  
% 7.08/1.48  fof(f34,plain,(
% 7.08/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.08/1.48    inference(flattening,[],[f33])).
% 7.08/1.48  
% 7.08/1.48  fof(f63,plain,(
% 7.08/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.08/1.48    inference(cnf_transformation,[],[f34])).
% 7.08/1.48  
% 7.08/1.48  fof(f66,plain,(
% 7.08/1.48    v1_funct_1(sK2)),
% 7.08/1.48    inference(cnf_transformation,[],[f43])).
% 7.08/1.48  
% 7.08/1.48  fof(f8,axiom,(
% 7.08/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f27,plain,(
% 7.08/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.08/1.48    inference(ennf_transformation,[],[f8])).
% 7.08/1.48  
% 7.08/1.48  fof(f28,plain,(
% 7.08/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.08/1.48    inference(flattening,[],[f27])).
% 7.08/1.48  
% 7.08/1.48  fof(f39,plain,(
% 7.08/1.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.08/1.48    inference(nnf_transformation,[],[f28])).
% 7.08/1.48  
% 7.08/1.48  fof(f52,plain,(
% 7.08/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.08/1.48    inference(cnf_transformation,[],[f39])).
% 7.08/1.48  
% 7.08/1.48  fof(f73,plain,(
% 7.08/1.48    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.08/1.48    inference(cnf_transformation,[],[f43])).
% 7.08/1.48  
% 7.08/1.48  fof(f11,axiom,(
% 7.08/1.48    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f17,plain,(
% 7.08/1.48    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.08/1.48    inference(pure_predicate_removal,[],[f11])).
% 7.08/1.48  
% 7.08/1.48  fof(f62,plain,(
% 7.08/1.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.08/1.48    inference(cnf_transformation,[],[f17])).
% 7.08/1.48  
% 7.08/1.48  fof(f10,axiom,(
% 7.08/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f31,plain,(
% 7.08/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.08/1.48    inference(ennf_transformation,[],[f10])).
% 7.08/1.48  
% 7.08/1.48  fof(f32,plain,(
% 7.08/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.08/1.48    inference(flattening,[],[f31])).
% 7.08/1.48  
% 7.08/1.48  fof(f61,plain,(
% 7.08/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.08/1.48    inference(cnf_transformation,[],[f32])).
% 7.08/1.48  
% 7.08/1.48  fof(f2,axiom,(
% 7.08/1.48    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f46,plain,(
% 7.08/1.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.08/1.48    inference(cnf_transformation,[],[f2])).
% 7.08/1.48  
% 7.08/1.48  fof(f13,axiom,(
% 7.08/1.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f64,plain,(
% 7.08/1.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.08/1.48    inference(cnf_transformation,[],[f13])).
% 7.08/1.48  
% 7.08/1.48  fof(f78,plain,(
% 7.08/1.48    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.08/1.48    inference(definition_unfolding,[],[f46,f64])).
% 7.08/1.48  
% 7.08/1.48  fof(f3,axiom,(
% 7.08/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f20,plain,(
% 7.08/1.48    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.08/1.48    inference(ennf_transformation,[],[f3])).
% 7.08/1.48  
% 7.08/1.48  fof(f21,plain,(
% 7.08/1.48    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.08/1.48    inference(flattening,[],[f20])).
% 7.08/1.48  
% 7.08/1.48  fof(f47,plain,(
% 7.08/1.48    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.08/1.48    inference(cnf_transformation,[],[f21])).
% 7.08/1.48  
% 7.08/1.48  fof(f79,plain,(
% 7.08/1.48    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.08/1.48    inference(definition_unfolding,[],[f47,f64])).
% 7.08/1.48  
% 7.08/1.48  fof(f14,axiom,(
% 7.08/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.08/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.48  
% 7.08/1.48  fof(f35,plain,(
% 7.08/1.48    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.08/1.48    inference(ennf_transformation,[],[f14])).
% 7.08/1.48  
% 7.08/1.48  fof(f36,plain,(
% 7.08/1.48    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.08/1.48    inference(flattening,[],[f35])).
% 7.08/1.48  
% 7.08/1.48  fof(f65,plain,(
% 7.08/1.48    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.08/1.49    inference(cnf_transformation,[],[f36])).
% 7.08/1.49  
% 7.08/1.49  fof(f67,plain,(
% 7.08/1.49    v1_funct_2(sK2,sK0,sK1)),
% 7.08/1.49    inference(cnf_transformation,[],[f43])).
% 7.08/1.49  
% 7.08/1.49  fof(f4,axiom,(
% 7.08/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 7.08/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.08/1.49  
% 7.08/1.49  fof(f22,plain,(
% 7.08/1.49    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.08/1.49    inference(ennf_transformation,[],[f4])).
% 7.08/1.49  
% 7.08/1.49  fof(f23,plain,(
% 7.08/1.49    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.08/1.49    inference(flattening,[],[f22])).
% 7.08/1.49  
% 7.08/1.49  fof(f48,plain,(
% 7.08/1.49    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.08/1.49    inference(cnf_transformation,[],[f23])).
% 7.08/1.49  
% 7.08/1.49  fof(f77,plain,(
% 7.08/1.49    k2_funct_1(sK2) != sK3),
% 7.08/1.49    inference(cnf_transformation,[],[f43])).
% 7.08/1.49  
% 7.08/1.49  cnf(c_30,negated_conjecture,
% 7.08/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.08/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1102,plain,
% 7.08/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_7,plain,
% 7.08/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.08/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.08/1.49      inference(cnf_transformation,[],[f51]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1117,plain,
% 7.08/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.08/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2056,plain,
% 7.08/1.49      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_1102,c_1117]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_26,negated_conjecture,
% 7.08/1.49      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.08/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2058,plain,
% 7.08/1.49      ( k2_relat_1(sK2) = sK1 ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_2056,c_26]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_27,negated_conjecture,
% 7.08/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.08/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1105,plain,
% 7.08/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_15,plain,
% 7.08/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.08/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.08/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.08/1.49      | k1_xboole_0 = X2 ),
% 7.08/1.49      inference(cnf_transformation,[],[f54]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1111,plain,
% 7.08/1.49      ( k1_relset_1(X0,X1,X2) = X0
% 7.08/1.49      | k1_xboole_0 = X1
% 7.08/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.08/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3029,plain,
% 7.08/1.49      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 7.08/1.49      | sK0 = k1_xboole_0
% 7.08/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_1105,c_1111]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_6,plain,
% 7.08/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.08/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.08/1.49      inference(cnf_transformation,[],[f50]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1118,plain,
% 7.08/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.08/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2135,plain,
% 7.08/1.49      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_1105,c_1118]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3041,plain,
% 7.08/1.49      ( k1_relat_1(sK3) = sK1
% 7.08/1.49      | sK0 = k1_xboole_0
% 7.08/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_3029,c_2135]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_28,negated_conjecture,
% 7.08/1.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.08/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_37,plain,
% 7.08/1.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_23,negated_conjecture,
% 7.08/1.49      ( k1_xboole_0 != sK0 ),
% 7.08/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_619,plain,( X0 = X0 ),theory(equality) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_644,plain,
% 7.08/1.49      ( k1_xboole_0 = k1_xboole_0 ),
% 7.08/1.49      inference(instantiation,[status(thm)],[c_619]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_620,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1444,plain,
% 7.08/1.49      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 7.08/1.49      inference(instantiation,[status(thm)],[c_620]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1445,plain,
% 7.08/1.49      ( sK0 != k1_xboole_0
% 7.08/1.49      | k1_xboole_0 = sK0
% 7.08/1.49      | k1_xboole_0 != k1_xboole_0 ),
% 7.08/1.49      inference(instantiation,[status(thm)],[c_1444]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3255,plain,
% 7.08/1.49      ( k1_relat_1(sK3) = sK1 ),
% 7.08/1.49      inference(global_propositional_subsumption,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_3041,c_37,c_23,c_644,c_1445]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_0,plain,
% 7.08/1.49      ( ~ v1_relat_1(X0)
% 7.08/1.49      | ~ v1_relat_1(X1)
% 7.08/1.49      | ~ v1_funct_1(X0)
% 7.08/1.49      | ~ v1_funct_1(X1)
% 7.08/1.49      | v2_funct_1(X1)
% 7.08/1.49      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 7.08/1.49      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 7.08/1.49      inference(cnf_transformation,[],[f45]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1124,plain,
% 7.08/1.49      ( k1_relat_1(X0) != k2_relat_1(X1)
% 7.08/1.49      | v1_relat_1(X1) != iProver_top
% 7.08/1.49      | v1_relat_1(X0) != iProver_top
% 7.08/1.49      | v1_funct_1(X1) != iProver_top
% 7.08/1.49      | v1_funct_1(X0) != iProver_top
% 7.08/1.49      | v2_funct_1(X0) = iProver_top
% 7.08/1.49      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3887,plain,
% 7.08/1.49      ( k2_relat_1(X0) != sK1
% 7.08/1.49      | v1_relat_1(X0) != iProver_top
% 7.08/1.49      | v1_relat_1(sK3) != iProver_top
% 7.08/1.49      | v1_funct_1(X0) != iProver_top
% 7.08/1.49      | v1_funct_1(sK3) != iProver_top
% 7.08/1.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 7.08/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_3255,c_1124]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_29,negated_conjecture,
% 7.08/1.49      ( v1_funct_1(sK3) ),
% 7.08/1.49      inference(cnf_transformation,[],[f69]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_36,plain,
% 7.08/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_38,plain,
% 7.08/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_5,plain,
% 7.08/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.08/1.49      | v1_relat_1(X0) ),
% 7.08/1.49      inference(cnf_transformation,[],[f49]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1406,plain,
% 7.08/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.08/1.49      | v1_relat_1(sK3) ),
% 7.08/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1407,plain,
% 7.08/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.08/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_1406]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_18834,plain,
% 7.08/1.49      ( v1_funct_1(X0) != iProver_top
% 7.08/1.49      | k2_relat_1(X0) != sK1
% 7.08/1.49      | v1_relat_1(X0) != iProver_top
% 7.08/1.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 7.08/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.08/1.49      inference(global_propositional_subsumption,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_3887,c_36,c_38,c_1407]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_18835,plain,
% 7.08/1.49      ( k2_relat_1(X0) != sK1
% 7.08/1.49      | v1_relat_1(X0) != iProver_top
% 7.08/1.49      | v1_funct_1(X0) != iProver_top
% 7.08/1.49      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 7.08/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.08/1.49      inference(renaming,[status(thm)],[c_18834]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_18846,plain,
% 7.08/1.49      ( v1_relat_1(sK2) != iProver_top
% 7.08/1.49      | v1_funct_1(sK2) != iProver_top
% 7.08/1.49      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 7.08/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_2058,c_18835]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_19,plain,
% 7.08/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.08/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.08/1.49      | ~ v1_funct_1(X0)
% 7.08/1.49      | ~ v1_funct_1(X3)
% 7.08/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.08/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1107,plain,
% 7.08/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.08/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.08/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.08/1.49      | v1_funct_1(X4) != iProver_top
% 7.08/1.49      | v1_funct_1(X5) != iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3373,plain,
% 7.08/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.08/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.08/1.49      | v1_funct_1(X2) != iProver_top
% 7.08/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_1105,c_1107]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3428,plain,
% 7.08/1.49      ( v1_funct_1(X2) != iProver_top
% 7.08/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.08/1.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.08/1.49      inference(global_propositional_subsumption,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_3373,c_36]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3429,plain,
% 7.08/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.08/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.08/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.08/1.49      inference(renaming,[status(thm)],[c_3428]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3439,plain,
% 7.08/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.08/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_1102,c_3429]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_32,negated_conjecture,
% 7.08/1.49      ( v1_funct_1(sK2) ),
% 7.08/1.49      inference(cnf_transformation,[],[f66]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1543,plain,
% 7.08/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.08/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.08/1.49      | ~ v1_funct_1(X0)
% 7.08/1.49      | ~ v1_funct_1(sK3)
% 7.08/1.49      | k1_partfun1(X1,X2,X3,X4,X0,sK3) = k5_relat_1(X0,sK3) ),
% 7.08/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1818,plain,
% 7.08/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.08/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.08/1.49      | ~ v1_funct_1(sK3)
% 7.08/1.49      | ~ v1_funct_1(sK2)
% 7.08/1.49      | k1_partfun1(X2,X3,X0,X1,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.08/1.49      inference(instantiation,[status(thm)],[c_1543]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2095,plain,
% 7.08/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.08/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.08/1.49      | ~ v1_funct_1(sK3)
% 7.08/1.49      | ~ v1_funct_1(sK2)
% 7.08/1.49      | k1_partfun1(X0,X1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.08/1.49      inference(instantiation,[status(thm)],[c_1818]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2153,plain,
% 7.08/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.08/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.08/1.49      | ~ v1_funct_1(sK3)
% 7.08/1.49      | ~ v1_funct_1(sK2)
% 7.08/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.08/1.49      inference(instantiation,[status(thm)],[c_2095]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3949,plain,
% 7.08/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 7.08/1.49      inference(global_propositional_subsumption,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_3439,c_32,c_30,c_29,c_27,c_2153]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_9,plain,
% 7.08/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.08/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.08/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.08/1.49      | X3 = X2 ),
% 7.08/1.49      inference(cnf_transformation,[],[f52]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_25,negated_conjecture,
% 7.08/1.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.08/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_361,plain,
% 7.08/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.08/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.08/1.49      | X3 = X0
% 7.08/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.08/1.49      | k6_partfun1(sK0) != X3
% 7.08/1.49      | sK0 != X2
% 7.08/1.49      | sK0 != X1 ),
% 7.08/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_362,plain,
% 7.08/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.08/1.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.08/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.08/1.49      inference(unflattening,[status(thm)],[c_361]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_18,plain,
% 7.08/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.08/1.49      inference(cnf_transformation,[],[f62]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_370,plain,
% 7.08/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.08/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.08/1.49      inference(forward_subsumption_resolution,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_362,c_18]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1098,plain,
% 7.08/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.08/1.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3952,plain,
% 7.08/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.08/1.49      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_3949,c_1098]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_33,plain,
% 7.08/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_35,plain,
% 7.08/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_16,plain,
% 7.08/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.08/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.08/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.08/1.49      | ~ v1_funct_1(X0)
% 7.08/1.49      | ~ v1_funct_1(X3) ),
% 7.08/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1110,plain,
% 7.08/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.08/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.08/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 7.08/1.49      | v1_funct_1(X3) != iProver_top
% 7.08/1.49      | v1_funct_1(X0) != iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3978,plain,
% 7.08/1.49      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 7.08/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.08/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.08/1.49      | v1_funct_1(sK3) != iProver_top
% 7.08/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_3949,c_1110]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_4192,plain,
% 7.08/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.08/1.49      inference(global_propositional_subsumption,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_3952,c_33,c_35,c_36,c_38,c_3978]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_18851,plain,
% 7.08/1.49      ( v1_relat_1(sK2) != iProver_top
% 7.08/1.49      | v1_funct_1(sK2) != iProver_top
% 7.08/1.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.08/1.49      | v2_funct_1(sK3) = iProver_top ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_18846,c_4192]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1409,plain,
% 7.08/1.49      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.08/1.49      | v1_relat_1(sK2) ),
% 7.08/1.49      inference(instantiation,[status(thm)],[c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1410,plain,
% 7.08/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.08/1.49      | v1_relat_1(sK2) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_1409]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2,plain,
% 7.08/1.49      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.08/1.49      inference(cnf_transformation,[],[f78]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_13934,plain,
% 7.08/1.49      ( v2_funct_1(k6_partfun1(sK0)) ),
% 7.08/1.49      inference(instantiation,[status(thm)],[c_2]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_13935,plain,
% 7.08/1.49      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_13934]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_18980,plain,
% 7.08/1.49      ( v2_funct_1(sK3) = iProver_top ),
% 7.08/1.49      inference(global_propositional_subsumption,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_18851,c_33,c_35,c_1410,c_13935]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_3,plain,
% 7.08/1.49      ( ~ v1_relat_1(X0)
% 7.08/1.49      | ~ v1_relat_1(X1)
% 7.08/1.49      | ~ v1_funct_1(X0)
% 7.08/1.49      | ~ v1_funct_1(X1)
% 7.08/1.49      | ~ v2_funct_1(X1)
% 7.08/1.49      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.08/1.49      | k2_funct_1(X1) = X0
% 7.08/1.49      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 7.08/1.49      inference(cnf_transformation,[],[f79]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1121,plain,
% 7.08/1.49      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 7.08/1.49      | k2_funct_1(X1) = X0
% 7.08/1.49      | k1_relat_1(X1) != k2_relat_1(X0)
% 7.08/1.49      | v1_relat_1(X0) != iProver_top
% 7.08/1.49      | v1_relat_1(X1) != iProver_top
% 7.08/1.49      | v1_funct_1(X0) != iProver_top
% 7.08/1.49      | v1_funct_1(X1) != iProver_top
% 7.08/1.49      | v2_funct_1(X1) != iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_4196,plain,
% 7.08/1.49      ( k2_funct_1(sK3) = sK2
% 7.08/1.49      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 7.08/1.49      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 7.08/1.49      | v1_relat_1(sK3) != iProver_top
% 7.08/1.49      | v1_relat_1(sK2) != iProver_top
% 7.08/1.49      | v1_funct_1(sK3) != iProver_top
% 7.08/1.49      | v1_funct_1(sK2) != iProver_top
% 7.08/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_4192,c_1121]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2055,plain,
% 7.08/1.49      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_1105,c_1117]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_20,plain,
% 7.08/1.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.08/1.49      | ~ v1_funct_2(X3,X1,X0)
% 7.08/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.08/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.08/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.08/1.49      | ~ v1_funct_1(X2)
% 7.08/1.49      | ~ v1_funct_1(X3)
% 7.08/1.49      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.08/1.49      inference(cnf_transformation,[],[f65]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_374,plain,
% 7.08/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.08/1.49      | ~ v1_funct_2(X3,X2,X1)
% 7.08/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.08/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.08/1.49      | ~ v1_funct_1(X3)
% 7.08/1.49      | ~ v1_funct_1(X0)
% 7.08/1.49      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.08/1.49      | k2_relset_1(X2,X1,X3) = X1
% 7.08/1.49      | k6_partfun1(X1) != k6_partfun1(sK0)
% 7.08/1.49      | sK0 != X1 ),
% 7.08/1.49      inference(resolution_lifted,[status(thm)],[c_20,c_25]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_375,plain,
% 7.08/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.08/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.08/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.08/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.08/1.49      | ~ v1_funct_1(X2)
% 7.08/1.49      | ~ v1_funct_1(X0)
% 7.08/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.08/1.49      | k2_relset_1(X1,sK0,X0) = sK0
% 7.08/1.49      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.08/1.49      inference(unflattening,[status(thm)],[c_374]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_457,plain,
% 7.08/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.08/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.08/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.08/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.08/1.49      | ~ v1_funct_1(X0)
% 7.08/1.49      | ~ v1_funct_1(X2)
% 7.08/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.08/1.49      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.08/1.49      inference(equality_resolution_simp,[status(thm)],[c_375]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1097,plain,
% 7.08/1.49      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.08/1.49      | k2_relset_1(X0,sK0,X2) = sK0
% 7.08/1.49      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.08/1.49      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.08/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.08/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.08/1.49      | v1_funct_1(X1) != iProver_top
% 7.08/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1607,plain,
% 7.08/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.08/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.08/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.08/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.08/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.08/1.49      | v1_funct_1(sK3) != iProver_top
% 7.08/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.08/1.49      inference(equality_resolution,[status(thm)],[c_1097]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_31,negated_conjecture,
% 7.08/1.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.08/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_34,plain,
% 7.08/1.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1864,plain,
% 7.08/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.08/1.49      inference(global_propositional_subsumption,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_1607,c_33,c_34,c_35,c_36,c_37,c_38]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2061,plain,
% 7.08/1.49      ( k2_relat_1(sK3) = sK0 ),
% 7.08/1.49      inference(light_normalisation,[status(thm)],[c_2055,c_1864]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_4197,plain,
% 7.08/1.49      ( k2_funct_1(sK3) = sK2
% 7.08/1.49      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 7.08/1.49      | sK1 != sK1
% 7.08/1.49      | v1_relat_1(sK3) != iProver_top
% 7.08/1.49      | v1_relat_1(sK2) != iProver_top
% 7.08/1.49      | v1_funct_1(sK3) != iProver_top
% 7.08/1.49      | v1_funct_1(sK2) != iProver_top
% 7.08/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.08/1.49      inference(light_normalisation,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_4196,c_2058,c_2061,c_3255]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_4198,plain,
% 7.08/1.49      ( k2_funct_1(sK3) = sK2
% 7.08/1.49      | v1_relat_1(sK3) != iProver_top
% 7.08/1.49      | v1_relat_1(sK2) != iProver_top
% 7.08/1.49      | v1_funct_1(sK3) != iProver_top
% 7.08/1.49      | v1_funct_1(sK2) != iProver_top
% 7.08/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.08/1.49      inference(equality_resolution_simp,[status(thm)],[c_4197]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_5435,plain,
% 7.08/1.49      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 7.08/1.49      inference(global_propositional_subsumption,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_4198,c_33,c_35,c_36,c_38,c_1407,c_1410]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_18985,plain,
% 7.08/1.49      ( k2_funct_1(sK3) = sK2 ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_18980,c_5435]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1119,plain,
% 7.08/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.08/1.49      | v1_relat_1(X0) = iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1957,plain,
% 7.08/1.49      ( v1_relat_1(sK3) = iProver_top ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_1105,c_1119]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_4,plain,
% 7.08/1.49      ( ~ v1_relat_1(X0)
% 7.08/1.49      | ~ v1_funct_1(X0)
% 7.08/1.49      | ~ v2_funct_1(X0)
% 7.08/1.49      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 7.08/1.49      inference(cnf_transformation,[],[f48]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_1120,plain,
% 7.08/1.49      ( k2_funct_1(k2_funct_1(X0)) = X0
% 7.08/1.49      | v1_relat_1(X0) != iProver_top
% 7.08/1.49      | v1_funct_1(X0) != iProver_top
% 7.08/1.49      | v2_funct_1(X0) != iProver_top ),
% 7.08/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2194,plain,
% 7.08/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.08/1.49      | v1_funct_1(sK3) != iProver_top
% 7.08/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_1957,c_1120]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_2366,plain,
% 7.08/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 7.08/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.08/1.49      inference(global_propositional_subsumption,
% 7.08/1.49                [status(thm)],
% 7.08/1.49                [c_2194,c_36]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_18986,plain,
% 7.08/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 7.08/1.49      inference(superposition,[status(thm)],[c_18980,c_2366]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_18990,plain,
% 7.08/1.49      ( k2_funct_1(sK2) = sK3 ),
% 7.08/1.49      inference(demodulation,[status(thm)],[c_18985,c_18986]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(c_21,negated_conjecture,
% 7.08/1.49      ( k2_funct_1(sK2) != sK3 ),
% 7.08/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.08/1.49  
% 7.08/1.49  cnf(contradiction,plain,
% 7.08/1.49      ( $false ),
% 7.08/1.49      inference(minisat,[status(thm)],[c_18990,c_21]) ).
% 7.08/1.49  
% 7.08/1.49  
% 7.08/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.08/1.49  
% 7.08/1.49  ------                               Statistics
% 7.08/1.49  
% 7.08/1.49  ------ General
% 7.08/1.49  
% 7.08/1.49  abstr_ref_over_cycles:                  0
% 7.08/1.49  abstr_ref_under_cycles:                 0
% 7.08/1.49  gc_basic_clause_elim:                   0
% 7.08/1.49  forced_gc_time:                         0
% 7.08/1.49  parsing_time:                           0.009
% 7.08/1.49  unif_index_cands_time:                  0.
% 7.08/1.49  unif_index_add_time:                    0.
% 7.08/1.49  orderings_time:                         0.
% 7.08/1.49  out_proof_time:                         0.013
% 7.08/1.49  total_time:                             0.625
% 7.08/1.49  num_of_symbols:                         52
% 7.08/1.49  num_of_terms:                           22230
% 7.08/1.49  
% 7.08/1.49  ------ Preprocessing
% 7.08/1.49  
% 7.08/1.49  num_of_splits:                          0
% 7.08/1.49  num_of_split_atoms:                     0
% 7.08/1.49  num_of_reused_defs:                     0
% 7.08/1.49  num_eq_ax_congr_red:                    21
% 7.08/1.49  num_of_sem_filtered_clauses:            1
% 7.08/1.49  num_of_subtypes:                        0
% 7.08/1.49  monotx_restored_types:                  0
% 7.08/1.49  sat_num_of_epr_types:                   0
% 7.08/1.49  sat_num_of_non_cyclic_types:            0
% 7.08/1.49  sat_guarded_non_collapsed_types:        0
% 7.08/1.49  num_pure_diseq_elim:                    0
% 7.08/1.49  simp_replaced_by:                       0
% 7.08/1.49  res_preprocessed:                       156
% 7.08/1.49  prep_upred:                             0
% 7.08/1.49  prep_unflattend:                        12
% 7.08/1.49  smt_new_axioms:                         0
% 7.08/1.49  pred_elim_cands:                        5
% 7.08/1.49  pred_elim:                              1
% 7.08/1.49  pred_elim_cl:                           1
% 7.08/1.49  pred_elim_cycles:                       3
% 7.08/1.49  merged_defs:                            0
% 7.08/1.49  merged_defs_ncl:                        0
% 7.08/1.49  bin_hyper_res:                          0
% 7.08/1.49  prep_cycles:                            4
% 7.08/1.49  pred_elim_time:                         0.004
% 7.08/1.49  splitting_time:                         0.
% 7.08/1.49  sem_filter_time:                        0.
% 7.08/1.49  monotx_time:                            0.
% 7.08/1.49  subtype_inf_time:                       0.
% 7.08/1.49  
% 7.08/1.49  ------ Problem properties
% 7.08/1.49  
% 7.08/1.49  clauses:                                32
% 7.08/1.49  conjectures:                            11
% 7.08/1.49  epr:                                    7
% 7.08/1.49  horn:                                   28
% 7.08/1.49  ground:                                 12
% 7.08/1.49  unary:                                  13
% 7.08/1.49  binary:                                 4
% 7.08/1.49  lits:                                   99
% 7.08/1.49  lits_eq:                                27
% 7.08/1.49  fd_pure:                                0
% 7.08/1.49  fd_pseudo:                              0
% 7.08/1.49  fd_cond:                                3
% 7.08/1.49  fd_pseudo_cond:                         1
% 7.08/1.49  ac_symbols:                             0
% 7.08/1.49  
% 7.08/1.49  ------ Propositional Solver
% 7.08/1.49  
% 7.08/1.49  prop_solver_calls:                      30
% 7.08/1.49  prop_fast_solver_calls:                 1964
% 7.08/1.49  smt_solver_calls:                       0
% 7.08/1.49  smt_fast_solver_calls:                  0
% 7.08/1.49  prop_num_of_clauses:                    8085
% 7.08/1.49  prop_preprocess_simplified:             13556
% 7.08/1.49  prop_fo_subsumed:                       230
% 7.08/1.49  prop_solver_time:                       0.
% 7.08/1.49  smt_solver_time:                        0.
% 7.08/1.49  smt_fast_solver_time:                   0.
% 7.08/1.49  prop_fast_solver_time:                  0.
% 7.08/1.49  prop_unsat_core_time:                   0.001
% 7.08/1.49  
% 7.08/1.49  ------ QBF
% 7.08/1.49  
% 7.08/1.49  qbf_q_res:                              0
% 7.08/1.49  qbf_num_tautologies:                    0
% 7.08/1.49  qbf_prep_cycles:                        0
% 7.08/1.49  
% 7.08/1.49  ------ BMC1
% 7.08/1.49  
% 7.08/1.49  bmc1_current_bound:                     -1
% 7.08/1.49  bmc1_last_solved_bound:                 -1
% 7.08/1.49  bmc1_unsat_core_size:                   -1
% 7.08/1.49  bmc1_unsat_core_parents_size:           -1
% 7.08/1.49  bmc1_merge_next_fun:                    0
% 7.08/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.08/1.49  
% 7.08/1.49  ------ Instantiation
% 7.08/1.49  
% 7.08/1.49  inst_num_of_clauses:                    2253
% 7.08/1.49  inst_num_in_passive:                    469
% 7.08/1.49  inst_num_in_active:                     1087
% 7.08/1.49  inst_num_in_unprocessed:                698
% 7.08/1.49  inst_num_of_loops:                      1160
% 7.08/1.49  inst_num_of_learning_restarts:          0
% 7.08/1.49  inst_num_moves_active_passive:          69
% 7.08/1.49  inst_lit_activity:                      0
% 7.08/1.49  inst_lit_activity_moves:                1
% 7.08/1.49  inst_num_tautologies:                   0
% 7.08/1.49  inst_num_prop_implied:                  0
% 7.08/1.49  inst_num_existing_simplified:           0
% 7.08/1.49  inst_num_eq_res_simplified:             0
% 7.08/1.49  inst_num_child_elim:                    0
% 7.08/1.49  inst_num_of_dismatching_blockings:      300
% 7.08/1.49  inst_num_of_non_proper_insts:           1560
% 7.08/1.49  inst_num_of_duplicates:                 0
% 7.08/1.49  inst_inst_num_from_inst_to_res:         0
% 7.08/1.49  inst_dismatching_checking_time:         0.
% 7.08/1.49  
% 7.08/1.49  ------ Resolution
% 7.08/1.49  
% 7.08/1.49  res_num_of_clauses:                     0
% 7.08/1.49  res_num_in_passive:                     0
% 7.08/1.49  res_num_in_active:                      0
% 7.08/1.49  res_num_of_loops:                       160
% 7.08/1.49  res_forward_subset_subsumed:            151
% 7.08/1.49  res_backward_subset_subsumed:           2
% 7.08/1.49  res_forward_subsumed:                   0
% 7.08/1.49  res_backward_subsumed:                  0
% 7.08/1.49  res_forward_subsumption_resolution:     2
% 7.08/1.49  res_backward_subsumption_resolution:    0
% 7.08/1.49  res_clause_to_clause_subsumption:       1368
% 7.08/1.49  res_orphan_elimination:                 0
% 7.08/1.49  res_tautology_del:                      52
% 7.08/1.49  res_num_eq_res_simplified:              1
% 7.08/1.49  res_num_sel_changes:                    0
% 7.08/1.49  res_moves_from_active_to_pass:          0
% 7.08/1.49  
% 7.08/1.49  ------ Superposition
% 7.08/1.49  
% 7.08/1.49  sup_time_total:                         0.
% 7.08/1.49  sup_time_generating:                    0.
% 7.08/1.49  sup_time_sim_full:                      0.
% 7.08/1.49  sup_time_sim_immed:                     0.
% 7.08/1.49  
% 7.08/1.49  sup_num_of_clauses:                     583
% 7.08/1.49  sup_num_in_active:                      225
% 7.08/1.49  sup_num_in_passive:                     358
% 7.08/1.49  sup_num_of_loops:                       230
% 7.08/1.49  sup_fw_superposition:                   306
% 7.08/1.49  sup_bw_superposition:                   310
% 7.08/1.49  sup_immediate_simplified:               169
% 7.08/1.49  sup_given_eliminated:                   0
% 7.08/1.49  comparisons_done:                       0
% 7.08/1.49  comparisons_avoided:                    1
% 7.08/1.49  
% 7.08/1.49  ------ Simplifications
% 7.08/1.49  
% 7.08/1.49  
% 7.08/1.49  sim_fw_subset_subsumed:                 23
% 7.08/1.49  sim_bw_subset_subsumed:                 8
% 7.08/1.49  sim_fw_subsumed:                        3
% 7.08/1.49  sim_bw_subsumed:                        0
% 7.08/1.49  sim_fw_subsumption_res:                 5
% 7.08/1.49  sim_bw_subsumption_res:                 0
% 7.08/1.49  sim_tautology_del:                      0
% 7.08/1.49  sim_eq_tautology_del:                   21
% 7.08/1.49  sim_eq_res_simp:                        1
% 7.08/1.49  sim_fw_demodulated:                     17
% 7.08/1.49  sim_bw_demodulated:                     6
% 7.08/1.49  sim_light_normalised:                   158
% 7.08/1.49  sim_joinable_taut:                      0
% 7.08/1.49  sim_joinable_simp:                      0
% 7.08/1.49  sim_ac_normalised:                      0
% 7.08/1.49  sim_smt_subsumption:                    0
% 7.08/1.49  
%------------------------------------------------------------------------------
