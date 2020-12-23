%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:31 EST 2020

% Result     : Theorem 46.90s
% Output     : CNFRefutation 46.90s
% Verified   : 
% Statistics : Number of formulae       :  272 (3594 expanded)
%              Number of clauses        :  196 (1044 expanded)
%              Number of leaves         :   20 ( 918 expanded)
%              Depth                    :   27
%              Number of atoms          : 1030 (30916 expanded)
%              Number of equality atoms :  615 (11509 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

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

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f11,axiom,(
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
    inference(ennf_transformation,[],[f11])).

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

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f71,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f13,axiom,(
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
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f33])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

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

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f75,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f14,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f56,f66])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f31])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f80,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f48,f66])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f49,f66])).

fof(f6,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f51,f66])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f67,plain,(
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

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f69,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f78,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f43])).

fof(f76,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_166915,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_166927,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_167463,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_166915,c_166927])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_167465,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_167463,c_28])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_166918,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_166920,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_168405,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_166918,c_166920])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_166928,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_167556,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_166918,c_166928])).

cnf(c_168417,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_168405,c_167556])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_653,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_682,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_653])).

cnf(c_654,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8517,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_8518,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8517])).

cnf(c_24658,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24659,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_24711,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24658,c_24659])).

cnf(c_24660,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_24702,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_24658,c_24660])).

cnf(c_24712,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24711,c_24702])).

cnf(c_175044,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_168417,c_39,c_25,c_682,c_8518,c_24712])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_166934,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_175056,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_175044,c_166934])).

cnf(c_58873,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_58537,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1)))
    | ~ iProver_ARSWP_238 ),
    inference(arg_filter_abstr,[status(unp)],[c_29])).

cnf(c_58851,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1))) = iProver_top
    | iProver_ARSWP_238 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58537])).

cnf(c_58533,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_234
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(arg_filter_abstr,[status(unp)],[c_18])).

cnf(c_58855,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
    | iProver_ARSWP_234 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58533])).

cnf(c_60402,plain,
    ( k1_relset_1(sK1,X0,sK3) = sK1
    | k1_xboole_0 = X0
    | v1_funct_2(sK3,sK1,X0) != iProver_top
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_234 != iProver_top ),
    inference(superposition,[status(thm)],[c_58851,c_58855])).

cnf(c_62132,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_234 != iProver_top ),
    inference(superposition,[status(thm)],[c_58873,c_60402])).

cnf(c_24691,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_62135,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_62132,c_30,c_29,c_25,c_24691])).

cnf(c_58525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_226
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_58863,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58525])).

cnf(c_59969,plain,
    ( k1_relset_1(sK1,X0,sK3) = k1_relat_1(sK3)
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(superposition,[status(thm)],[c_58851,c_58863])).

cnf(c_62140,plain,
    ( k1_relat_1(sK3) = sK1
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(superposition,[status(thm)],[c_62135,c_59969])).

cnf(c_62238,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_62140,c_39,c_25,c_682,c_8518,c_24712])).

cnf(c_58880,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_62271,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_62238,c_58880])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_54754,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_54755,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54754])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_54830,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_54831,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54830])).

cnf(c_62426,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_62271,c_38,c_40,c_54755,c_54831])).

cnf(c_62427,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_62426])).

cnf(c_216042,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_175056,c_38,c_40,c_54755,c_54831,c_62271])).

cnf(c_216043,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_216042])).

cnf(c_216052,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_167465,c_216043])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_166621,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ iProver_ARSWP_247
    | arAF1_k1_partfun1_0_1_2(X4,X5) = k5_relat_1(X3,X0) ),
    inference(arg_filter_abstr,[status(unp)],[c_21])).

cnf(c_166905,plain,
    ( arAF1_k1_partfun1_0_1_2(X0,X1) = k5_relat_1(X2,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166621])).

cnf(c_167777,plain,
    ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_166915,c_166905])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_168151,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_167777,c_35])).

cnf(c_168152,plain,
    ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(renaming,[status(thm)],[c_168151])).

cnf(c_168162,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_166918,c_168152])).

cnf(c_168222,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_168162,c_38])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_383,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_12,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_391,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_383,c_12])).

cnf(c_166623,plain,
    ( ~ m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ iProver_ARSWP_249
    | k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
    inference(arg_filter_abstr,[status(unp)],[c_391])).

cnf(c_166903,plain,
    ( k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | iProver_ARSWP_249 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166623])).

cnf(c_168228,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | iProver_ARSWP_249 != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_168222,c_166903])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_54625,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_54628,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_54630,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_54886,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_54628,c_54630])).

cnf(c_55124,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_54886,c_38])).

cnf(c_55125,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_55124])).

cnf(c_55136,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_54625,c_55125])).

cnf(c_54758,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,sK1,sK0,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_54849,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_54758])).

cnf(c_55177,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_55136,c_34,c_32,c_31,c_29,c_54849])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_54631,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_55182,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_55177,c_54631])).

cnf(c_172731,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
    | iProver_ARSWP_249 != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_168228,c_35,c_37,c_38,c_40,c_55182])).

cnf(c_172749,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | iProver_ARSWP_249 != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_172731,c_168222])).

cnf(c_54622,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_55180,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_55177,c_54622])).

cnf(c_172993,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_172749,c_35,c_37,c_38,c_40,c_55180,c_55182])).

cnf(c_216132,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_216052,c_172993])).

cnf(c_54783,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_54784,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54783])).

cnf(c_54876,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_54877,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54876])).

cnf(c_216189,plain,
    ( v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_216132,c_35,c_37,c_54784,c_54877])).

cnf(c_216190,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_216189])).

cnf(c_4,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_166932,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_216195,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_216190,c_166932])).

cnf(c_166916,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_166930,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_167866,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_166916,c_166930])).

cnf(c_39568,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_39577,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_39746,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_39568,c_39577])).

cnf(c_167972,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_167866,c_40,c_39746,c_54755,c_54831])).

cnf(c_167973,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_167972])).

cnf(c_175047,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_175044,c_167973])).

cnf(c_216197,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_216195,c_175047])).

cnf(c_168163,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_166915,c_168152])).

cnf(c_168571,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_168163,c_35])).

cnf(c_168577,plain,
    ( k5_relat_1(sK2,sK2) = k5_relat_1(sK2,sK3)
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_168222,c_168571])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_166929,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_168971,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK2)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_168577,c_166929])).

cnf(c_167462,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_166918,c_166927])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_395,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_396,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_480,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_396])).

cnf(c_166624,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | ~ iProver_ARSWP_250
    | k2_relset_1(X1,sK0,X0) = sK0
    | arAF1_k1_partfun1_0_1_2(sK0,X1) != arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
    inference(arg_filter_abstr,[status(unp)],[c_480])).

cnf(c_166902,plain,
    ( k2_relset_1(X0,sK0,X1) = sK0
    | arAF1_k1_partfun1_0_1_2(sK0,X0) != arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | v1_funct_2(X2,sK0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_166624])).

cnf(c_167278,plain,
    ( k2_relset_1(sK1,sK0,X0) = sK0
    | v1_funct_2(X1,sK0,sK1) != iProver_top
    | v1_funct_2(X0,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_166902])).

cnf(c_167372,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(X0,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(superposition,[status(thm)],[c_166918,c_167278])).

cnf(c_54757,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_54837,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_54757])).

cnf(c_136169,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_391,c_34,c_32,c_31,c_29,c_54837])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_347,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | X2 != X6
    | X2 != X5
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != X4
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != X4 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_348,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(k1_partfun1(X2,X1,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
    inference(unflattening,[status(thm)],[c_347])).

cnf(c_370,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_348,c_19])).

cnf(c_136260,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | k6_partfun1(X1) != k1_partfun1(X1,X0,X0,X1,X3,X2)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_136585,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_136169,c_136260])).

cnf(c_136266,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_136274,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_136514,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_136266,c_136274])).

cnf(c_136586,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_136585,c_136514])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_136732,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_136586,c_35,c_36,c_37,c_38,c_39,c_40])).

cnf(c_136736,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_136732,c_136514])).

cnf(c_167397,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_167372,c_136736])).

cnf(c_167468,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_167462,c_167397])).

cnf(c_168981,plain,
    ( k5_relat_1(sK2,sK2) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_168971,c_167465,c_167468])).

cnf(c_136263,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_136268,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_136767,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_136266,c_136268])).

cnf(c_137033,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_136767,c_38,c_54886])).

cnf(c_137034,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_137033])).

cnf(c_137043,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_136263,c_137034])).

cnf(c_137046,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_137043,c_136169])).

cnf(c_137187,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_137046,c_35,c_37,c_38,c_40,c_55180,c_55182])).

cnf(c_136276,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_137190,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_137187,c_136276])).

cnf(c_136515,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_136263,c_136274])).

cnf(c_136517,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_136515,c_28])).

cnf(c_137191,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_137190,c_136517,c_136732])).

cnf(c_137192,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_137191])).

cnf(c_137609,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_137192,c_35,c_37,c_38,c_39,c_40,c_25,c_682,c_8518,c_24712,c_54755,c_54784,c_54831,c_54877])).

cnf(c_169761,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_168981,c_137609])).

cnf(c_169762,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_169761])).

cnf(c_216199,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_216195,c_169762])).

cnf(c_216204,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_216197,c_216199])).

cnf(c_217033,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_216204,c_166929])).

cnf(c_168406,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_166915,c_166920])).

cnf(c_167557,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_166915,c_166928])).

cnf(c_168410,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_168406,c_167557])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_8515,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_654])).

cnf(c_8516,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8515])).

cnf(c_54632,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_54974,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_54625,c_54632])).

cnf(c_54635,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_54865,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_54625,c_54635])).

cnf(c_54978,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_54974,c_54865])).

cnf(c_174359,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_168410,c_36,c_24,c_682,c_8516,c_54978])).

cnf(c_217034,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_217033,c_167465,c_167468,c_174359])).

cnf(c_217035,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_217034])).

cnf(c_23,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_42,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_217035,c_54877,c_54831,c_54784,c_54755,c_23,c_42,c_40,c_38,c_37,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n013.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 09:41:09 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  % Running in FOF mode
% 46.90/6.45  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 46.90/6.45  
% 46.90/6.45  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 46.90/6.45  
% 46.90/6.45  ------  iProver source info
% 46.90/6.45  
% 46.90/6.45  git: date: 2020-06-30 10:37:57 +0100
% 46.90/6.45  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 46.90/6.45  git: non_committed_changes: false
% 46.90/6.45  git: last_make_outside_of_git: false
% 46.90/6.45  
% 46.90/6.45  ------ 
% 46.90/6.45  ------ Parsing...
% 46.90/6.45  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  ------ Proving...
% 46.90/6.45  ------ Problem Properties 
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  clauses                                 34
% 46.90/6.45  conjectures                             11
% 46.90/6.45  EPR                                     7
% 46.90/6.45  Horn                                    30
% 46.90/6.45  unary                                   14
% 46.90/6.45  binary                                  3
% 46.90/6.45  lits                                    105
% 46.90/6.45  lits eq                                 28
% 46.90/6.45  fd_pure                                 0
% 46.90/6.45  fd_pseudo                               0
% 46.90/6.45  fd_cond                                 3
% 46.90/6.45  fd_pseudo_cond                          1
% 46.90/6.45  AC symbols                              0
% 46.90/6.45  
% 46.90/6.45  ------ Input Options Time Limit: Unbounded
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 46.90/6.45  Current options:
% 46.90/6.45  ------ 
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 46.90/6.45  
% 46.90/6.45  ------ Proving...
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  % SZS status Theorem for theBenchmark.p
% 46.90/6.45  
% 46.90/6.45  % SZS output start CNFRefutation for theBenchmark.p
% 46.90/6.45  
% 46.90/6.45  fof(f16,conjecture,(
% 46.90/6.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f17,negated_conjecture,(
% 46.90/6.45    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 46.90/6.45    inference(negated_conjecture,[],[f16])).
% 46.90/6.45  
% 46.90/6.45  fof(f37,plain,(
% 46.90/6.45    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 46.90/6.45    inference(ennf_transformation,[],[f17])).
% 46.90/6.45  
% 46.90/6.45  fof(f38,plain,(
% 46.90/6.45    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 46.90/6.45    inference(flattening,[],[f37])).
% 46.90/6.45  
% 46.90/6.45  fof(f42,plain,(
% 46.90/6.45    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 46.90/6.45    introduced(choice_axiom,[])).
% 46.90/6.45  
% 46.90/6.45  fof(f41,plain,(
% 46.90/6.45    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 46.90/6.45    introduced(choice_axiom,[])).
% 46.90/6.45  
% 46.90/6.45  fof(f43,plain,(
% 46.90/6.45    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 46.90/6.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f38,f42,f41])).
% 46.90/6.45  
% 46.90/6.45  fof(f70,plain,(
% 46.90/6.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  fof(f8,axiom,(
% 46.90/6.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f26,plain,(
% 46.90/6.45    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 46.90/6.45    inference(ennf_transformation,[],[f8])).
% 46.90/6.45  
% 46.90/6.45  fof(f53,plain,(
% 46.90/6.45    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 46.90/6.45    inference(cnf_transformation,[],[f26])).
% 46.90/6.45  
% 46.90/6.45  fof(f74,plain,(
% 46.90/6.45    k2_relset_1(sK0,sK1,sK2) = sK1),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  fof(f73,plain,(
% 46.90/6.45    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  fof(f11,axiom,(
% 46.90/6.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f29,plain,(
% 46.90/6.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 46.90/6.45    inference(ennf_transformation,[],[f11])).
% 46.90/6.45  
% 46.90/6.45  fof(f30,plain,(
% 46.90/6.45    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 46.90/6.45    inference(flattening,[],[f29])).
% 46.90/6.45  
% 46.90/6.45  fof(f40,plain,(
% 46.90/6.45    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 46.90/6.45    inference(nnf_transformation,[],[f30])).
% 46.90/6.45  
% 46.90/6.45  fof(f57,plain,(
% 46.90/6.45    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 46.90/6.45    inference(cnf_transformation,[],[f40])).
% 46.90/6.45  
% 46.90/6.45  fof(f7,axiom,(
% 46.90/6.45    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f25,plain,(
% 46.90/6.45    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 46.90/6.45    inference(ennf_transformation,[],[f7])).
% 46.90/6.45  
% 46.90/6.45  fof(f52,plain,(
% 46.90/6.45    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 46.90/6.45    inference(cnf_transformation,[],[f25])).
% 46.90/6.45  
% 46.90/6.45  fof(f72,plain,(
% 46.90/6.45    v1_funct_2(sK3,sK1,sK0)),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  fof(f77,plain,(
% 46.90/6.45    k1_xboole_0 != sK0),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  fof(f3,axiom,(
% 46.90/6.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f19,plain,(
% 46.90/6.45    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 46.90/6.45    inference(ennf_transformation,[],[f3])).
% 46.90/6.45  
% 46.90/6.45  fof(f20,plain,(
% 46.90/6.45    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 46.90/6.45    inference(flattening,[],[f19])).
% 46.90/6.45  
% 46.90/6.45  fof(f47,plain,(
% 46.90/6.45    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 46.90/6.45    inference(cnf_transformation,[],[f20])).
% 46.90/6.45  
% 46.90/6.45  fof(f71,plain,(
% 46.90/6.45    v1_funct_1(sK3)),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  fof(f1,axiom,(
% 46.90/6.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f18,plain,(
% 46.90/6.45    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 46.90/6.45    inference(ennf_transformation,[],[f1])).
% 46.90/6.45  
% 46.90/6.45  fof(f44,plain,(
% 46.90/6.45    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 46.90/6.45    inference(cnf_transformation,[],[f18])).
% 46.90/6.45  
% 46.90/6.45  fof(f2,axiom,(
% 46.90/6.45    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f45,plain,(
% 46.90/6.45    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 46.90/6.45    inference(cnf_transformation,[],[f2])).
% 46.90/6.45  
% 46.90/6.45  fof(f13,axiom,(
% 46.90/6.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f33,plain,(
% 46.90/6.45    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 46.90/6.45    inference(ennf_transformation,[],[f13])).
% 46.90/6.45  
% 46.90/6.45  fof(f34,plain,(
% 46.90/6.45    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 46.90/6.45    inference(flattening,[],[f33])).
% 46.90/6.45  
% 46.90/6.45  fof(f65,plain,(
% 46.90/6.45    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 46.90/6.45    inference(cnf_transformation,[],[f34])).
% 46.90/6.45  
% 46.90/6.45  fof(f68,plain,(
% 46.90/6.45    v1_funct_1(sK2)),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  fof(f9,axiom,(
% 46.90/6.45    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f27,plain,(
% 46.90/6.45    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 46.90/6.45    inference(ennf_transformation,[],[f9])).
% 46.90/6.45  
% 46.90/6.45  fof(f28,plain,(
% 46.90/6.45    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 46.90/6.45    inference(flattening,[],[f27])).
% 46.90/6.45  
% 46.90/6.45  fof(f39,plain,(
% 46.90/6.45    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 46.90/6.45    inference(nnf_transformation,[],[f28])).
% 46.90/6.45  
% 46.90/6.45  fof(f54,plain,(
% 46.90/6.45    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 46.90/6.45    inference(cnf_transformation,[],[f39])).
% 46.90/6.45  
% 46.90/6.45  fof(f75,plain,(
% 46.90/6.45    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  fof(f10,axiom,(
% 46.90/6.45    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f56,plain,(
% 46.90/6.45    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 46.90/6.45    inference(cnf_transformation,[],[f10])).
% 46.90/6.45  
% 46.90/6.45  fof(f14,axiom,(
% 46.90/6.45    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f66,plain,(
% 46.90/6.45    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 46.90/6.45    inference(cnf_transformation,[],[f14])).
% 46.90/6.45  
% 46.90/6.45  fof(f84,plain,(
% 46.90/6.45    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 46.90/6.45    inference(definition_unfolding,[],[f56,f66])).
% 46.90/6.45  
% 46.90/6.45  fof(f12,axiom,(
% 46.90/6.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f31,plain,(
% 46.90/6.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 46.90/6.45    inference(ennf_transformation,[],[f12])).
% 46.90/6.45  
% 46.90/6.45  fof(f32,plain,(
% 46.90/6.45    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 46.90/6.45    inference(flattening,[],[f31])).
% 46.90/6.45  
% 46.90/6.45  fof(f64,plain,(
% 46.90/6.45    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 46.90/6.45    inference(cnf_transformation,[],[f32])).
% 46.90/6.45  
% 46.90/6.45  fof(f4,axiom,(
% 46.90/6.45    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f48,plain,(
% 46.90/6.45    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 46.90/6.45    inference(cnf_transformation,[],[f4])).
% 46.90/6.45  
% 46.90/6.45  fof(f80,plain,(
% 46.90/6.45    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 46.90/6.45    inference(definition_unfolding,[],[f48,f66])).
% 46.90/6.45  
% 46.90/6.45  fof(f5,axiom,(
% 46.90/6.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f21,plain,(
% 46.90/6.45    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 46.90/6.45    inference(ennf_transformation,[],[f5])).
% 46.90/6.45  
% 46.90/6.45  fof(f22,plain,(
% 46.90/6.45    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 46.90/6.45    inference(flattening,[],[f21])).
% 46.90/6.45  
% 46.90/6.45  fof(f49,plain,(
% 46.90/6.45    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 46.90/6.45    inference(cnf_transformation,[],[f22])).
% 46.90/6.45  
% 46.90/6.45  fof(f82,plain,(
% 46.90/6.45    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 46.90/6.45    inference(definition_unfolding,[],[f49,f66])).
% 46.90/6.45  
% 46.90/6.45  fof(f6,axiom,(
% 46.90/6.45    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f23,plain,(
% 46.90/6.45    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 46.90/6.45    inference(ennf_transformation,[],[f6])).
% 46.90/6.45  
% 46.90/6.45  fof(f24,plain,(
% 46.90/6.45    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 46.90/6.45    inference(flattening,[],[f23])).
% 46.90/6.45  
% 46.90/6.45  fof(f51,plain,(
% 46.90/6.45    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 46.90/6.45    inference(cnf_transformation,[],[f24])).
% 46.90/6.45  
% 46.90/6.45  fof(f83,plain,(
% 46.90/6.45    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 46.90/6.45    inference(definition_unfolding,[],[f51,f66])).
% 46.90/6.45  
% 46.90/6.45  fof(f15,axiom,(
% 46.90/6.45    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 46.90/6.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.90/6.45  
% 46.90/6.45  fof(f35,plain,(
% 46.90/6.45    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 46.90/6.45    inference(ennf_transformation,[],[f15])).
% 46.90/6.45  
% 46.90/6.45  fof(f36,plain,(
% 46.90/6.45    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 46.90/6.45    inference(flattening,[],[f35])).
% 46.90/6.45  
% 46.90/6.45  fof(f67,plain,(
% 46.90/6.45    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 46.90/6.45    inference(cnf_transformation,[],[f36])).
% 46.90/6.45  
% 46.90/6.45  fof(f55,plain,(
% 46.90/6.45    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 46.90/6.45    inference(cnf_transformation,[],[f39])).
% 46.90/6.45  
% 46.90/6.45  fof(f85,plain,(
% 46.90/6.45    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 46.90/6.45    inference(equality_resolution,[],[f55])).
% 46.90/6.45  
% 46.90/6.45  fof(f69,plain,(
% 46.90/6.45    v1_funct_2(sK2,sK0,sK1)),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  fof(f78,plain,(
% 46.90/6.45    k1_xboole_0 != sK1),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  fof(f79,plain,(
% 46.90/6.45    k2_funct_1(sK2) != sK3),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  fof(f76,plain,(
% 46.90/6.45    v2_funct_1(sK2)),
% 46.90/6.45    inference(cnf_transformation,[],[f43])).
% 46.90/6.45  
% 46.90/6.45  cnf(c_32,negated_conjecture,
% 46.90/6.45      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 46.90/6.45      inference(cnf_transformation,[],[f70]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166915,plain,
% 46.90/6.45      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_9,plain,
% 46.90/6.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 46.90/6.45      inference(cnf_transformation,[],[f53]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166927,plain,
% 46.90/6.45      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167463,plain,
% 46.90/6.45      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_166915,c_166927]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_28,negated_conjecture,
% 46.90/6.45      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 46.90/6.45      inference(cnf_transformation,[],[f74]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167465,plain,
% 46.90/6.45      ( k2_relat_1(sK2) = sK1 ),
% 46.90/6.45      inference(light_normalisation,[status(thm)],[c_167463,c_28]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_29,negated_conjecture,
% 46.90/6.45      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 46.90/6.45      inference(cnf_transformation,[],[f73]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166918,plain,
% 46.90/6.45      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_18,plain,
% 46.90/6.45      ( ~ v1_funct_2(X0,X1,X2)
% 46.90/6.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | k1_relset_1(X1,X2,X0) = X1
% 46.90/6.45      | k1_xboole_0 = X2 ),
% 46.90/6.45      inference(cnf_transformation,[],[f57]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166920,plain,
% 46.90/6.45      ( k1_relset_1(X0,X1,X2) = X0
% 46.90/6.45      | k1_xboole_0 = X1
% 46.90/6.45      | v1_funct_2(X2,X0,X1) != iProver_top
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168405,plain,
% 46.90/6.45      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 46.90/6.45      | sK0 = k1_xboole_0
% 46.90/6.45      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_166918,c_166920]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_8,plain,
% 46.90/6.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 46.90/6.45      inference(cnf_transformation,[],[f52]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166928,plain,
% 46.90/6.45      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167556,plain,
% 46.90/6.45      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_166918,c_166928]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168417,plain,
% 46.90/6.45      ( k1_relat_1(sK3) = sK1
% 46.90/6.45      | sK0 = k1_xboole_0
% 46.90/6.45      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 46.90/6.45      inference(demodulation,[status(thm)],[c_168405,c_167556]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_30,negated_conjecture,
% 46.90/6.45      ( v1_funct_2(sK3,sK1,sK0) ),
% 46.90/6.45      inference(cnf_transformation,[],[f72]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_39,plain,
% 46.90/6.45      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_25,negated_conjecture,
% 46.90/6.45      ( k1_xboole_0 != sK0 ),
% 46.90/6.45      inference(cnf_transformation,[],[f77]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_653,plain,( X0 = X0 ),theory(equality) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_682,plain,
% 46.90/6.45      ( k1_xboole_0 = k1_xboole_0 ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_653]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_654,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_8517,plain,
% 46.90/6.45      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_654]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_8518,plain,
% 46.90/6.45      ( sK0 != k1_xboole_0
% 46.90/6.45      | k1_xboole_0 = sK0
% 46.90/6.45      | k1_xboole_0 != k1_xboole_0 ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_8517]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_24658,plain,
% 46.90/6.45      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_24659,plain,
% 46.90/6.45      ( k1_relset_1(X0,X1,X2) = X0
% 46.90/6.45      | k1_xboole_0 = X1
% 46.90/6.45      | v1_funct_2(X2,X0,X1) != iProver_top
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_24711,plain,
% 46.90/6.45      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 46.90/6.45      | sK0 = k1_xboole_0
% 46.90/6.45      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_24658,c_24659]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_24660,plain,
% 46.90/6.45      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_24702,plain,
% 46.90/6.45      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_24658,c_24660]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_24712,plain,
% 46.90/6.45      ( k1_relat_1(sK3) = sK1
% 46.90/6.45      | sK0 = k1_xboole_0
% 46.90/6.45      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 46.90/6.45      inference(demodulation,[status(thm)],[c_24711,c_24702]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_175044,plain,
% 46.90/6.45      ( k1_relat_1(sK3) = sK1 ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_168417,c_39,c_25,c_682,c_8518,c_24712]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_2,plain,
% 46.90/6.45      ( ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(X1)
% 46.90/6.45      | v2_funct_1(X1)
% 46.90/6.45      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 46.90/6.45      | ~ v1_relat_1(X1)
% 46.90/6.45      | ~ v1_relat_1(X0)
% 46.90/6.45      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 46.90/6.45      inference(cnf_transformation,[],[f47]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166934,plain,
% 46.90/6.45      ( k1_relat_1(X0) != k2_relat_1(X1)
% 46.90/6.45      | v1_funct_1(X1) != iProver_top
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v2_funct_1(X0) = iProver_top
% 46.90/6.45      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 46.90/6.45      | v1_relat_1(X0) != iProver_top
% 46.90/6.45      | v1_relat_1(X1) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_175056,plain,
% 46.90/6.45      ( k2_relat_1(X0) != sK1
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) = iProver_top
% 46.90/6.45      | v1_relat_1(X0) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_175044,c_166934]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_58873,plain,
% 46.90/6.45      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_58537,negated_conjecture,
% 46.90/6.45      ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1)))
% 46.90/6.45      | ~ iProver_ARSWP_238 ),
% 46.90/6.45      inference(arg_filter_abstr,[status(unp)],[c_29]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_58851,plain,
% 46.90/6.45      ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1))) = iProver_top
% 46.90/6.45      | iProver_ARSWP_238 != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_58537]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_58533,plain,
% 46.90/6.45      ( ~ v1_funct_2(X0,X1,X2)
% 46.90/6.45      | ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
% 46.90/6.45      | ~ iProver_ARSWP_234
% 46.90/6.45      | k1_relset_1(X1,X2,X0) = X1
% 46.90/6.45      | k1_xboole_0 = X2 ),
% 46.90/6.45      inference(arg_filter_abstr,[status(unp)],[c_18]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_58855,plain,
% 46.90/6.45      ( k1_relset_1(X0,X1,X2) = X0
% 46.90/6.45      | k1_xboole_0 = X1
% 46.90/6.45      | v1_funct_2(X2,X0,X1) != iProver_top
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
% 46.90/6.45      | iProver_ARSWP_234 != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_58533]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_60402,plain,
% 46.90/6.45      ( k1_relset_1(sK1,X0,sK3) = sK1
% 46.90/6.45      | k1_xboole_0 = X0
% 46.90/6.45      | v1_funct_2(sK3,sK1,X0) != iProver_top
% 46.90/6.45      | iProver_ARSWP_238 != iProver_top
% 46.90/6.45      | iProver_ARSWP_234 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_58851,c_58855]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_62132,plain,
% 46.90/6.45      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 46.90/6.45      | sK0 = k1_xboole_0
% 46.90/6.45      | iProver_ARSWP_238 != iProver_top
% 46.90/6.45      | iProver_ARSWP_234 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_58873,c_60402]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_24691,plain,
% 46.90/6.45      ( ~ v1_funct_2(sK3,sK1,sK0)
% 46.90/6.45      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 46.90/6.45      | k1_relset_1(sK1,sK0,sK3) = sK1
% 46.90/6.45      | k1_xboole_0 = sK0 ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_18]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_62135,plain,
% 46.90/6.45      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_62132,c_30,c_29,c_25,c_24691]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_58525,plain,
% 46.90/6.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
% 46.90/6.45      | ~ iProver_ARSWP_226
% 46.90/6.45      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 46.90/6.45      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_58863,plain,
% 46.90/6.45      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
% 46.90/6.45      | iProver_ARSWP_226 != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_58525]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_59969,plain,
% 46.90/6.45      ( k1_relset_1(sK1,X0,sK3) = k1_relat_1(sK3)
% 46.90/6.45      | iProver_ARSWP_238 != iProver_top
% 46.90/6.45      | iProver_ARSWP_226 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_58851,c_58863]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_62140,plain,
% 46.90/6.45      ( k1_relat_1(sK3) = sK1
% 46.90/6.45      | iProver_ARSWP_238 != iProver_top
% 46.90/6.45      | iProver_ARSWP_226 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_62135,c_59969]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_62238,plain,
% 46.90/6.45      ( k1_relat_1(sK3) = sK1 ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_62140,c_39,c_25,c_682,c_8518,c_24712]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_58880,plain,
% 46.90/6.45      ( k1_relat_1(X0) != k2_relat_1(X1)
% 46.90/6.45      | v1_funct_1(X1) != iProver_top
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v2_funct_1(X0) = iProver_top
% 46.90/6.45      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 46.90/6.45      | v1_relat_1(X0) != iProver_top
% 46.90/6.45      | v1_relat_1(X1) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_62271,plain,
% 46.90/6.45      ( k2_relat_1(X0) != sK1
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) = iProver_top
% 46.90/6.45      | v1_relat_1(X0) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_62238,c_58880]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_31,negated_conjecture,
% 46.90/6.45      ( v1_funct_1(sK3) ),
% 46.90/6.45      inference(cnf_transformation,[],[f71]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_38,plain,
% 46.90/6.45      ( v1_funct_1(sK3) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_40,plain,
% 46.90/6.45      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_0,plain,
% 46.90/6.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 46.90/6.45      | ~ v1_relat_1(X1)
% 46.90/6.45      | v1_relat_1(X0) ),
% 46.90/6.45      inference(cnf_transformation,[],[f44]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54754,plain,
% 46.90/6.45      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 46.90/6.45      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 46.90/6.45      | v1_relat_1(sK3) ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_0]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54755,plain,
% 46.90/6.45      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 46.90/6.45      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_54754]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_1,plain,
% 46.90/6.45      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 46.90/6.45      inference(cnf_transformation,[],[f45]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54830,plain,
% 46.90/6.45      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_1]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54831,plain,
% 46.90/6.45      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_54830]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_62426,plain,
% 46.90/6.45      ( v1_relat_1(X0) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) = iProver_top
% 46.90/6.45      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 46.90/6.45      | k2_relat_1(X0) != sK1
% 46.90/6.45      | v1_funct_1(X0) != iProver_top ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_62271,c_38,c_40,c_54755,c_54831]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_62427,plain,
% 46.90/6.45      ( k2_relat_1(X0) != sK1
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) = iProver_top
% 46.90/6.45      | v1_relat_1(X0) != iProver_top ),
% 46.90/6.45      inference(renaming,[status(thm)],[c_62426]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_216042,plain,
% 46.90/6.45      ( v1_relat_1(X0) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) = iProver_top
% 46.90/6.45      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 46.90/6.45      | k2_relat_1(X0) != sK1
% 46.90/6.45      | v1_funct_1(X0) != iProver_top ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_175056,c_38,c_40,c_54755,c_54831,c_62271]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_216043,plain,
% 46.90/6.45      ( k2_relat_1(X0) != sK1
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) = iProver_top
% 46.90/6.45      | v1_relat_1(X0) != iProver_top ),
% 46.90/6.45      inference(renaming,[status(thm)],[c_216042]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_216052,plain,
% 46.90/6.45      ( v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) = iProver_top
% 46.90/6.45      | v1_relat_1(sK2) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_167465,c_216043]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_21,plain,
% 46.90/6.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(X3)
% 46.90/6.45      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 46.90/6.45      inference(cnf_transformation,[],[f65]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166621,plain,
% 46.90/6.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(X3)
% 46.90/6.45      | ~ iProver_ARSWP_247
% 46.90/6.45      | arAF1_k1_partfun1_0_1_2(X4,X5) = k5_relat_1(X3,X0) ),
% 46.90/6.45      inference(arg_filter_abstr,[status(unp)],[c_21]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166905,plain,
% 46.90/6.45      ( arAF1_k1_partfun1_0_1_2(X0,X1) = k5_relat_1(X2,X3)
% 46.90/6.45      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.90/6.45      | v1_funct_1(X2) != iProver_top
% 46.90/6.45      | v1_funct_1(X3) != iProver_top
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_166621]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167777,plain,
% 46.90/6.45      ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 46.90/6.45      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_166915,c_166905]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_34,negated_conjecture,
% 46.90/6.45      ( v1_funct_1(sK2) ),
% 46.90/6.45      inference(cnf_transformation,[],[f68]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_35,plain,
% 46.90/6.45      ( v1_funct_1(sK2) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168151,plain,
% 46.90/6.45      ( v1_funct_1(X0) != iProver_top
% 46.90/6.45      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 46.90/6.45      | k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_167777,c_35]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168152,plain,
% 46.90/6.45      ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 46.90/6.45      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(renaming,[status(thm)],[c_168151]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168162,plain,
% 46.90/6.45      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_166918,c_168152]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168222,plain,
% 46.90/6.45      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_168162,c_38]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_11,plain,
% 46.90/6.45      ( ~ r2_relset_1(X0,X1,X2,X3)
% 46.90/6.45      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 46.90/6.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 46.90/6.45      | X3 = X2 ),
% 46.90/6.45      inference(cnf_transformation,[],[f54]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_27,negated_conjecture,
% 46.90/6.45      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 46.90/6.45      inference(cnf_transformation,[],[f75]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_382,plain,
% 46.90/6.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | X3 = X0
% 46.90/6.45      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 46.90/6.45      | k6_partfun1(sK0) != X3
% 46.90/6.45      | sK0 != X2
% 46.90/6.45      | sK0 != X1 ),
% 46.90/6.45      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_383,plain,
% 46.90/6.45      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 46.90/6.45      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 46.90/6.45      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 46.90/6.45      inference(unflattening,[status(thm)],[c_382]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_12,plain,
% 46.90/6.45      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 46.90/6.45      inference(cnf_transformation,[],[f84]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_391,plain,
% 46.90/6.45      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 46.90/6.45      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 46.90/6.45      inference(forward_subsumption_resolution,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_383,c_12]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166623,plain,
% 46.90/6.45      ( ~ m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 46.90/6.45      | ~ iProver_ARSWP_249
% 46.90/6.45      | k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
% 46.90/6.45      inference(arg_filter_abstr,[status(unp)],[c_391]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166903,plain,
% 46.90/6.45      ( k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 46.90/6.45      | m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 46.90/6.45      | iProver_ARSWP_249 != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_166623]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168228,plain,
% 46.90/6.45      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
% 46.90/6.45      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 46.90/6.45      | iProver_ARSWP_249 != iProver_top
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_168222,c_166903]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_37,plain,
% 46.90/6.45      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54625,plain,
% 46.90/6.45      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54628,plain,
% 46.90/6.45      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54630,plain,
% 46.90/6.45      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 46.90/6.45      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 46.90/6.45      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.90/6.45      | v1_funct_1(X4) != iProver_top
% 46.90/6.45      | v1_funct_1(X5) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54886,plain,
% 46.90/6.45      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.90/6.45      | v1_funct_1(X2) != iProver_top
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_54628,c_54630]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_55124,plain,
% 46.90/6.45      ( v1_funct_1(X2) != iProver_top
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.90/6.45      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_54886,c_38]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_55125,plain,
% 46.90/6.45      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.90/6.45      | v1_funct_1(X2) != iProver_top ),
% 46.90/6.45      inference(renaming,[status(thm)],[c_55124]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_55136,plain,
% 46.90/6.45      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_54625,c_55125]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54758,plain,
% 46.90/6.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(sK3)
% 46.90/6.45      | k1_partfun1(X1,X2,sK1,sK0,X0,sK3) = k5_relat_1(X0,sK3) ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_21]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54849,plain,
% 46.90/6.45      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 46.90/6.45      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 46.90/6.45      | ~ v1_funct_1(sK3)
% 46.90/6.45      | ~ v1_funct_1(sK2)
% 46.90/6.45      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_54758]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_55177,plain,
% 46.90/6.45      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_55136,c_34,c_32,c_31,c_29,c_54849]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_19,plain,
% 46.90/6.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 46.90/6.45      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(X3) ),
% 46.90/6.45      inference(cnf_transformation,[],[f64]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54631,plain,
% 46.90/6.45      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 46.90/6.45      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 46.90/6.45      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 46.90/6.45      | v1_funct_1(X3) != iProver_top
% 46.90/6.45      | v1_funct_1(X0) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_55182,plain,
% 46.90/6.45      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 46.90/6.45      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 46.90/6.45      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_55177,c_54631]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_172731,plain,
% 46.90/6.45      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
% 46.90/6.45      | iProver_ARSWP_249 != iProver_top
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_168228,c_35,c_37,c_38,c_40,c_55182]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_172749,plain,
% 46.90/6.45      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 46.90/6.45      | iProver_ARSWP_249 != iProver_top
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_172731,c_168222]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54622,plain,
% 46.90/6.45      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 46.90/6.45      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_55180,plain,
% 46.90/6.45      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 46.90/6.45      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 46.90/6.45      inference(demodulation,[status(thm)],[c_55177,c_54622]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_172993,plain,
% 46.90/6.45      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_172749,c_35,c_37,c_38,c_40,c_55180,c_55182]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_216132,plain,
% 46.90/6.45      ( v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) = iProver_top
% 46.90/6.45      | v1_relat_1(sK2) != iProver_top ),
% 46.90/6.45      inference(light_normalisation,[status(thm)],[c_216052,c_172993]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54783,plain,
% 46.90/6.45      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 46.90/6.45      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 46.90/6.45      | v1_relat_1(sK2) ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_0]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54784,plain,
% 46.90/6.45      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 46.90/6.45      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 46.90/6.45      | v1_relat_1(sK2) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_54783]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54876,plain,
% 46.90/6.45      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_1]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54877,plain,
% 46.90/6.45      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_54876]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_216189,plain,
% 46.90/6.45      ( v2_funct_1(sK3) = iProver_top
% 46.90/6.45      | v2_funct_1(k6_partfun1(sK0)) != iProver_top ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_216132,c_35,c_37,c_54784,c_54877]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_216190,plain,
% 46.90/6.45      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) = iProver_top ),
% 46.90/6.45      inference(renaming,[status(thm)],[c_216189]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_4,plain,
% 46.90/6.45      ( v2_funct_1(k6_partfun1(X0)) ),
% 46.90/6.45      inference(cnf_transformation,[],[f80]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166932,plain,
% 46.90/6.45      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_216195,plain,
% 46.90/6.45      ( v2_funct_1(sK3) = iProver_top ),
% 46.90/6.45      inference(forward_subsumption_resolution,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_216190,c_166932]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166916,plain,
% 46.90/6.45      ( v1_funct_1(sK3) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_6,plain,
% 46.90/6.45      ( ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v2_funct_1(X0)
% 46.90/6.45      | ~ v1_relat_1(X0)
% 46.90/6.45      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 46.90/6.45      inference(cnf_transformation,[],[f82]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166930,plain,
% 46.90/6.45      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v2_funct_1(X0) != iProver_top
% 46.90/6.45      | v1_relat_1(X0) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167866,plain,
% 46.90/6.45      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 46.90/6.45      | v2_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_166916,c_166930]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_39568,plain,
% 46.90/6.45      ( v1_funct_1(sK3) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_39577,plain,
% 46.90/6.45      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v2_funct_1(X0) != iProver_top
% 46.90/6.45      | v1_relat_1(X0) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_39746,plain,
% 46.90/6.45      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 46.90/6.45      | v2_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_39568,c_39577]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167972,plain,
% 46.90/6.45      ( v2_funct_1(sK3) != iProver_top
% 46.90/6.45      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_167866,c_40,c_39746,c_54755,c_54831]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167973,plain,
% 46.90/6.45      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 46.90/6.45      | v2_funct_1(sK3) != iProver_top ),
% 46.90/6.45      inference(renaming,[status(thm)],[c_167972]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_175047,plain,
% 46.90/6.45      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 46.90/6.45      | v2_funct_1(sK3) != iProver_top ),
% 46.90/6.45      inference(demodulation,[status(thm)],[c_175044,c_167973]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_216197,plain,
% 46.90/6.45      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_216195,c_175047]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168163,plain,
% 46.90/6.45      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_166915,c_168152]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168571,plain,
% 46.90/6.45      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_168163,c_35]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168577,plain,
% 46.90/6.45      ( k5_relat_1(sK2,sK2) = k5_relat_1(sK2,sK3)
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_168222,c_168571]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_7,plain,
% 46.90/6.45      ( ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(X1)
% 46.90/6.45      | ~ v2_funct_1(X1)
% 46.90/6.45      | ~ v1_relat_1(X1)
% 46.90/6.45      | ~ v1_relat_1(X0)
% 46.90/6.45      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 46.90/6.45      | k2_funct_1(X1) = X0
% 46.90/6.45      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 46.90/6.45      inference(cnf_transformation,[],[f83]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166929,plain,
% 46.90/6.45      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 46.90/6.45      | k2_funct_1(X1) = X0
% 46.90/6.45      | k1_relat_1(X1) != k2_relat_1(X0)
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v1_funct_1(X1) != iProver_top
% 46.90/6.45      | v2_funct_1(X1) != iProver_top
% 46.90/6.45      | v1_relat_1(X1) != iProver_top
% 46.90/6.45      | v1_relat_1(X0) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168971,plain,
% 46.90/6.45      ( k2_funct_1(sK3) = sK2
% 46.90/6.45      | k6_partfun1(k2_relat_1(sK3)) != k5_relat_1(sK2,sK2)
% 46.90/6.45      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK2) != iProver_top
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_168577,c_166929]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167462,plain,
% 46.90/6.45      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_166918,c_166927]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_22,plain,
% 46.90/6.45      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 46.90/6.45      | ~ v1_funct_2(X3,X1,X0)
% 46.90/6.45      | ~ v1_funct_2(X2,X0,X1)
% 46.90/6.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 46.90/6.45      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 46.90/6.45      | ~ v1_funct_1(X2)
% 46.90/6.45      | ~ v1_funct_1(X3)
% 46.90/6.45      | k2_relset_1(X1,X0,X3) = X0 ),
% 46.90/6.45      inference(cnf_transformation,[],[f67]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_395,plain,
% 46.90/6.45      ( ~ v1_funct_2(X0,X1,X2)
% 46.90/6.45      | ~ v1_funct_2(X3,X2,X1)
% 46.90/6.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(X3)
% 46.90/6.45      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 46.90/6.45      | k2_relset_1(X1,X2,X0) = X2
% 46.90/6.45      | k6_partfun1(X2) != k6_partfun1(sK0)
% 46.90/6.45      | sK0 != X2 ),
% 46.90/6.45      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_396,plain,
% 46.90/6.45      ( ~ v1_funct_2(X0,X1,sK0)
% 46.90/6.45      | ~ v1_funct_2(X2,sK0,X1)
% 46.90/6.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 46.90/6.45      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(X2)
% 46.90/6.45      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 46.90/6.45      | k2_relset_1(X1,sK0,X0) = sK0
% 46.90/6.45      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 46.90/6.45      inference(unflattening,[status(thm)],[c_395]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_480,plain,
% 46.90/6.45      ( ~ v1_funct_2(X0,X1,sK0)
% 46.90/6.45      | ~ v1_funct_2(X2,sK0,X1)
% 46.90/6.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 46.90/6.45      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(X2)
% 46.90/6.45      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 46.90/6.45      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 46.90/6.45      inference(equality_resolution_simp,[status(thm)],[c_396]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166624,plain,
% 46.90/6.45      ( ~ v1_funct_2(X0,X1,sK0)
% 46.90/6.45      | ~ v1_funct_2(X2,sK0,X1)
% 46.90/6.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 46.90/6.45      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(X2)
% 46.90/6.45      | ~ iProver_ARSWP_250
% 46.90/6.45      | k2_relset_1(X1,sK0,X0) = sK0
% 46.90/6.45      | arAF1_k1_partfun1_0_1_2(sK0,X1) != arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
% 46.90/6.45      inference(arg_filter_abstr,[status(unp)],[c_480]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_166902,plain,
% 46.90/6.45      ( k2_relset_1(X0,sK0,X1) = sK0
% 46.90/6.45      | arAF1_k1_partfun1_0_1_2(sK0,X0) != arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 46.90/6.45      | v1_funct_2(X1,X0,sK0) != iProver_top
% 46.90/6.45      | v1_funct_2(X2,sK0,X0) != iProver_top
% 46.90/6.45      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 46.90/6.45      | v1_funct_1(X2) != iProver_top
% 46.90/6.45      | v1_funct_1(X1) != iProver_top
% 46.90/6.45      | iProver_ARSWP_250 != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_166624]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167278,plain,
% 46.90/6.45      ( k2_relset_1(sK1,sK0,X0) = sK0
% 46.90/6.45      | v1_funct_2(X1,sK0,sK1) != iProver_top
% 46.90/6.45      | v1_funct_2(X0,sK1,sK0) != iProver_top
% 46.90/6.45      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 46.90/6.45      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v1_funct_1(X1) != iProver_top
% 46.90/6.45      | iProver_ARSWP_250 != iProver_top ),
% 46.90/6.45      inference(equality_resolution,[status(thm)],[c_166902]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167372,plain,
% 46.90/6.45      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 46.90/6.45      | v1_funct_2(X0,sK0,sK1) != iProver_top
% 46.90/6.45      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 46.90/6.45      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | iProver_ARSWP_250 != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_166918,c_167278]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54757,plain,
% 46.90/6.45      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 46.90/6.45      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(sK3) ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_19]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54837,plain,
% 46.90/6.45      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 46.90/6.45      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 46.90/6.45      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 46.90/6.45      | ~ v1_funct_1(sK3)
% 46.90/6.45      | ~ v1_funct_1(sK2) ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_54757]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136169,plain,
% 46.90/6.45      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_391,c_34,c_32,c_31,c_29,c_54837]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_10,plain,
% 46.90/6.45      ( r2_relset_1(X0,X1,X2,X2)
% 46.90/6.45      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 46.90/6.45      inference(cnf_transformation,[],[f85]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_347,plain,
% 46.90/6.45      ( ~ v1_funct_2(X0,X1,X2)
% 46.90/6.45      | ~ v1_funct_2(X3,X2,X1)
% 46.90/6.45      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
% 46.90/6.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 46.90/6.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | ~ v1_funct_1(X3)
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | X2 != X6
% 46.90/6.45      | X2 != X5
% 46.90/6.45      | k1_partfun1(X2,X1,X1,X2,X3,X0) != X4
% 46.90/6.45      | k2_relset_1(X1,X2,X0) = X2
% 46.90/6.45      | k6_partfun1(X2) != X4 ),
% 46.90/6.45      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_348,plain,
% 46.90/6.45      ( ~ v1_funct_2(X0,X1,X2)
% 46.90/6.45      | ~ v1_funct_2(X3,X2,X1)
% 46.90/6.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 46.90/6.45      | ~ m1_subset_1(k1_partfun1(X2,X1,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(X3)
% 46.90/6.45      | k2_relset_1(X1,X2,X0) = X2
% 46.90/6.45      | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
% 46.90/6.45      inference(unflattening,[status(thm)],[c_347]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_370,plain,
% 46.90/6.45      ( ~ v1_funct_2(X0,X1,X2)
% 46.90/6.45      | ~ v1_funct_2(X3,X2,X1)
% 46.90/6.45      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.90/6.45      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 46.90/6.45      | ~ v1_funct_1(X0)
% 46.90/6.45      | ~ v1_funct_1(X3)
% 46.90/6.45      | k2_relset_1(X1,X2,X0) = X2
% 46.90/6.45      | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
% 46.90/6.45      inference(forward_subsumption_resolution,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_348,c_19]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136260,plain,
% 46.90/6.45      ( k2_relset_1(X0,X1,X2) = X1
% 46.90/6.45      | k6_partfun1(X1) != k1_partfun1(X1,X0,X0,X1,X3,X2)
% 46.90/6.45      | v1_funct_2(X2,X0,X1) != iProver_top
% 46.90/6.45      | v1_funct_2(X3,X1,X0) != iProver_top
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.90/6.45      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 46.90/6.45      | v1_funct_1(X3) != iProver_top
% 46.90/6.45      | v1_funct_1(X2) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136585,plain,
% 46.90/6.45      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 46.90/6.45      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 46.90/6.45      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 46.90/6.45      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 46.90/6.45      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_136169,c_136260]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136266,plain,
% 46.90/6.45      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136274,plain,
% 46.90/6.45      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136514,plain,
% 46.90/6.45      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_136266,c_136274]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136586,plain,
% 46.90/6.45      ( k2_relat_1(sK3) = sK0
% 46.90/6.45      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 46.90/6.45      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 46.90/6.45      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 46.90/6.45      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top ),
% 46.90/6.45      inference(demodulation,[status(thm)],[c_136585,c_136514]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_33,negated_conjecture,
% 46.90/6.45      ( v1_funct_2(sK2,sK0,sK1) ),
% 46.90/6.45      inference(cnf_transformation,[],[f69]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_36,plain,
% 46.90/6.45      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136732,plain,
% 46.90/6.45      ( k2_relat_1(sK3) = sK0 ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_136586,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136736,plain,
% 46.90/6.45      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 46.90/6.45      inference(demodulation,[status(thm)],[c_136732,c_136514]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167397,plain,
% 46.90/6.45      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_167372,c_136736]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167468,plain,
% 46.90/6.45      ( k2_relat_1(sK3) = sK0 ),
% 46.90/6.45      inference(light_normalisation,[status(thm)],[c_167462,c_167397]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168981,plain,
% 46.90/6.45      ( k5_relat_1(sK2,sK2) != k6_partfun1(sK0)
% 46.90/6.45      | k2_funct_1(sK3) = sK2
% 46.90/6.45      | k1_relat_1(sK3) != sK1
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK2) != iProver_top
% 46.90/6.45      | iProver_ARSWP_247 != iProver_top ),
% 46.90/6.45      inference(light_normalisation,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_168971,c_167465,c_167468]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136263,plain,
% 46.90/6.45      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136268,plain,
% 46.90/6.45      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 46.90/6.45      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 46.90/6.45      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.90/6.45      | v1_funct_1(X4) != iProver_top
% 46.90/6.45      | v1_funct_1(X5) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136767,plain,
% 46.90/6.45      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.90/6.45      | v1_funct_1(X2) != iProver_top
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_136266,c_136268]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_137033,plain,
% 46.90/6.45      ( v1_funct_1(X2) != iProver_top
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.90/6.45      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_136767,c_38,c_54886]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_137034,plain,
% 46.90/6.45      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.90/6.45      | v1_funct_1(X2) != iProver_top ),
% 46.90/6.45      inference(renaming,[status(thm)],[c_137033]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_137043,plain,
% 46.90/6.45      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_136263,c_137034]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_137046,plain,
% 46.90/6.45      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top ),
% 46.90/6.45      inference(light_normalisation,[status(thm)],[c_137043,c_136169]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_137187,plain,
% 46.90/6.45      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_137046,c_35,c_37,c_38,c_40,c_55180,c_55182]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136276,plain,
% 46.90/6.45      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 46.90/6.45      | k2_funct_1(X1) = X0
% 46.90/6.45      | k1_relat_1(X1) != k2_relat_1(X0)
% 46.90/6.45      | v1_funct_1(X0) != iProver_top
% 46.90/6.45      | v1_funct_1(X1) != iProver_top
% 46.90/6.45      | v2_funct_1(X1) != iProver_top
% 46.90/6.45      | v1_relat_1(X1) != iProver_top
% 46.90/6.45      | v1_relat_1(X0) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_137190,plain,
% 46.90/6.45      ( k2_funct_1(sK3) = sK2
% 46.90/6.45      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 46.90/6.45      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK2) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_137187,c_136276]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136515,plain,
% 46.90/6.45      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_136263,c_136274]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_136517,plain,
% 46.90/6.45      ( k2_relat_1(sK2) = sK1 ),
% 46.90/6.45      inference(light_normalisation,[status(thm)],[c_136515,c_28]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_137191,plain,
% 46.90/6.45      ( k2_funct_1(sK3) = sK2
% 46.90/6.45      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 46.90/6.45      | k1_relat_1(sK3) != sK1
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK2) != iProver_top ),
% 46.90/6.45      inference(light_normalisation,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_137190,c_136517,c_136732]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_137192,plain,
% 46.90/6.45      ( k2_funct_1(sK3) = sK2
% 46.90/6.45      | k1_relat_1(sK3) != sK1
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | v2_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK2) != iProver_top ),
% 46.90/6.45      inference(equality_resolution_simp,[status(thm)],[c_137191]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_137609,plain,
% 46.90/6.45      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_137192,c_35,c_37,c_38,c_39,c_40,c_25,c_682,c_8518,
% 46.90/6.45                 c_24712,c_54755,c_54784,c_54831,c_54877]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_169761,plain,
% 46.90/6.45      ( v2_funct_1(sK3) != iProver_top | k2_funct_1(sK3) = sK2 ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_168981,c_137609]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_169762,plain,
% 46.90/6.45      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 46.90/6.45      inference(renaming,[status(thm)],[c_169761]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_216199,plain,
% 46.90/6.45      ( k2_funct_1(sK3) = sK2 ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_216195,c_169762]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_216204,plain,
% 46.90/6.45      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 46.90/6.45      inference(light_normalisation,[status(thm)],[c_216197,c_216199]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_217033,plain,
% 46.90/6.45      ( k2_funct_1(sK2) = sK3
% 46.90/6.45      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 46.90/6.45      | k1_relat_1(sK2) != k2_relat_1(sK3)
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | v2_funct_1(sK2) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK2) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_216204,c_166929]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168406,plain,
% 46.90/6.45      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 46.90/6.45      | sK1 = k1_xboole_0
% 46.90/6.45      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_166915,c_166920]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_167557,plain,
% 46.90/6.45      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_166915,c_166928]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_168410,plain,
% 46.90/6.45      ( k1_relat_1(sK2) = sK0
% 46.90/6.45      | sK1 = k1_xboole_0
% 46.90/6.45      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 46.90/6.45      inference(demodulation,[status(thm)],[c_168406,c_167557]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_24,negated_conjecture,
% 46.90/6.45      ( k1_xboole_0 != sK1 ),
% 46.90/6.45      inference(cnf_transformation,[],[f78]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_8515,plain,
% 46.90/6.45      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_654]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_8516,plain,
% 46.90/6.45      ( sK1 != k1_xboole_0
% 46.90/6.45      | k1_xboole_0 = sK1
% 46.90/6.45      | k1_xboole_0 != k1_xboole_0 ),
% 46.90/6.45      inference(instantiation,[status(thm)],[c_8515]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54632,plain,
% 46.90/6.45      ( k1_relset_1(X0,X1,X2) = X0
% 46.90/6.45      | k1_xboole_0 = X1
% 46.90/6.45      | v1_funct_2(X2,X0,X1) != iProver_top
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54974,plain,
% 46.90/6.45      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 46.90/6.45      | sK1 = k1_xboole_0
% 46.90/6.45      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_54625,c_54632]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54635,plain,
% 46.90/6.45      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 46.90/6.45      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54865,plain,
% 46.90/6.45      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 46.90/6.45      inference(superposition,[status(thm)],[c_54625,c_54635]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_54978,plain,
% 46.90/6.45      ( k1_relat_1(sK2) = sK0
% 46.90/6.45      | sK1 = k1_xboole_0
% 46.90/6.45      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 46.90/6.45      inference(demodulation,[status(thm)],[c_54974,c_54865]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_174359,plain,
% 46.90/6.45      ( k1_relat_1(sK2) = sK0 ),
% 46.90/6.45      inference(global_propositional_subsumption,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_168410,c_36,c_24,c_682,c_8516,c_54978]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_217034,plain,
% 46.90/6.45      ( k2_funct_1(sK2) = sK3
% 46.90/6.45      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 46.90/6.45      | sK0 != sK0
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | v2_funct_1(sK2) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK2) != iProver_top ),
% 46.90/6.45      inference(light_normalisation,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_217033,c_167465,c_167468,c_174359]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_217035,plain,
% 46.90/6.45      ( k2_funct_1(sK2) = sK3
% 46.90/6.45      | v1_funct_1(sK3) != iProver_top
% 46.90/6.45      | v1_funct_1(sK2) != iProver_top
% 46.90/6.45      | v2_funct_1(sK2) != iProver_top
% 46.90/6.45      | v1_relat_1(sK3) != iProver_top
% 46.90/6.45      | v1_relat_1(sK2) != iProver_top ),
% 46.90/6.45      inference(equality_resolution_simp,[status(thm)],[c_217034]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_23,negated_conjecture,
% 46.90/6.45      ( k2_funct_1(sK2) != sK3 ),
% 46.90/6.45      inference(cnf_transformation,[],[f79]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_26,negated_conjecture,
% 46.90/6.45      ( v2_funct_1(sK2) ),
% 46.90/6.45      inference(cnf_transformation,[],[f76]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(c_42,plain,
% 46.90/6.45      ( v2_funct_1(sK2) = iProver_top ),
% 46.90/6.45      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 46.90/6.45  
% 46.90/6.45  cnf(contradiction,plain,
% 46.90/6.45      ( $false ),
% 46.90/6.45      inference(minisat,
% 46.90/6.45                [status(thm)],
% 46.90/6.45                [c_217035,c_54877,c_54831,c_54784,c_54755,c_23,c_42,c_40,
% 46.90/6.45                 c_38,c_37,c_35]) ).
% 46.90/6.45  
% 46.90/6.45  
% 46.90/6.45  % SZS output end CNFRefutation for theBenchmark.p
% 46.90/6.45  
% 46.90/6.45  ------                               Statistics
% 46.90/6.45  
% 46.90/6.45  ------ Selected
% 46.90/6.45  
% 46.90/6.45  total_time:                             5.981
% 46.90/6.45  
%------------------------------------------------------------------------------
