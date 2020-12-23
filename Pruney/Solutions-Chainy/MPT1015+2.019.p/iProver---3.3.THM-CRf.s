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
% DateTime   : Thu Dec  3 12:06:50 EST 2020

% Result     : Theorem 51.53s
% Output     : CNFRefutation 51.53s
% Verified   : 
% Statistics : Number of formulae       :  379 (13664 expanded)
%              Number of clauses        :  261 (4175 expanded)
%              Number of leaves         :   35 (3465 expanded)
%              Depth                    :   25
%              Number of atoms          : 1253 (87002 expanded)
%              Number of equality atoms :  694 (8328 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f28])).

fof(f67,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f68,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f67])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k6_partfun1(X0))
        & v2_funct_1(X1)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK2,X1),X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & v2_funct_1(sK1)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f68,f72,f71])).

fof(f119,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f73])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f63])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f117,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

fof(f118,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f59])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f25,axiom,(
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

fof(f61,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f62,plain,(
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
    inference(flattening,[],[f61])).

fof(f109,plain,(
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
    inference(cnf_transformation,[],[f62])).

fof(f114,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f73])).

fof(f115,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f116,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f73])).

fof(f121,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f73])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f87,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f24,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f108,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f127,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f87,f108])).

fof(f88,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f126,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f88,f108])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f54])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f120,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f73])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f57])).

fof(f106,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f9,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f124,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f84,f108])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k2_relat_1(X0) = k1_xboole_0
          | k1_relat_1(X0) = k1_xboole_0 )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k2_relat_1(X0) != k1_xboole_0
        & k1_relat_1(X0) != k1_xboole_0 )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f65])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f80,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f42,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f89,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f48,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f95,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k2_relat_1(X0) != k1_xboole_0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f93,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f93,f108])).

fof(f122,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f73])).

fof(f90,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f94,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f85,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f123,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f85,f108])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f129,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f102])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1641,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_24,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_7,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_24,c_7])).

cnf(c_1635,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_2984,plain,
    ( k7_relat_1(sK2,sK0) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1635])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_158,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_160,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_158])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1672,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3051,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1672])).

cnf(c_3266,plain,
    ( k7_relat_1(sK2,sK0) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2984,c_160,c_3051])).

cnf(c_3386,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3051,c_160])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1670,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3390,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_3386,c_1670])).

cnf(c_4509,plain,
    ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3266,c_3390])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1651,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3109,plain,
    ( k7_relset_1(sK0,sK0,sK2,sK0) = k2_relset_1(sK0,sK0,sK2) ),
    inference(superposition,[status(thm)],[c_1641,c_1651])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1653,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3056,plain,
    ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_1641,c_1653])).

cnf(c_3112,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k9_relat_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_3109,c_3056])).

cnf(c_4518,plain,
    ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4509,c_3112])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1645,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_15950,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK0)
    | k2_relat_1(sK2) != sK0
    | sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4518,c_1645])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1648,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_7106,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1648])).

cnf(c_51,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_7456,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7106,c_51])).

cnf(c_7457,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7456])).

cnf(c_7462,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_7457])).

cnf(c_7605,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7462,c_51])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1646,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7608,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK2)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7605,c_1646])).

cnf(c_47,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_48,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_46,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_49,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_50,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_52,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_40,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_55,plain,
    ( v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_14,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_129,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_131,plain,
    ( v1_relat_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_129])).

cnf(c_13,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_132,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_134,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_132])).

cnf(c_28,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_41,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_568,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X0
    | sK1 != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_41])).

cnf(c_569,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_568])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1725,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_967,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1723,plain,
    ( k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK2 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1798,plain,
    ( k6_partfun1(sK0) != k1_xboole_0
    | sK2 = k6_partfun1(sK0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1723])).

cnf(c_1959,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_1770,plain,
    ( X0 != X1
    | X0 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X1 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1850,plain,
    ( X0 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | X0 != k5_relat_1(sK2,sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k5_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1770])).

cnf(c_2105,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k5_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_11,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f124])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1666,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2534,plain,
    ( k6_partfun1(X0) = k1_xboole_0
    | k1_xboole_0 != X0
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11,c_1666])).

cnf(c_2536,plain,
    ( k6_partfun1(sK0) = k1_xboole_0
    | k1_xboole_0 != sK0
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2534])).

cnf(c_1853,plain,
    ( X0 != X1
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X1
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = X0 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1985,plain,
    ( X0 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1853])).

cnf(c_2662,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = sK1
    | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1985])).

cnf(c_979,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2269,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_3433,plain,
    ( ~ v2_funct_1(k6_partfun1(X0))
    | v2_funct_1(sK2)
    | sK2 != k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_2269])).

cnf(c_3434,plain,
    ( sK2 != k6_partfun1(X0)
    | v2_funct_1(k6_partfun1(X0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3433])).

cnf(c_3436,plain,
    ( sK2 != k6_partfun1(sK0)
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3434])).

cnf(c_2279,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK2,X3,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k1_partfun1(X3,X1,X1,X2,sK2,X0))
    | v2_funct_1(sK2)
    | k1_xboole_0 = X2 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3724,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ v1_funct_2(sK2,X2,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(k1_partfun1(X2,X0,X0,X1,sK2,sK1))
    | v2_funct_1(sK2)
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_2279])).

cnf(c_3725,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(sK1,X1,X0) != iProver_top
    | v1_funct_2(sK2,X2,X1) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k1_partfun1(X2,X1,X1,X0,sK2,sK1)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3724])).

cnf(c_3727,plain,
    ( k1_xboole_0 = sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3725])).

cnf(c_571,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_569,c_45])).

cnf(c_1632,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_571])).

cnf(c_2102,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1632,c_47,c_45,c_44,c_42,c_569,c_1725])).

cnf(c_6966,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v2_funct_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2102,c_1646])).

cnf(c_5115,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(sK1)
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_979])).

cnf(c_9871,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1))
    | ~ v2_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_5115])).

cnf(c_9872,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK1
    | v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) = iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9871])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1643,plain,
    ( k1_relset_1(X0,X0,X1) = X0
    | v1_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_3806,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1643])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1654,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2613,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1641,c_1654])).

cnf(c_3809,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3806,c_2613])).

cnf(c_11190,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3809,c_51,c_52])).

cnf(c_11198,plain,
    ( sK2 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_11190,c_1666])).

cnf(c_15627,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7608,c_47,c_48,c_49,c_45,c_50,c_44,c_51,c_52,c_42,c_53,c_55,c_131,c_134,c_160,c_569,c_1725,c_1798,c_1959,c_2105,c_2536,c_2662,c_3051,c_3436,c_3727,c_6966,c_9872,c_11198])).

cnf(c_15629,plain,
    ( v2_funct_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15627])).

cnf(c_15952,plain,
    ( ~ v1_funct_2(sK2,sK0,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK0)
    | k2_relat_1(sK2) != sK0
    | sK0 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_15950])).

cnf(c_23,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_537,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_23,c_2])).

cnf(c_1634,plain,
    ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_2471,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_1634])).

cnf(c_1638,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_3807,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1643])).

cnf(c_2614,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1638,c_1654])).

cnf(c_3808,plain,
    ( k1_relat_1(sK1) = sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3807,c_2614])).

cnf(c_8067,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3808,c_48,c_49])).

cnf(c_18,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1659,plain,
    ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_8074,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8067,c_1659])).

cnf(c_3052,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1672])).

cnf(c_28391,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8074,c_48,c_55,c_160,c_3052])).

cnf(c_28392,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_28391])).

cnf(c_28397,plain,
    ( k10_relat_1(sK1,k9_relat_1(sK1,k2_relat_1(sK2))) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2471,c_28392])).

cnf(c_7107,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1638,c_1648])).

cnf(c_7983,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7107,c_48])).

cnf(c_7984,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7983])).

cnf(c_7989,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_7984])).

cnf(c_7991,plain,
    ( k5_relat_1(sK2,sK1) = sK1
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7989,c_2102])).

cnf(c_2119,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k5_relat_1(sK2,sK1)
    | k5_relat_1(sK2,sK1) = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | k5_relat_1(sK2,sK1) != k5_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1850])).

cnf(c_966,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2507,plain,
    ( k5_relat_1(sK2,sK1) = k5_relat_1(sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_1896,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_3078,plain,
    ( X0 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | X0 = sK1
    | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1896])).

cnf(c_4818,plain,
    ( k5_relat_1(sK2,sK1) != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | k5_relat_1(sK2,sK1) = sK1
    | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_3078])).

cnf(c_8061,plain,
    ( k5_relat_1(sK2,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7991,c_47,c_45,c_44,c_42,c_569,c_1725,c_1959,c_2119,c_2507,c_4818])).

cnf(c_3594,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3052,c_160])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1669,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4141,plain,
    ( k9_relat_1(sK1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3594,c_1669])).

cnf(c_5670,plain,
    ( k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_3386,c_4141])).

cnf(c_8063,plain,
    ( k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(sK1) ),
    inference(demodulation,[status(thm)],[c_8061,c_5670])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1668,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3599,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_3594,c_1668])).

cnf(c_8072,plain,
    ( k10_relat_1(sK1,k2_relat_1(sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_8067,c_3599])).

cnf(c_28406,plain,
    ( k2_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_28397,c_8063,c_8072])).

cnf(c_1650,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_8895,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X4,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1650,c_1672])).

cnf(c_1639,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1660,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4745,plain,
    ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1660,c_1669])).

cnf(c_17502,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2)))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_4745])).

cnf(c_17600,plain,
    ( v1_relat_1(X0) != iProver_top
    | k9_relat_1(k2_funct_1(sK2),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17502,c_47,c_48,c_49,c_45,c_50,c_44,c_51,c_52,c_42,c_53,c_55,c_131,c_134,c_160,c_569,c_1725,c_1798,c_1959,c_2105,c_2536,c_2662,c_3051,c_3436,c_3727,c_6966,c_9872,c_11198])).

cnf(c_17601,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2)))
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_17600])).

cnf(c_28993,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) = k2_relat_1(k5_relat_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k2_funct_1(sK2)))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8895,c_17601])).

cnf(c_29281,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2))) = k2_relat_1(k5_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2),k2_funct_1(sK2)))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_28993])).

cnf(c_29362,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k9_relat_1(k2_funct_1(sK2),k2_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2))) = k2_relat_1(k5_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2),k2_funct_1(sK2)))
    | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_29281,c_51])).

cnf(c_29363,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2))) = k2_relat_1(k5_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2),k2_funct_1(sK2)))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_29362])).

cnf(c_29369,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2))) = k2_relat_1(k5_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2),k2_funct_1(sK2)))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1641,c_29363])).

cnf(c_1636,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_17608,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k2_funct_1(X0))) = k2_relat_1(k5_relat_1(k2_funct_1(X0),k2_funct_1(sK2)))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1660,c_17601])).

cnf(c_20150,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k2_funct_1(sK1))) = k2_relat_1(k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)))
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_17608])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1657,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_6158,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_1657])).

cnf(c_6338,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6158,c_55,c_160,c_3052])).

cnf(c_8070,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_8067,c_6338])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1655,plain,
    ( k5_relat_1(k2_funct_1(X0),k2_funct_1(X1)) = k2_funct_1(k5_relat_1(X1,X0))
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8946,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1636,c_1655])).

cnf(c_10542,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8946,c_55,c_160,c_3052])).

cnf(c_10543,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10542])).

cnf(c_10550,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,sK1))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_10543])).

cnf(c_10552,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK1)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10550,c_8061])).

cnf(c_11749,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10552,c_47,c_48,c_49,c_45,c_50,c_44,c_51,c_52,c_42,c_53,c_55,c_131,c_134,c_160,c_569,c_1725,c_1798,c_1959,c_2105,c_2536,c_2662,c_3051,c_3436,c_3727,c_6966,c_9872,c_11198])).

cnf(c_20154,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = sK0
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_20150,c_8070,c_11749])).

cnf(c_20168,plain,
    ( k9_relat_1(k2_funct_1(sK2),sK0) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_20154,c_55,c_160,c_3052])).

cnf(c_28476,plain,
    ( k2_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_28406,c_160,c_3051])).

cnf(c_4140,plain,
    ( k9_relat_1(sK2,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK2))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3386,c_1669])).

cnf(c_5580,plain,
    ( k9_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,sK2)) ),
    inference(superposition,[status(thm)],[c_3386,c_4140])).

cnf(c_28518,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK2)) = k9_relat_1(sK2,sK0) ),
    inference(demodulation,[status(thm)],[c_28476,c_5580])).

cnf(c_28519,plain,
    ( k9_relat_1(sK2,sK0) = sK0 ),
    inference(demodulation,[status(thm)],[c_28476,c_4509])).

cnf(c_28521,plain,
    ( k2_relat_1(k5_relat_1(sK2,sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_28518,c_28519])).

cnf(c_29378,plain,
    ( k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k2_funct_1(sK2))) = sK0
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_29369,c_7605,c_20168,c_28521])).

cnf(c_29447,plain,
    ( k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k2_funct_1(sK2))) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29378,c_51,c_160])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1667,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_29452,plain,
    ( k5_relat_1(k5_relat_1(sK2,sK2),k2_funct_1(sK2)) = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29447,c_1667])).

cnf(c_1741,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1751,plain,
    ( X0 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | sK1 = X0
    | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1741])).

cnf(c_1756,plain,
    ( sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1751])).

cnf(c_8075,plain,
    ( sK1 = k1_xboole_0
    | sK0 != k1_xboole_0
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_8067,c_1666])).

cnf(c_1738,plain,
    ( X0 != X1
    | sK2 != X1
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_967])).

cnf(c_1799,plain,
    ( X0 != k1_xboole_0
    | sK2 = X0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1738])).

cnf(c_16328,plain,
    ( sK1 != k1_xboole_0
    | sK2 = sK1
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1799])).

cnf(c_1753,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1741])).

cnf(c_24978,plain,
    ( sK1 != sK1
    | sK1 = sK2
    | sK2 != sK1 ),
    inference(instantiation,[status(thm)],[c_1753])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != X0
    | k6_partfun1(k1_relat_1(X1)) = X1
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f128])).

cnf(c_1658,plain,
    ( k5_relat_1(X0,X1) != X0
    | k6_partfun1(k1_relat_1(X1)) = X1
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_8064,plain,
    ( k6_partfun1(k1_relat_1(sK1)) = sK1
    | k1_relat_1(sK1) != k2_relat_1(sK2)
    | sK1 != sK2
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8061,c_1658])).

cnf(c_159,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3053,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3051])).

cnf(c_3054,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0))
    | v1_relat_1(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3052])).

cnf(c_8065,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK1)) = sK1
    | k1_relat_1(sK1) != k2_relat_1(sK2)
    | sK1 != sK2 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8064])).

cnf(c_27517,plain,
    ( k6_partfun1(k1_relat_1(sK1)) = sK1
    | k1_relat_1(sK1) != k2_relat_1(sK2)
    | sK1 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8064,c_47,c_44,c_159,c_3053,c_3054,c_8065])).

cnf(c_27519,plain,
    ( k6_partfun1(sK0) = sK1
    | k2_relat_1(sK2) != sK0
    | sK1 != sK2 ),
    inference(light_normalisation,[status(thm)],[c_27517,c_8067])).

cnf(c_39,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_582,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK2
    | k6_partfun1(sK0) != sK1
    | sK0 != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_41])).

cnf(c_689,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK2
    | k6_partfun1(sK0) != sK1 ),
    inference(equality_resolution_simp,[status(thm)],[c_582])).

cnf(c_2104,plain,
    ( k6_partfun1(sK0) != sK1
    | sK1 != sK2 ),
    inference(demodulation,[status(thm)],[c_2102,c_689])).

cnf(c_27520,plain,
    ( k2_relat_1(sK2) != sK0
    | sK1 != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27519,c_2104])).

cnf(c_29661,plain,
    ( sK0 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_29452,c_47,c_45,c_44,c_42,c_160,c_569,c_1725,c_1756,c_2104,c_3051,c_3052,c_8075,c_11198,c_16328,c_24978,c_27519,c_28406])).

cnf(c_173435,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_15950,c_47,c_45,c_44,c_43,c_42,c_160,c_569,c_1725,c_1756,c_2104,c_3051,c_3052,c_8075,c_11198,c_15629,c_15952,c_16328,c_24978,c_27519,c_28406])).

cnf(c_11751,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1))
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11749,c_1658])).

cnf(c_11752,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) != sK0
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11751,c_8070])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2644,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2645,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2644])).

cnf(c_2647,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2648,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2647])).

cnf(c_5130,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_5131,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5130])).

cnf(c_5133,plain,
    ( ~ v1_funct_1(sK1)
    | ~ v2_funct_1(sK1)
    | v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_5134,plain,
    ( v1_funct_1(sK1) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5133])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1656,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5262,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_1656])).

cnf(c_5270,plain,
    ( v2_funct_1(sK2) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5262,c_160,c_3051])).

cnf(c_5271,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5270])).

cnf(c_15632,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_15627,c_5271])).

cnf(c_28514,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_28476,c_15632])).

cnf(c_51055,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11752,c_47,c_48,c_49,c_45,c_50,c_44,c_51,c_52,c_42,c_53,c_55,c_131,c_134,c_160,c_569,c_1725,c_1798,c_1959,c_2105,c_2536,c_2645,c_2648,c_2662,c_3051,c_3052,c_3436,c_3727,c_5131,c_5134,c_6966,c_9872,c_11198,c_28514])).

cnf(c_51057,plain,
    ( k2_funct_1(sK2) = k6_partfun1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_51055,c_28514])).

cnf(c_173437,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = k6_partfun1(sK0) ),
    inference(light_normalisation,[status(thm)],[c_173435,c_51057])).

cnf(c_173438,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k2_relat_1(k6_partfun1(sK0)) != k1_relat_1(sK2)
    | v1_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_173437,c_1658])).

cnf(c_173441,plain,
    ( k6_partfun1(sK0) = sK2
    | k2_relat_1(k6_partfun1(sK0)) != sK0
    | v1_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_173438,c_11190])).

cnf(c_10,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f123])).

cnf(c_173442,plain,
    ( k6_partfun1(sK0) = sK2
    | sK0 != sK0
    | v1_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_173441,c_10])).

cnf(c_173443,plain,
    ( k6_partfun1(sK0) = sK2
    | v1_funct_1(k6_partfun1(sK0)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k6_partfun1(sK0)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_173442])).

cnf(c_970,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_57140,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | X2 != X0
    | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != X1 ),
    inference(instantiation,[status(thm)],[c_970])).

cnf(c_60075,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0 != sK2
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_57140])).

cnf(c_61006,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | X0 != sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_60075])).

cnf(c_65065,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) != sK2
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_61006])).

cnf(c_969,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_61012,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_969])).

cnf(c_61014,plain,
    ( k2_zfmisc_1(sK0,sK0) != k2_zfmisc_1(sK0,sK0)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
    inference(instantiation,[status(thm)],[c_61012])).

cnf(c_1661,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_51206,plain,
    ( v1_funct_1(k6_partfun1(sK0)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_51057,c_1661])).

cnf(c_1744,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_1737,plain,
    ( k6_partfun1(sK0) != sK2
    | sK2 = k6_partfun1(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1723])).

cnf(c_1001,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_966])).

cnf(c_973,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_989,plain,
    ( k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK0,sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_27,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_558,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_39])).

cnf(c_559,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_558])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_173443,c_65065,c_61014,c_51206,c_15627,c_3051,c_1744,c_1737,c_1001,c_989,c_559,c_160,c_131,c_42,c_51])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:39:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 51.53/6.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 51.53/6.99  
% 51.53/6.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.53/6.99  
% 51.53/6.99  ------  iProver source info
% 51.53/6.99  
% 51.53/6.99  git: date: 2020-06-30 10:37:57 +0100
% 51.53/6.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.53/6.99  git: non_committed_changes: false
% 51.53/6.99  git: last_make_outside_of_git: false
% 51.53/6.99  
% 51.53/6.99  ------ 
% 51.53/6.99  
% 51.53/6.99  ------ Input Options
% 51.53/6.99  
% 51.53/6.99  --out_options                           all
% 51.53/6.99  --tptp_safe_out                         true
% 51.53/6.99  --problem_path                          ""
% 51.53/6.99  --include_path                          ""
% 51.53/6.99  --clausifier                            res/vclausify_rel
% 51.53/6.99  --clausifier_options                    ""
% 51.53/6.99  --stdin                                 false
% 51.53/6.99  --stats_out                             all
% 51.53/6.99  
% 51.53/6.99  ------ General Options
% 51.53/6.99  
% 51.53/6.99  --fof                                   false
% 51.53/6.99  --time_out_real                         305.
% 51.53/6.99  --time_out_virtual                      -1.
% 51.53/6.99  --symbol_type_check                     false
% 51.53/6.99  --clausify_out                          false
% 51.53/6.99  --sig_cnt_out                           false
% 51.53/6.99  --trig_cnt_out                          false
% 51.53/6.99  --trig_cnt_out_tolerance                1.
% 51.53/6.99  --trig_cnt_out_sk_spl                   false
% 51.53/6.99  --abstr_cl_out                          false
% 51.53/6.99  
% 51.53/6.99  ------ Global Options
% 51.53/6.99  
% 51.53/6.99  --schedule                              default
% 51.53/6.99  --add_important_lit                     false
% 51.53/6.99  --prop_solver_per_cl                    1000
% 51.53/6.99  --min_unsat_core                        false
% 51.53/6.99  --soft_assumptions                      false
% 51.53/6.99  --soft_lemma_size                       3
% 51.53/6.99  --prop_impl_unit_size                   0
% 51.53/6.99  --prop_impl_unit                        []
% 51.53/6.99  --share_sel_clauses                     true
% 51.53/6.99  --reset_solvers                         false
% 51.53/6.99  --bc_imp_inh                            [conj_cone]
% 51.53/6.99  --conj_cone_tolerance                   3.
% 51.53/6.99  --extra_neg_conj                        none
% 51.53/6.99  --large_theory_mode                     true
% 51.53/6.99  --prolific_symb_bound                   200
% 51.53/6.99  --lt_threshold                          2000
% 51.53/6.99  --clause_weak_htbl                      true
% 51.53/6.99  --gc_record_bc_elim                     false
% 51.53/6.99  
% 51.53/6.99  ------ Preprocessing Options
% 51.53/6.99  
% 51.53/6.99  --preprocessing_flag                    true
% 51.53/6.99  --time_out_prep_mult                    0.1
% 51.53/6.99  --splitting_mode                        input
% 51.53/6.99  --splitting_grd                         true
% 51.53/6.99  --splitting_cvd                         false
% 51.53/6.99  --splitting_cvd_svl                     false
% 51.53/6.99  --splitting_nvd                         32
% 51.53/6.99  --sub_typing                            true
% 51.53/6.99  --prep_gs_sim                           true
% 51.53/6.99  --prep_unflatten                        true
% 51.53/6.99  --prep_res_sim                          true
% 51.53/6.99  --prep_upred                            true
% 51.53/6.99  --prep_sem_filter                       exhaustive
% 51.53/6.99  --prep_sem_filter_out                   false
% 51.53/6.99  --pred_elim                             true
% 51.53/6.99  --res_sim_input                         true
% 51.53/6.99  --eq_ax_congr_red                       true
% 51.53/6.99  --pure_diseq_elim                       true
% 51.53/6.99  --brand_transform                       false
% 51.53/6.99  --non_eq_to_eq                          false
% 51.53/6.99  --prep_def_merge                        true
% 51.53/6.99  --prep_def_merge_prop_impl              false
% 51.53/6.99  --prep_def_merge_mbd                    true
% 51.53/6.99  --prep_def_merge_tr_red                 false
% 51.53/6.99  --prep_def_merge_tr_cl                  false
% 51.53/6.99  --smt_preprocessing                     true
% 51.53/6.99  --smt_ac_axioms                         fast
% 51.53/6.99  --preprocessed_out                      false
% 51.53/6.99  --preprocessed_stats                    false
% 51.53/6.99  
% 51.53/6.99  ------ Abstraction refinement Options
% 51.53/6.99  
% 51.53/6.99  --abstr_ref                             []
% 51.53/6.99  --abstr_ref_prep                        false
% 51.53/6.99  --abstr_ref_until_sat                   false
% 51.53/6.99  --abstr_ref_sig_restrict                funpre
% 51.53/6.99  --abstr_ref_af_restrict_to_split_sk     false
% 51.53/6.99  --abstr_ref_under                       []
% 51.53/6.99  
% 51.53/6.99  ------ SAT Options
% 51.53/6.99  
% 51.53/6.99  --sat_mode                              false
% 51.53/6.99  --sat_fm_restart_options                ""
% 51.53/6.99  --sat_gr_def                            false
% 51.53/6.99  --sat_epr_types                         true
% 51.53/6.99  --sat_non_cyclic_types                  false
% 51.53/6.99  --sat_finite_models                     false
% 51.53/6.99  --sat_fm_lemmas                         false
% 51.53/6.99  --sat_fm_prep                           false
% 51.53/6.99  --sat_fm_uc_incr                        true
% 51.53/6.99  --sat_out_model                         small
% 51.53/6.99  --sat_out_clauses                       false
% 51.53/6.99  
% 51.53/6.99  ------ QBF Options
% 51.53/6.99  
% 51.53/6.99  --qbf_mode                              false
% 51.53/6.99  --qbf_elim_univ                         false
% 51.53/6.99  --qbf_dom_inst                          none
% 51.53/6.99  --qbf_dom_pre_inst                      false
% 51.53/6.99  --qbf_sk_in                             false
% 51.53/6.99  --qbf_pred_elim                         true
% 51.53/6.99  --qbf_split                             512
% 51.53/6.99  
% 51.53/6.99  ------ BMC1 Options
% 51.53/6.99  
% 51.53/6.99  --bmc1_incremental                      false
% 51.53/6.99  --bmc1_axioms                           reachable_all
% 51.53/6.99  --bmc1_min_bound                        0
% 51.53/6.99  --bmc1_max_bound                        -1
% 51.53/6.99  --bmc1_max_bound_default                -1
% 51.53/6.99  --bmc1_symbol_reachability              true
% 51.53/6.99  --bmc1_property_lemmas                  false
% 51.53/6.99  --bmc1_k_induction                      false
% 51.53/6.99  --bmc1_non_equiv_states                 false
% 51.53/6.99  --bmc1_deadlock                         false
% 51.53/6.99  --bmc1_ucm                              false
% 51.53/6.99  --bmc1_add_unsat_core                   none
% 51.53/6.99  --bmc1_unsat_core_children              false
% 51.53/6.99  --bmc1_unsat_core_extrapolate_axioms    false
% 51.53/6.99  --bmc1_out_stat                         full
% 51.53/6.99  --bmc1_ground_init                      false
% 51.53/6.99  --bmc1_pre_inst_next_state              false
% 51.53/6.99  --bmc1_pre_inst_state                   false
% 51.53/6.99  --bmc1_pre_inst_reach_state             false
% 51.53/6.99  --bmc1_out_unsat_core                   false
% 51.53/6.99  --bmc1_aig_witness_out                  false
% 51.53/6.99  --bmc1_verbose                          false
% 51.53/6.99  --bmc1_dump_clauses_tptp                false
% 51.53/6.99  --bmc1_dump_unsat_core_tptp             false
% 51.53/6.99  --bmc1_dump_file                        -
% 51.53/6.99  --bmc1_ucm_expand_uc_limit              128
% 51.53/6.99  --bmc1_ucm_n_expand_iterations          6
% 51.53/6.99  --bmc1_ucm_extend_mode                  1
% 51.53/6.99  --bmc1_ucm_init_mode                    2
% 51.53/6.99  --bmc1_ucm_cone_mode                    none
% 51.53/6.99  --bmc1_ucm_reduced_relation_type        0
% 51.53/6.99  --bmc1_ucm_relax_model                  4
% 51.53/6.99  --bmc1_ucm_full_tr_after_sat            true
% 51.53/6.99  --bmc1_ucm_expand_neg_assumptions       false
% 51.53/6.99  --bmc1_ucm_layered_model                none
% 51.53/7.00  --bmc1_ucm_max_lemma_size               10
% 51.53/7.00  
% 51.53/7.00  ------ AIG Options
% 51.53/7.00  
% 51.53/7.00  --aig_mode                              false
% 51.53/7.00  
% 51.53/7.00  ------ Instantiation Options
% 51.53/7.00  
% 51.53/7.00  --instantiation_flag                    true
% 51.53/7.00  --inst_sos_flag                         true
% 51.53/7.00  --inst_sos_phase                        true
% 51.53/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.53/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.53/7.00  --inst_lit_sel_side                     num_symb
% 51.53/7.00  --inst_solver_per_active                1400
% 51.53/7.00  --inst_solver_calls_frac                1.
% 51.53/7.00  --inst_passive_queue_type               priority_queues
% 51.53/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.53/7.00  --inst_passive_queues_freq              [25;2]
% 51.53/7.00  --inst_dismatching                      true
% 51.53/7.00  --inst_eager_unprocessed_to_passive     true
% 51.53/7.00  --inst_prop_sim_given                   true
% 51.53/7.00  --inst_prop_sim_new                     false
% 51.53/7.00  --inst_subs_new                         false
% 51.53/7.00  --inst_eq_res_simp                      false
% 51.53/7.00  --inst_subs_given                       false
% 51.53/7.00  --inst_orphan_elimination               true
% 51.53/7.00  --inst_learning_loop_flag               true
% 51.53/7.00  --inst_learning_start                   3000
% 51.53/7.00  --inst_learning_factor                  2
% 51.53/7.00  --inst_start_prop_sim_after_learn       3
% 51.53/7.00  --inst_sel_renew                        solver
% 51.53/7.00  --inst_lit_activity_flag                true
% 51.53/7.00  --inst_restr_to_given                   false
% 51.53/7.00  --inst_activity_threshold               500
% 51.53/7.00  --inst_out_proof                        true
% 51.53/7.00  
% 51.53/7.00  ------ Resolution Options
% 51.53/7.00  
% 51.53/7.00  --resolution_flag                       true
% 51.53/7.00  --res_lit_sel                           adaptive
% 51.53/7.00  --res_lit_sel_side                      none
% 51.53/7.00  --res_ordering                          kbo
% 51.53/7.00  --res_to_prop_solver                    active
% 51.53/7.00  --res_prop_simpl_new                    false
% 51.53/7.00  --res_prop_simpl_given                  true
% 51.53/7.00  --res_passive_queue_type                priority_queues
% 51.53/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.53/7.00  --res_passive_queues_freq               [15;5]
% 51.53/7.00  --res_forward_subs                      full
% 51.53/7.00  --res_backward_subs                     full
% 51.53/7.00  --res_forward_subs_resolution           true
% 51.53/7.00  --res_backward_subs_resolution          true
% 51.53/7.00  --res_orphan_elimination                true
% 51.53/7.00  --res_time_limit                        2.
% 51.53/7.00  --res_out_proof                         true
% 51.53/7.00  
% 51.53/7.00  ------ Superposition Options
% 51.53/7.00  
% 51.53/7.00  --superposition_flag                    true
% 51.53/7.00  --sup_passive_queue_type                priority_queues
% 51.53/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.53/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.53/7.00  --demod_completeness_check              fast
% 51.53/7.00  --demod_use_ground                      true
% 51.53/7.00  --sup_to_prop_solver                    passive
% 51.53/7.00  --sup_prop_simpl_new                    true
% 51.53/7.00  --sup_prop_simpl_given                  true
% 51.53/7.00  --sup_fun_splitting                     true
% 51.53/7.00  --sup_smt_interval                      50000
% 51.53/7.00  
% 51.53/7.00  ------ Superposition Simplification Setup
% 51.53/7.00  
% 51.53/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.53/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.53/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.53/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.53/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.53/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.53/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.53/7.00  --sup_immed_triv                        [TrivRules]
% 51.53/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.53/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.53/7.00  --sup_immed_bw_main                     []
% 51.53/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.53/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.53/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.53/7.00  --sup_input_bw                          []
% 51.53/7.00  
% 51.53/7.00  ------ Combination Options
% 51.53/7.00  
% 51.53/7.00  --comb_res_mult                         3
% 51.53/7.00  --comb_sup_mult                         2
% 51.53/7.00  --comb_inst_mult                        10
% 51.53/7.00  
% 51.53/7.00  ------ Debug Options
% 51.53/7.00  
% 51.53/7.00  --dbg_backtrace                         false
% 51.53/7.00  --dbg_dump_prop_clauses                 false
% 51.53/7.00  --dbg_dump_prop_clauses_file            -
% 51.53/7.00  --dbg_out_stat                          false
% 51.53/7.00  ------ Parsing...
% 51.53/7.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.53/7.00  
% 51.53/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.53/7.00  
% 51.53/7.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.53/7.00  
% 51.53/7.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.53/7.00  ------ Proving...
% 51.53/7.00  ------ Problem Properties 
% 51.53/7.00  
% 51.53/7.00  
% 51.53/7.00  clauses                                 44
% 51.53/7.00  conjectures                             7
% 51.53/7.00  EPR                                     5
% 51.53/7.00  Horn                                    41
% 51.53/7.00  unary                                   12
% 51.53/7.00  binary                                  9
% 51.53/7.00  lits                                    140
% 51.53/7.00  lits eq                                 35
% 51.53/7.00  fd_pure                                 0
% 51.53/7.00  fd_pseudo                               0
% 51.53/7.00  fd_cond                                 5
% 51.53/7.00  fd_pseudo_cond                          0
% 51.53/7.00  AC symbols                              0
% 51.53/7.00  
% 51.53/7.00  ------ Schedule dynamic 5 is on 
% 51.53/7.00  
% 51.53/7.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.53/7.00  
% 51.53/7.00  
% 51.53/7.00  ------ 
% 51.53/7.00  Current options:
% 51.53/7.00  ------ 
% 51.53/7.00  
% 51.53/7.00  ------ Input Options
% 51.53/7.00  
% 51.53/7.00  --out_options                           all
% 51.53/7.00  --tptp_safe_out                         true
% 51.53/7.00  --problem_path                          ""
% 51.53/7.00  --include_path                          ""
% 51.53/7.00  --clausifier                            res/vclausify_rel
% 51.53/7.00  --clausifier_options                    ""
% 51.53/7.00  --stdin                                 false
% 51.53/7.00  --stats_out                             all
% 51.53/7.00  
% 51.53/7.00  ------ General Options
% 51.53/7.00  
% 51.53/7.00  --fof                                   false
% 51.53/7.00  --time_out_real                         305.
% 51.53/7.00  --time_out_virtual                      -1.
% 51.53/7.00  --symbol_type_check                     false
% 51.53/7.00  --clausify_out                          false
% 51.53/7.00  --sig_cnt_out                           false
% 51.53/7.00  --trig_cnt_out                          false
% 51.53/7.00  --trig_cnt_out_tolerance                1.
% 51.53/7.00  --trig_cnt_out_sk_spl                   false
% 51.53/7.00  --abstr_cl_out                          false
% 51.53/7.00  
% 51.53/7.00  ------ Global Options
% 51.53/7.00  
% 51.53/7.00  --schedule                              default
% 51.53/7.00  --add_important_lit                     false
% 51.53/7.00  --prop_solver_per_cl                    1000
% 51.53/7.00  --min_unsat_core                        false
% 51.53/7.00  --soft_assumptions                      false
% 51.53/7.00  --soft_lemma_size                       3
% 51.53/7.00  --prop_impl_unit_size                   0
% 51.53/7.00  --prop_impl_unit                        []
% 51.53/7.00  --share_sel_clauses                     true
% 51.53/7.00  --reset_solvers                         false
% 51.53/7.00  --bc_imp_inh                            [conj_cone]
% 51.53/7.00  --conj_cone_tolerance                   3.
% 51.53/7.00  --extra_neg_conj                        none
% 51.53/7.00  --large_theory_mode                     true
% 51.53/7.00  --prolific_symb_bound                   200
% 51.53/7.00  --lt_threshold                          2000
% 51.53/7.00  --clause_weak_htbl                      true
% 51.53/7.00  --gc_record_bc_elim                     false
% 51.53/7.00  
% 51.53/7.00  ------ Preprocessing Options
% 51.53/7.00  
% 51.53/7.00  --preprocessing_flag                    true
% 51.53/7.00  --time_out_prep_mult                    0.1
% 51.53/7.00  --splitting_mode                        input
% 51.53/7.00  --splitting_grd                         true
% 51.53/7.00  --splitting_cvd                         false
% 51.53/7.00  --splitting_cvd_svl                     false
% 51.53/7.00  --splitting_nvd                         32
% 51.53/7.00  --sub_typing                            true
% 51.53/7.00  --prep_gs_sim                           true
% 51.53/7.00  --prep_unflatten                        true
% 51.53/7.00  --prep_res_sim                          true
% 51.53/7.00  --prep_upred                            true
% 51.53/7.00  --prep_sem_filter                       exhaustive
% 51.53/7.00  --prep_sem_filter_out                   false
% 51.53/7.00  --pred_elim                             true
% 51.53/7.00  --res_sim_input                         true
% 51.53/7.00  --eq_ax_congr_red                       true
% 51.53/7.00  --pure_diseq_elim                       true
% 51.53/7.00  --brand_transform                       false
% 51.53/7.00  --non_eq_to_eq                          false
% 51.53/7.00  --prep_def_merge                        true
% 51.53/7.00  --prep_def_merge_prop_impl              false
% 51.53/7.00  --prep_def_merge_mbd                    true
% 51.53/7.00  --prep_def_merge_tr_red                 false
% 51.53/7.00  --prep_def_merge_tr_cl                  false
% 51.53/7.00  --smt_preprocessing                     true
% 51.53/7.00  --smt_ac_axioms                         fast
% 51.53/7.00  --preprocessed_out                      false
% 51.53/7.00  --preprocessed_stats                    false
% 51.53/7.00  
% 51.53/7.00  ------ Abstraction refinement Options
% 51.53/7.00  
% 51.53/7.00  --abstr_ref                             []
% 51.53/7.00  --abstr_ref_prep                        false
% 51.53/7.00  --abstr_ref_until_sat                   false
% 51.53/7.00  --abstr_ref_sig_restrict                funpre
% 51.53/7.00  --abstr_ref_af_restrict_to_split_sk     false
% 51.53/7.00  --abstr_ref_under                       []
% 51.53/7.00  
% 51.53/7.00  ------ SAT Options
% 51.53/7.00  
% 51.53/7.00  --sat_mode                              false
% 51.53/7.00  --sat_fm_restart_options                ""
% 51.53/7.00  --sat_gr_def                            false
% 51.53/7.00  --sat_epr_types                         true
% 51.53/7.00  --sat_non_cyclic_types                  false
% 51.53/7.00  --sat_finite_models                     false
% 51.53/7.00  --sat_fm_lemmas                         false
% 51.53/7.00  --sat_fm_prep                           false
% 51.53/7.00  --sat_fm_uc_incr                        true
% 51.53/7.00  --sat_out_model                         small
% 51.53/7.00  --sat_out_clauses                       false
% 51.53/7.00  
% 51.53/7.00  ------ QBF Options
% 51.53/7.00  
% 51.53/7.00  --qbf_mode                              false
% 51.53/7.00  --qbf_elim_univ                         false
% 51.53/7.00  --qbf_dom_inst                          none
% 51.53/7.00  --qbf_dom_pre_inst                      false
% 51.53/7.00  --qbf_sk_in                             false
% 51.53/7.00  --qbf_pred_elim                         true
% 51.53/7.00  --qbf_split                             512
% 51.53/7.00  
% 51.53/7.00  ------ BMC1 Options
% 51.53/7.00  
% 51.53/7.00  --bmc1_incremental                      false
% 51.53/7.00  --bmc1_axioms                           reachable_all
% 51.53/7.00  --bmc1_min_bound                        0
% 51.53/7.00  --bmc1_max_bound                        -1
% 51.53/7.00  --bmc1_max_bound_default                -1
% 51.53/7.00  --bmc1_symbol_reachability              true
% 51.53/7.00  --bmc1_property_lemmas                  false
% 51.53/7.00  --bmc1_k_induction                      false
% 51.53/7.00  --bmc1_non_equiv_states                 false
% 51.53/7.00  --bmc1_deadlock                         false
% 51.53/7.00  --bmc1_ucm                              false
% 51.53/7.00  --bmc1_add_unsat_core                   none
% 51.53/7.00  --bmc1_unsat_core_children              false
% 51.53/7.00  --bmc1_unsat_core_extrapolate_axioms    false
% 51.53/7.00  --bmc1_out_stat                         full
% 51.53/7.00  --bmc1_ground_init                      false
% 51.53/7.00  --bmc1_pre_inst_next_state              false
% 51.53/7.00  --bmc1_pre_inst_state                   false
% 51.53/7.00  --bmc1_pre_inst_reach_state             false
% 51.53/7.00  --bmc1_out_unsat_core                   false
% 51.53/7.00  --bmc1_aig_witness_out                  false
% 51.53/7.00  --bmc1_verbose                          false
% 51.53/7.00  --bmc1_dump_clauses_tptp                false
% 51.53/7.00  --bmc1_dump_unsat_core_tptp             false
% 51.53/7.00  --bmc1_dump_file                        -
% 51.53/7.00  --bmc1_ucm_expand_uc_limit              128
% 51.53/7.00  --bmc1_ucm_n_expand_iterations          6
% 51.53/7.00  --bmc1_ucm_extend_mode                  1
% 51.53/7.00  --bmc1_ucm_init_mode                    2
% 51.53/7.00  --bmc1_ucm_cone_mode                    none
% 51.53/7.00  --bmc1_ucm_reduced_relation_type        0
% 51.53/7.00  --bmc1_ucm_relax_model                  4
% 51.53/7.00  --bmc1_ucm_full_tr_after_sat            true
% 51.53/7.00  --bmc1_ucm_expand_neg_assumptions       false
% 51.53/7.00  --bmc1_ucm_layered_model                none
% 51.53/7.00  --bmc1_ucm_max_lemma_size               10
% 51.53/7.00  
% 51.53/7.00  ------ AIG Options
% 51.53/7.00  
% 51.53/7.00  --aig_mode                              false
% 51.53/7.00  
% 51.53/7.00  ------ Instantiation Options
% 51.53/7.00  
% 51.53/7.00  --instantiation_flag                    true
% 51.53/7.00  --inst_sos_flag                         true
% 51.53/7.00  --inst_sos_phase                        true
% 51.53/7.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.53/7.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.53/7.00  --inst_lit_sel_side                     none
% 51.53/7.00  --inst_solver_per_active                1400
% 51.53/7.00  --inst_solver_calls_frac                1.
% 51.53/7.00  --inst_passive_queue_type               priority_queues
% 51.53/7.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.53/7.00  --inst_passive_queues_freq              [25;2]
% 51.53/7.00  --inst_dismatching                      true
% 51.53/7.00  --inst_eager_unprocessed_to_passive     true
% 51.53/7.00  --inst_prop_sim_given                   true
% 51.53/7.00  --inst_prop_sim_new                     false
% 51.53/7.00  --inst_subs_new                         false
% 51.53/7.00  --inst_eq_res_simp                      false
% 51.53/7.00  --inst_subs_given                       false
% 51.53/7.00  --inst_orphan_elimination               true
% 51.53/7.00  --inst_learning_loop_flag               true
% 51.53/7.00  --inst_learning_start                   3000
% 51.53/7.00  --inst_learning_factor                  2
% 51.53/7.00  --inst_start_prop_sim_after_learn       3
% 51.53/7.00  --inst_sel_renew                        solver
% 51.53/7.00  --inst_lit_activity_flag                true
% 51.53/7.00  --inst_restr_to_given                   false
% 51.53/7.00  --inst_activity_threshold               500
% 51.53/7.00  --inst_out_proof                        true
% 51.53/7.00  
% 51.53/7.00  ------ Resolution Options
% 51.53/7.00  
% 51.53/7.00  --resolution_flag                       false
% 51.53/7.00  --res_lit_sel                           adaptive
% 51.53/7.00  --res_lit_sel_side                      none
% 51.53/7.00  --res_ordering                          kbo
% 51.53/7.00  --res_to_prop_solver                    active
% 51.53/7.00  --res_prop_simpl_new                    false
% 51.53/7.00  --res_prop_simpl_given                  true
% 51.53/7.00  --res_passive_queue_type                priority_queues
% 51.53/7.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.53/7.00  --res_passive_queues_freq               [15;5]
% 51.53/7.00  --res_forward_subs                      full
% 51.53/7.00  --res_backward_subs                     full
% 51.53/7.00  --res_forward_subs_resolution           true
% 51.53/7.00  --res_backward_subs_resolution          true
% 51.53/7.00  --res_orphan_elimination                true
% 51.53/7.00  --res_time_limit                        2.
% 51.53/7.00  --res_out_proof                         true
% 51.53/7.00  
% 51.53/7.00  ------ Superposition Options
% 51.53/7.00  
% 51.53/7.00  --superposition_flag                    true
% 51.53/7.00  --sup_passive_queue_type                priority_queues
% 51.53/7.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.53/7.00  --sup_passive_queues_freq               [8;1;4]
% 51.53/7.00  --demod_completeness_check              fast
% 51.53/7.00  --demod_use_ground                      true
% 51.53/7.00  --sup_to_prop_solver                    passive
% 51.53/7.00  --sup_prop_simpl_new                    true
% 51.53/7.00  --sup_prop_simpl_given                  true
% 51.53/7.00  --sup_fun_splitting                     true
% 51.53/7.00  --sup_smt_interval                      50000
% 51.53/7.00  
% 51.53/7.00  ------ Superposition Simplification Setup
% 51.53/7.00  
% 51.53/7.00  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.53/7.00  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.53/7.00  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.53/7.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.53/7.00  --sup_full_triv                         [TrivRules;PropSubs]
% 51.53/7.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.53/7.00  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.53/7.00  --sup_immed_triv                        [TrivRules]
% 51.53/7.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.53/7.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.53/7.00  --sup_immed_bw_main                     []
% 51.53/7.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.53/7.00  --sup_input_triv                        [Unflattening;TrivRules]
% 51.53/7.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.53/7.00  --sup_input_bw                          []
% 51.53/7.00  
% 51.53/7.00  ------ Combination Options
% 51.53/7.00  
% 51.53/7.00  --comb_res_mult                         3
% 51.53/7.00  --comb_sup_mult                         2
% 51.53/7.00  --comb_inst_mult                        10
% 51.53/7.00  
% 51.53/7.00  ------ Debug Options
% 51.53/7.00  
% 51.53/7.00  --dbg_backtrace                         false
% 51.53/7.00  --dbg_dump_prop_clauses                 false
% 51.53/7.00  --dbg_dump_prop_clauses_file            -
% 51.53/7.00  --dbg_out_stat                          false
% 51.53/7.00  
% 51.53/7.00  
% 51.53/7.00  
% 51.53/7.00  
% 51.53/7.00  ------ Proving...
% 51.53/7.00  
% 51.53/7.00  
% 51.53/7.00  % SZS status Theorem for theBenchmark.p
% 51.53/7.00  
% 51.53/7.00  % SZS output start CNFRefutation for theBenchmark.p
% 51.53/7.00  
% 51.53/7.00  fof(f28,conjecture,(
% 51.53/7.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f29,negated_conjecture,(
% 51.53/7.00    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 51.53/7.00    inference(negated_conjecture,[],[f28])).
% 51.53/7.00  
% 51.53/7.00  fof(f67,plain,(
% 51.53/7.00    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 51.53/7.00    inference(ennf_transformation,[],[f29])).
% 51.53/7.00  
% 51.53/7.00  fof(f68,plain,(
% 51.53/7.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 51.53/7.00    inference(flattening,[],[f67])).
% 51.53/7.00  
% 51.53/7.00  fof(f72,plain,(
% 51.53/7.00    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK2,X1),X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 51.53/7.00    introduced(choice_axiom,[])).
% 51.53/7.00  
% 51.53/7.00  fof(f71,plain,(
% 51.53/7.00    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 51.53/7.00    introduced(choice_axiom,[])).
% 51.53/7.00  
% 51.53/7.00  fof(f73,plain,(
% 51.53/7.00    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 51.53/7.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f68,f72,f71])).
% 51.53/7.00  
% 51.53/7.00  fof(f119,plain,(
% 51.53/7.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 51.53/7.00    inference(cnf_transformation,[],[f73])).
% 51.53/7.00  
% 51.53/7.00  fof(f17,axiom,(
% 51.53/7.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f51,plain,(
% 51.53/7.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.53/7.00    inference(ennf_transformation,[],[f17])).
% 51.53/7.00  
% 51.53/7.00  fof(f97,plain,(
% 51.53/7.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.53/7.00    inference(cnf_transformation,[],[f51])).
% 51.53/7.00  
% 51.53/7.00  fof(f7,axiom,(
% 51.53/7.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f35,plain,(
% 51.53/7.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 51.53/7.00    inference(ennf_transformation,[],[f7])).
% 51.53/7.00  
% 51.53/7.00  fof(f36,plain,(
% 51.53/7.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 51.53/7.00    inference(flattening,[],[f35])).
% 51.53/7.00  
% 51.53/7.00  fof(f81,plain,(
% 51.53/7.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f36])).
% 51.53/7.00  
% 51.53/7.00  fof(f3,axiom,(
% 51.53/7.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f77,plain,(
% 51.53/7.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 51.53/7.00    inference(cnf_transformation,[],[f3])).
% 51.53/7.00  
% 51.53/7.00  fof(f1,axiom,(
% 51.53/7.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f30,plain,(
% 51.53/7.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 51.53/7.00    inference(ennf_transformation,[],[f1])).
% 51.53/7.00  
% 51.53/7.00  fof(f74,plain,(
% 51.53/7.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f30])).
% 51.53/7.00  
% 51.53/7.00  fof(f4,axiom,(
% 51.53/7.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f32,plain,(
% 51.53/7.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 51.53/7.00    inference(ennf_transformation,[],[f4])).
% 51.53/7.00  
% 51.53/7.00  fof(f78,plain,(
% 51.53/7.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f32])).
% 51.53/7.00  
% 51.53/7.00  fof(f21,axiom,(
% 51.53/7.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f56,plain,(
% 51.53/7.00    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.53/7.00    inference(ennf_transformation,[],[f21])).
% 51.53/7.00  
% 51.53/7.00  fof(f103,plain,(
% 51.53/7.00    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.53/7.00    inference(cnf_transformation,[],[f56])).
% 51.53/7.00  
% 51.53/7.00  fof(f19,axiom,(
% 51.53/7.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f53,plain,(
% 51.53/7.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.53/7.00    inference(ennf_transformation,[],[f19])).
% 51.53/7.00  
% 51.53/7.00  fof(f100,plain,(
% 51.53/7.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.53/7.00    inference(cnf_transformation,[],[f53])).
% 51.53/7.00  
% 51.53/7.00  fof(f26,axiom,(
% 51.53/7.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f63,plain,(
% 51.53/7.00    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 51.53/7.00    inference(ennf_transformation,[],[f26])).
% 51.53/7.00  
% 51.53/7.00  fof(f64,plain,(
% 51.53/7.00    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 51.53/7.00    inference(flattening,[],[f63])).
% 51.53/7.00  
% 51.53/7.00  fof(f112,plain,(
% 51.53/7.00    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f64])).
% 51.53/7.00  
% 51.53/7.00  fof(f117,plain,(
% 51.53/7.00    v1_funct_1(sK2)),
% 51.53/7.00    inference(cnf_transformation,[],[f73])).
% 51.53/7.00  
% 51.53/7.00  fof(f118,plain,(
% 51.53/7.00    v1_funct_2(sK2,sK0,sK0)),
% 51.53/7.00    inference(cnf_transformation,[],[f73])).
% 51.53/7.00  
% 51.53/7.00  fof(f23,axiom,(
% 51.53/7.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f59,plain,(
% 51.53/7.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 51.53/7.00    inference(ennf_transformation,[],[f23])).
% 51.53/7.00  
% 51.53/7.00  fof(f60,plain,(
% 51.53/7.00    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 51.53/7.00    inference(flattening,[],[f59])).
% 51.53/7.00  
% 51.53/7.00  fof(f107,plain,(
% 51.53/7.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f60])).
% 51.53/7.00  
% 51.53/7.00  fof(f25,axiom,(
% 51.53/7.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f61,plain,(
% 51.53/7.00    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 51.53/7.00    inference(ennf_transformation,[],[f25])).
% 51.53/7.00  
% 51.53/7.00  fof(f62,plain,(
% 51.53/7.00    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 51.53/7.00    inference(flattening,[],[f61])).
% 51.53/7.00  
% 51.53/7.00  fof(f109,plain,(
% 51.53/7.00    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f62])).
% 51.53/7.00  
% 51.53/7.00  fof(f114,plain,(
% 51.53/7.00    v1_funct_1(sK1)),
% 51.53/7.00    inference(cnf_transformation,[],[f73])).
% 51.53/7.00  
% 51.53/7.00  fof(f115,plain,(
% 51.53/7.00    v1_funct_2(sK1,sK0,sK0)),
% 51.53/7.00    inference(cnf_transformation,[],[f73])).
% 51.53/7.00  
% 51.53/7.00  fof(f116,plain,(
% 51.53/7.00    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 51.53/7.00    inference(cnf_transformation,[],[f73])).
% 51.53/7.00  
% 51.53/7.00  fof(f121,plain,(
% 51.53/7.00    v2_funct_1(sK1)),
% 51.53/7.00    inference(cnf_transformation,[],[f73])).
% 51.53/7.00  
% 51.53/7.00  fof(f11,axiom,(
% 51.53/7.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f87,plain,(
% 51.53/7.00    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 51.53/7.00    inference(cnf_transformation,[],[f11])).
% 51.53/7.00  
% 51.53/7.00  fof(f24,axiom,(
% 51.53/7.00    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f108,plain,(
% 51.53/7.00    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f24])).
% 51.53/7.00  
% 51.53/7.00  fof(f127,plain,(
% 51.53/7.00    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 51.53/7.00    inference(definition_unfolding,[],[f87,f108])).
% 51.53/7.00  
% 51.53/7.00  fof(f88,plain,(
% 51.53/7.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 51.53/7.00    inference(cnf_transformation,[],[f11])).
% 51.53/7.00  
% 51.53/7.00  fof(f126,plain,(
% 51.53/7.00    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 51.53/7.00    inference(definition_unfolding,[],[f88,f108])).
% 51.53/7.00  
% 51.53/7.00  fof(f20,axiom,(
% 51.53/7.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f54,plain,(
% 51.53/7.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 51.53/7.00    inference(ennf_transformation,[],[f20])).
% 51.53/7.00  
% 51.53/7.00  fof(f55,plain,(
% 51.53/7.00    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.53/7.00    inference(flattening,[],[f54])).
% 51.53/7.00  
% 51.53/7.00  fof(f70,plain,(
% 51.53/7.00    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.53/7.00    inference(nnf_transformation,[],[f55])).
% 51.53/7.00  
% 51.53/7.00  fof(f101,plain,(
% 51.53/7.00    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.53/7.00    inference(cnf_transformation,[],[f70])).
% 51.53/7.00  
% 51.53/7.00  fof(f120,plain,(
% 51.53/7.00    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 51.53/7.00    inference(cnf_transformation,[],[f73])).
% 51.53/7.00  
% 51.53/7.00  fof(f22,axiom,(
% 51.53/7.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f57,plain,(
% 51.53/7.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 51.53/7.00    inference(ennf_transformation,[],[f22])).
% 51.53/7.00  
% 51.53/7.00  fof(f58,plain,(
% 51.53/7.00    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 51.53/7.00    inference(flattening,[],[f57])).
% 51.53/7.00  
% 51.53/7.00  fof(f106,plain,(
% 51.53/7.00    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f58])).
% 51.53/7.00  
% 51.53/7.00  fof(f9,axiom,(
% 51.53/7.00    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f84,plain,(
% 51.53/7.00    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 51.53/7.00    inference(cnf_transformation,[],[f9])).
% 51.53/7.00  
% 51.53/7.00  fof(f124,plain,(
% 51.53/7.00    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 51.53/7.00    inference(definition_unfolding,[],[f84,f108])).
% 51.53/7.00  
% 51.53/7.00  fof(f8,axiom,(
% 51.53/7.00    ! [X0] : (v1_relat_1(X0) => ((k2_relat_1(X0) = k1_xboole_0 | k1_relat_1(X0) = k1_xboole_0) => k1_xboole_0 = X0))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f37,plain,(
% 51.53/7.00    ! [X0] : ((k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0)) | ~v1_relat_1(X0))),
% 51.53/7.00    inference(ennf_transformation,[],[f8])).
% 51.53/7.00  
% 51.53/7.00  fof(f38,plain,(
% 51.53/7.00    ! [X0] : (k1_xboole_0 = X0 | (k2_relat_1(X0) != k1_xboole_0 & k1_relat_1(X0) != k1_xboole_0) | ~v1_relat_1(X0))),
% 51.53/7.00    inference(flattening,[],[f37])).
% 51.53/7.00  
% 51.53/7.00  fof(f82,plain,(
% 51.53/7.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f38])).
% 51.53/7.00  
% 51.53/7.00  fof(f27,axiom,(
% 51.53/7.00    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f65,plain,(
% 51.53/7.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 51.53/7.00    inference(ennf_transformation,[],[f27])).
% 51.53/7.00  
% 51.53/7.00  fof(f66,plain,(
% 51.53/7.00    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 51.53/7.00    inference(flattening,[],[f65])).
% 51.53/7.00  
% 51.53/7.00  fof(f113,plain,(
% 51.53/7.00    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f66])).
% 51.53/7.00  
% 51.53/7.00  fof(f18,axiom,(
% 51.53/7.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f52,plain,(
% 51.53/7.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.53/7.00    inference(ennf_transformation,[],[f18])).
% 51.53/7.00  
% 51.53/7.00  fof(f99,plain,(
% 51.53/7.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.53/7.00    inference(cnf_transformation,[],[f52])).
% 51.53/7.00  
% 51.53/7.00  fof(f98,plain,(
% 51.53/7.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.53/7.00    inference(cnf_transformation,[],[f51])).
% 51.53/7.00  
% 51.53/7.00  fof(f2,axiom,(
% 51.53/7.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f31,plain,(
% 51.53/7.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 51.53/7.00    inference(ennf_transformation,[],[f2])).
% 51.53/7.00  
% 51.53/7.00  fof(f69,plain,(
% 51.53/7.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 51.53/7.00    inference(nnf_transformation,[],[f31])).
% 51.53/7.00  
% 51.53/7.00  fof(f75,plain,(
% 51.53/7.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f69])).
% 51.53/7.00  
% 51.53/7.00  fof(f13,axiom,(
% 51.53/7.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f43,plain,(
% 51.53/7.00    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 51.53/7.00    inference(ennf_transformation,[],[f13])).
% 51.53/7.00  
% 51.53/7.00  fof(f44,plain,(
% 51.53/7.00    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 51.53/7.00    inference(flattening,[],[f43])).
% 51.53/7.00  
% 51.53/7.00  fof(f92,plain,(
% 51.53/7.00    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f44])).
% 51.53/7.00  
% 51.53/7.00  fof(f5,axiom,(
% 51.53/7.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f33,plain,(
% 51.53/7.00    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 51.53/7.00    inference(ennf_transformation,[],[f5])).
% 51.53/7.00  
% 51.53/7.00  fof(f79,plain,(
% 51.53/7.00    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f33])).
% 51.53/7.00  
% 51.53/7.00  fof(f6,axiom,(
% 51.53/7.00    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f34,plain,(
% 51.53/7.00    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 51.53/7.00    inference(ennf_transformation,[],[f6])).
% 51.53/7.00  
% 51.53/7.00  fof(f80,plain,(
% 51.53/7.00    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f34])).
% 51.53/7.00  
% 51.53/7.00  fof(f12,axiom,(
% 51.53/7.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f41,plain,(
% 51.53/7.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.53/7.00    inference(ennf_transformation,[],[f12])).
% 51.53/7.00  
% 51.53/7.00  fof(f42,plain,(
% 51.53/7.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.53/7.00    inference(flattening,[],[f41])).
% 51.53/7.00  
% 51.53/7.00  fof(f89,plain,(
% 51.53/7.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f42])).
% 51.53/7.00  
% 51.53/7.00  fof(f15,axiom,(
% 51.53/7.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f47,plain,(
% 51.53/7.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.53/7.00    inference(ennf_transformation,[],[f15])).
% 51.53/7.00  
% 51.53/7.00  fof(f48,plain,(
% 51.53/7.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.53/7.00    inference(flattening,[],[f47])).
% 51.53/7.00  
% 51.53/7.00  fof(f95,plain,(
% 51.53/7.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f48])).
% 51.53/7.00  
% 51.53/7.00  fof(f16,axiom,(
% 51.53/7.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)))))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f49,plain,(
% 51.53/7.00    ! [X0] : (! [X1] : ((k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.53/7.00    inference(ennf_transformation,[],[f16])).
% 51.53/7.00  
% 51.53/7.00  fof(f50,plain,(
% 51.53/7.00    ! [X0] : (! [X1] : (k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.53/7.00    inference(flattening,[],[f49])).
% 51.53/7.00  
% 51.53/7.00  fof(f96,plain,(
% 51.53/7.00    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f50])).
% 51.53/7.00  
% 51.53/7.00  fof(f83,plain,(
% 51.53/7.00    ( ! [X0] : (k1_xboole_0 = X0 | k2_relat_1(X0) != k1_xboole_0 | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f38])).
% 51.53/7.00  
% 51.53/7.00  fof(f14,axiom,(
% 51.53/7.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 51.53/7.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 51.53/7.00  
% 51.53/7.00  fof(f45,plain,(
% 51.53/7.00    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.53/7.00    inference(ennf_transformation,[],[f14])).
% 51.53/7.00  
% 51.53/7.00  fof(f46,plain,(
% 51.53/7.00    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.53/7.00    inference(flattening,[],[f45])).
% 51.53/7.00  
% 51.53/7.00  fof(f93,plain,(
% 51.53/7.00    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f46])).
% 51.53/7.00  
% 51.53/7.00  fof(f128,plain,(
% 51.53/7.00    ( ! [X0,X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(definition_unfolding,[],[f93,f108])).
% 51.53/7.00  
% 51.53/7.00  fof(f122,plain,(
% 51.53/7.00    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 51.53/7.00    inference(cnf_transformation,[],[f73])).
% 51.53/7.00  
% 51.53/7.00  fof(f90,plain,(
% 51.53/7.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f42])).
% 51.53/7.00  
% 51.53/7.00  fof(f94,plain,(
% 51.53/7.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.53/7.00    inference(cnf_transformation,[],[f48])).
% 51.53/7.00  
% 51.53/7.00  fof(f85,plain,(
% 51.53/7.00    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 51.53/7.00    inference(cnf_transformation,[],[f9])).
% 51.53/7.00  
% 51.53/7.00  fof(f123,plain,(
% 51.53/7.00    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 51.53/7.00    inference(definition_unfolding,[],[f85,f108])).
% 51.53/7.00  
% 51.53/7.00  fof(f102,plain,(
% 51.53/7.00    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.53/7.00    inference(cnf_transformation,[],[f70])).
% 51.53/7.00  
% 51.53/7.00  fof(f129,plain,(
% 51.53/7.00    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.53/7.00    inference(equality_resolution,[],[f102])).
% 51.53/7.00  
% 51.53/7.00  cnf(c_42,negated_conjecture,
% 51.53/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 51.53/7.00      inference(cnf_transformation,[],[f119]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1641,plain,
% 51.53/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_24,plain,
% 51.53/7.00      ( v4_relat_1(X0,X1)
% 51.53/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 51.53/7.00      inference(cnf_transformation,[],[f97]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7,plain,
% 51.53/7.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 51.53/7.00      inference(cnf_transformation,[],[f81]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_519,plain,
% 51.53/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | ~ v1_relat_1(X0)
% 51.53/7.00      | k7_relat_1(X0,X1) = X0 ),
% 51.53/7.00      inference(resolution,[status(thm)],[c_24,c_7]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1635,plain,
% 51.53/7.00      ( k7_relat_1(X0,X1) = X0
% 51.53/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2984,plain,
% 51.53/7.00      ( k7_relat_1(sK2,sK0) = sK2 | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_1635]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3,plain,
% 51.53/7.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 51.53/7.00      inference(cnf_transformation,[],[f77]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_158,plain,
% 51.53/7.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_160,plain,
% 51.53/7.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_158]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_0,plain,
% 51.53/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.53/7.00      | ~ v1_relat_1(X1)
% 51.53/7.00      | v1_relat_1(X0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f74]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1672,plain,
% 51.53/7.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 51.53/7.00      | v1_relat_1(X1) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3051,plain,
% 51.53/7.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) = iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_1672]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3266,plain,
% 51.53/7.00      ( k7_relat_1(sK2,sK0) = sK2 ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_2984,c_160,c_3051]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3386,plain,
% 51.53/7.00      ( v1_relat_1(sK2) = iProver_top ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_3051,c_160]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_4,plain,
% 51.53/7.00      ( ~ v1_relat_1(X0)
% 51.53/7.00      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 51.53/7.00      inference(cnf_transformation,[],[f78]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1670,plain,
% 51.53/7.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3390,plain,
% 51.53/7.00      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_3386,c_1670]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_4509,plain,
% 51.53/7.00      ( k9_relat_1(sK2,sK0) = k2_relat_1(sK2) ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_3266,c_3390]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_30,plain,
% 51.53/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f103]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1651,plain,
% 51.53/7.00      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3109,plain,
% 51.53/7.00      ( k7_relset_1(sK0,sK0,sK2,sK0) = k2_relset_1(sK0,sK0,sK2) ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_1651]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_26,plain,
% 51.53/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 51.53/7.00      inference(cnf_transformation,[],[f100]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1653,plain,
% 51.53/7.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3056,plain,
% 51.53/7.00      ( k7_relset_1(sK0,sK0,sK2,X0) = k9_relat_1(sK2,X0) ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_1653]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3112,plain,
% 51.53/7.00      ( k2_relset_1(sK0,sK0,sK2) = k9_relat_1(sK2,sK0) ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_3109,c_3056]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_4518,plain,
% 51.53/7.00      ( k2_relset_1(sK0,sK0,sK2) = k2_relat_1(sK2) ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_4509,c_3112]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_36,plain,
% 51.53/7.00      ( ~ v1_funct_2(X0,X1,X2)
% 51.53/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | ~ v1_funct_1(X0)
% 51.53/7.00      | ~ v2_funct_1(X0)
% 51.53/7.00      | k2_relset_1(X1,X2,X0) != X2
% 51.53/7.00      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 51.53/7.00      | k1_xboole_0 = X2 ),
% 51.53/7.00      inference(cnf_transformation,[],[f112]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1645,plain,
% 51.53/7.00      ( k2_relset_1(X0,X1,X2) != X1
% 51.53/7.00      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 51.53/7.00      | k1_xboole_0 = X1
% 51.53/7.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | v1_funct_1(X2) != iProver_top
% 51.53/7.00      | v2_funct_1(X2) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_15950,plain,
% 51.53/7.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK0)
% 51.53/7.00      | k2_relat_1(sK2) != sK0
% 51.53/7.00      | sK0 = k1_xboole_0
% 51.53/7.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 51.53/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v2_funct_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_4518,c_1645]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_44,negated_conjecture,
% 51.53/7.00      ( v1_funct_1(sK2) ),
% 51.53/7.00      inference(cnf_transformation,[],[f117]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_43,negated_conjecture,
% 51.53/7.00      ( v1_funct_2(sK2,sK0,sK0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f118]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_33,plain,
% 51.53/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 51.53/7.00      | ~ v1_funct_1(X0)
% 51.53/7.00      | ~ v1_funct_1(X3)
% 51.53/7.00      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f107]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1648,plain,
% 51.53/7.00      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 51.53/7.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 51.53/7.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | v1_funct_1(X5) != iProver_top
% 51.53/7.00      | v1_funct_1(X4) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7106,plain,
% 51.53/7.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | v1_funct_1(X2) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_1648]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_51,plain,
% 51.53/7.00      ( v1_funct_1(sK2) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7456,plain,
% 51.53/7.00      ( v1_funct_1(X2) != iProver_top
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2) ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_7106,c_51]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7457,plain,
% 51.53/7.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | v1_funct_1(X2) != iProver_top ),
% 51.53/7.00      inference(renaming,[status(thm)],[c_7456]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7462,plain,
% 51.53/7.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_7457]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7605,plain,
% 51.53/7.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_7462,c_51]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_35,plain,
% 51.53/7.00      ( ~ v1_funct_2(X0,X1,X2)
% 51.53/7.00      | ~ v1_funct_2(X3,X4,X1)
% 51.53/7.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 51.53/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | ~ v1_funct_1(X0)
% 51.53/7.00      | ~ v1_funct_1(X3)
% 51.53/7.00      | v2_funct_1(X3)
% 51.53/7.00      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 51.53/7.00      | k1_xboole_0 = X2 ),
% 51.53/7.00      inference(cnf_transformation,[],[f109]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1646,plain,
% 51.53/7.00      ( k1_xboole_0 = X0
% 51.53/7.00      | v1_funct_2(X1,X2,X0) != iProver_top
% 51.53/7.00      | v1_funct_2(X3,X4,X2) != iProver_top
% 51.53/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 51.53/7.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 51.53/7.00      | v1_funct_1(X1) != iProver_top
% 51.53/7.00      | v1_funct_1(X3) != iProver_top
% 51.53/7.00      | v2_funct_1(X3) = iProver_top
% 51.53/7.00      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7608,plain,
% 51.53/7.00      ( sK0 = k1_xboole_0
% 51.53/7.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 51.53/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v2_funct_1(k5_relat_1(sK2,sK2)) != iProver_top
% 51.53/7.00      | v2_funct_1(sK2) = iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_7605,c_1646]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_47,negated_conjecture,
% 51.53/7.00      ( v1_funct_1(sK1) ),
% 51.53/7.00      inference(cnf_transformation,[],[f114]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_48,plain,
% 51.53/7.00      ( v1_funct_1(sK1) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_46,negated_conjecture,
% 51.53/7.00      ( v1_funct_2(sK1,sK0,sK0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f115]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_49,plain,
% 51.53/7.00      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_45,negated_conjecture,
% 51.53/7.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 51.53/7.00      inference(cnf_transformation,[],[f116]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_50,plain,
% 51.53/7.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_52,plain,
% 51.53/7.00      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_53,plain,
% 51.53/7.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_40,negated_conjecture,
% 51.53/7.00      ( v2_funct_1(sK1) ),
% 51.53/7.00      inference(cnf_transformation,[],[f121]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_55,plain,
% 51.53/7.00      ( v2_funct_1(sK1) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_14,plain,
% 51.53/7.00      ( v1_relat_1(k6_partfun1(X0)) ),
% 51.53/7.00      inference(cnf_transformation,[],[f127]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_129,plain,
% 51.53/7.00      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_131,plain,
% 51.53/7.00      ( v1_relat_1(k6_partfun1(sK0)) = iProver_top ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_129]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_13,plain,
% 51.53/7.00      ( v2_funct_1(k6_partfun1(X0)) ),
% 51.53/7.00      inference(cnf_transformation,[],[f126]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_132,plain,
% 51.53/7.00      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_134,plain,
% 51.53/7.00      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_132]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_28,plain,
% 51.53/7.00      ( ~ r2_relset_1(X0,X1,X2,X3)
% 51.53/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.53/7.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.53/7.00      | X3 = X2 ),
% 51.53/7.00      inference(cnf_transformation,[],[f101]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_41,negated_conjecture,
% 51.53/7.00      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
% 51.53/7.00      inference(cnf_transformation,[],[f120]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_568,plain,
% 51.53/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | X3 = X0
% 51.53/7.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X0
% 51.53/7.00      | sK1 != X3
% 51.53/7.00      | sK0 != X2
% 51.53/7.00      | sK0 != X1 ),
% 51.53/7.00      inference(resolution_lifted,[status(thm)],[c_28,c_41]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_569,plain,
% 51.53/7.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 51.53/7.00      inference(unflattening,[status(thm)],[c_568]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_31,plain,
% 51.53/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 51.53/7.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 51.53/7.00      | ~ v1_funct_1(X0)
% 51.53/7.00      | ~ v1_funct_1(X3) ),
% 51.53/7.00      inference(cnf_transformation,[],[f106]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1725,plain,
% 51.53/7.00      ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | ~ v1_funct_1(sK1)
% 51.53/7.00      | ~ v1_funct_1(sK2) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_31]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_967,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1723,plain,
% 51.53/7.00      ( k6_partfun1(sK0) != X0 | sK2 != X0 | sK2 = k6_partfun1(sK0) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_967]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1798,plain,
% 51.53/7.00      ( k6_partfun1(sK0) != k1_xboole_0
% 51.53/7.00      | sK2 = k6_partfun1(sK0)
% 51.53/7.00      | sK2 != k1_xboole_0 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1723]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1959,plain,
% 51.53/7.00      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | ~ v1_funct_1(sK1)
% 51.53/7.00      | ~ v1_funct_1(sK2)
% 51.53/7.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_33]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1770,plain,
% 51.53/7.00      ( X0 != X1
% 51.53/7.00      | X0 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 51.53/7.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X1 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_967]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1850,plain,
% 51.53/7.00      ( X0 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 51.53/7.00      | X0 != k5_relat_1(sK2,sK1)
% 51.53/7.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k5_relat_1(sK2,sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1770]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2105,plain,
% 51.53/7.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 51.53/7.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k5_relat_1(sK2,sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1850]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_11,plain,
% 51.53/7.00      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 51.53/7.00      inference(cnf_transformation,[],[f124]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_9,plain,
% 51.53/7.00      ( ~ v1_relat_1(X0)
% 51.53/7.00      | k1_relat_1(X0) != k1_xboole_0
% 51.53/7.00      | k1_xboole_0 = X0 ),
% 51.53/7.00      inference(cnf_transformation,[],[f82]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1666,plain,
% 51.53/7.00      ( k1_relat_1(X0) != k1_xboole_0
% 51.53/7.00      | k1_xboole_0 = X0
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2534,plain,
% 51.53/7.00      ( k6_partfun1(X0) = k1_xboole_0
% 51.53/7.00      | k1_xboole_0 != X0
% 51.53/7.00      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_11,c_1666]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2536,plain,
% 51.53/7.00      ( k6_partfun1(sK0) = k1_xboole_0
% 51.53/7.00      | k1_xboole_0 != sK0
% 51.53/7.00      | v1_relat_1(k6_partfun1(sK0)) != iProver_top ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_2534]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1853,plain,
% 51.53/7.00      ( X0 != X1
% 51.53/7.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X1
% 51.53/7.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = X0 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_967]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1985,plain,
% 51.53/7.00      ( X0 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 51.53/7.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = X0
% 51.53/7.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1853]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2662,plain,
% 51.53/7.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 51.53/7.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = sK1
% 51.53/7.00      | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1985]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_979,plain,
% 51.53/7.00      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 51.53/7.00      theory(equality) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2269,plain,
% 51.53/7.00      ( ~ v2_funct_1(X0) | v2_funct_1(sK2) | sK2 != X0 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_979]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3433,plain,
% 51.53/7.00      ( ~ v2_funct_1(k6_partfun1(X0))
% 51.53/7.00      | v2_funct_1(sK2)
% 51.53/7.00      | sK2 != k6_partfun1(X0) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_2269]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3434,plain,
% 51.53/7.00      ( sK2 != k6_partfun1(X0)
% 51.53/7.00      | v2_funct_1(k6_partfun1(X0)) != iProver_top
% 51.53/7.00      | v2_funct_1(sK2) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_3433]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3436,plain,
% 51.53/7.00      ( sK2 != k6_partfun1(sK0)
% 51.53/7.00      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 51.53/7.00      | v2_funct_1(sK2) = iProver_top ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_3434]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2279,plain,
% 51.53/7.00      ( ~ v1_funct_2(X0,X1,X2)
% 51.53/7.00      | ~ v1_funct_2(sK2,X3,X1)
% 51.53/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 51.53/7.00      | ~ v1_funct_1(X0)
% 51.53/7.00      | ~ v1_funct_1(sK2)
% 51.53/7.00      | ~ v2_funct_1(k1_partfun1(X3,X1,X1,X2,sK2,X0))
% 51.53/7.00      | v2_funct_1(sK2)
% 51.53/7.00      | k1_xboole_0 = X2 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_35]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3724,plain,
% 51.53/7.00      ( ~ v1_funct_2(sK1,X0,X1)
% 51.53/7.00      | ~ v1_funct_2(sK2,X2,X0)
% 51.53/7.00      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.53/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
% 51.53/7.00      | ~ v1_funct_1(sK1)
% 51.53/7.00      | ~ v1_funct_1(sK2)
% 51.53/7.00      | ~ v2_funct_1(k1_partfun1(X2,X0,X0,X1,sK2,sK1))
% 51.53/7.00      | v2_funct_1(sK2)
% 51.53/7.00      | k1_xboole_0 = X1 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_2279]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3725,plain,
% 51.53/7.00      ( k1_xboole_0 = X0
% 51.53/7.00      | v1_funct_2(sK1,X1,X0) != iProver_top
% 51.53/7.00      | v1_funct_2(sK2,X2,X1) != iProver_top
% 51.53/7.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 51.53/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 51.53/7.00      | v1_funct_1(sK1) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v2_funct_1(k1_partfun1(X2,X1,X1,X0,sK2,sK1)) != iProver_top
% 51.53/7.00      | v2_funct_1(sK2) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_3724]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3727,plain,
% 51.53/7.00      ( k1_xboole_0 = sK0
% 51.53/7.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 51.53/7.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 51.53/7.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.53/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.53/7.00      | v1_funct_1(sK1) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) != iProver_top
% 51.53/7.00      | v2_funct_1(sK2) = iProver_top ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_3725]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_571,plain,
% 51.53/7.00      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_569,c_45]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1632,plain,
% 51.53/7.00      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 51.53/7.00      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_571]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2102,plain,
% 51.53/7.00      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_1632,c_47,c_45,c_44,c_42,c_569,c_1725]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_6966,plain,
% 51.53/7.00      ( sK0 = k1_xboole_0
% 51.53/7.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 51.53/7.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 51.53/7.00      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.53/7.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 51.53/7.00      | v1_funct_1(sK1) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v2_funct_1(sK1) != iProver_top
% 51.53/7.00      | v2_funct_1(sK2) = iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_2102,c_1646]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_5115,plain,
% 51.53/7.00      ( v2_funct_1(X0) | ~ v2_funct_1(sK1) | X0 != sK1 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_979]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_9871,plain,
% 51.53/7.00      ( v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1))
% 51.53/7.00      | ~ v2_funct_1(sK1)
% 51.53/7.00      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK1 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_5115]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_9872,plain,
% 51.53/7.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK1
% 51.53/7.00      | v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) = iProver_top
% 51.53/7.00      | v2_funct_1(sK1) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_9871]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_38,plain,
% 51.53/7.00      ( ~ v1_funct_2(X0,X1,X1)
% 51.53/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 51.53/7.00      | ~ v1_funct_1(X0)
% 51.53/7.00      | k1_relset_1(X1,X1,X0) = X1 ),
% 51.53/7.00      inference(cnf_transformation,[],[f113]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1643,plain,
% 51.53/7.00      ( k1_relset_1(X0,X0,X1) = X0
% 51.53/7.00      | v1_funct_2(X1,X0,X0) != iProver_top
% 51.53/7.00      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 51.53/7.00      | v1_funct_1(X1) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3806,plain,
% 51.53/7.00      ( k1_relset_1(sK0,sK0,sK2) = sK0
% 51.53/7.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_1643]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_25,plain,
% 51.53/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f99]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1654,plain,
% 51.53/7.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2613,plain,
% 51.53/7.00      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_1654]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3809,plain,
% 51.53/7.00      ( k1_relat_1(sK2) = sK0
% 51.53/7.00      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_3806,c_2613]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_11190,plain,
% 51.53/7.00      ( k1_relat_1(sK2) = sK0 ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_3809,c_51,c_52]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_11198,plain,
% 51.53/7.00      ( sK2 = k1_xboole_0
% 51.53/7.00      | sK0 != k1_xboole_0
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_11190,c_1666]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_15627,plain,
% 51.53/7.00      ( v2_funct_1(sK2) = iProver_top ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_7608,c_47,c_48,c_49,c_45,c_50,c_44,c_51,c_52,c_42,
% 51.53/7.00                 c_53,c_55,c_131,c_134,c_160,c_569,c_1725,c_1798,c_1959,
% 51.53/7.00                 c_2105,c_2536,c_2662,c_3051,c_3436,c_3727,c_6966,c_9872,
% 51.53/7.00                 c_11198]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_15629,plain,
% 51.53/7.00      ( v2_funct_1(sK2) ),
% 51.53/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_15627]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_15952,plain,
% 51.53/7.00      ( ~ v1_funct_2(sK2,sK0,sK0)
% 51.53/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | ~ v1_funct_1(sK2)
% 51.53/7.00      | ~ v2_funct_1(sK2)
% 51.53/7.00      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK0)
% 51.53/7.00      | k2_relat_1(sK2) != sK0
% 51.53/7.00      | sK0 = k1_xboole_0 ),
% 51.53/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_15950]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_23,plain,
% 51.53/7.00      ( v5_relat_1(X0,X1)
% 51.53/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 51.53/7.00      inference(cnf_transformation,[],[f98]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2,plain,
% 51.53/7.00      ( r1_tarski(k2_relat_1(X0),X1)
% 51.53/7.00      | ~ v5_relat_1(X0,X1)
% 51.53/7.00      | ~ v1_relat_1(X0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f75]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_537,plain,
% 51.53/7.00      ( r1_tarski(k2_relat_1(X0),X1)
% 51.53/7.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 51.53/7.00      | ~ v1_relat_1(X0) ),
% 51.53/7.00      inference(resolution,[status(thm)],[c_23,c_2]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1634,plain,
% 51.53/7.00      ( r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 51.53/7.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2471,plain,
% 51.53/7.00      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_1634]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1638,plain,
% 51.53/7.00      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3807,plain,
% 51.53/7.00      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 51.53/7.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 51.53/7.00      | v1_funct_1(sK1) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1638,c_1643]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2614,plain,
% 51.53/7.00      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1638,c_1654]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3808,plain,
% 51.53/7.00      ( k1_relat_1(sK1) = sK0
% 51.53/7.00      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 51.53/7.00      | v1_funct_1(sK1) != iProver_top ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_3807,c_2614]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8067,plain,
% 51.53/7.00      ( k1_relat_1(sK1) = sK0 ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_3808,c_48,c_49]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_18,plain,
% 51.53/7.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 51.53/7.00      | ~ v1_funct_1(X1)
% 51.53/7.00      | ~ v2_funct_1(X1)
% 51.53/7.00      | ~ v1_relat_1(X1)
% 51.53/7.00      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 51.53/7.00      inference(cnf_transformation,[],[f92]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1659,plain,
% 51.53/7.00      ( k10_relat_1(X0,k9_relat_1(X0,X1)) = X1
% 51.53/7.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v2_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8074,plain,
% 51.53/7.00      ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
% 51.53/7.00      | r1_tarski(X0,sK0) != iProver_top
% 51.53/7.00      | v1_funct_1(sK1) != iProver_top
% 51.53/7.00      | v2_funct_1(sK1) != iProver_top
% 51.53/7.00      | v1_relat_1(sK1) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_8067,c_1659]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3052,plain,
% 51.53/7.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 51.53/7.00      | v1_relat_1(sK1) = iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1638,c_1672]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_28391,plain,
% 51.53/7.00      ( r1_tarski(X0,sK0) != iProver_top
% 51.53/7.00      | k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0 ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_8074,c_48,c_55,c_160,c_3052]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_28392,plain,
% 51.53/7.00      ( k10_relat_1(sK1,k9_relat_1(sK1,X0)) = X0
% 51.53/7.00      | r1_tarski(X0,sK0) != iProver_top ),
% 51.53/7.00      inference(renaming,[status(thm)],[c_28391]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_28397,plain,
% 51.53/7.00      ( k10_relat_1(sK1,k9_relat_1(sK1,k2_relat_1(sK2))) = k2_relat_1(sK2)
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_2471,c_28392]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7107,plain,
% 51.53/7.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | v1_funct_1(X2) != iProver_top
% 51.53/7.00      | v1_funct_1(sK1) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1638,c_1648]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7983,plain,
% 51.53/7.00      ( v1_funct_1(X2) != iProver_top
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_7107,c_48]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7984,plain,
% 51.53/7.00      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | v1_funct_1(X2) != iProver_top ),
% 51.53/7.00      inference(renaming,[status(thm)],[c_7983]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7989,plain,
% 51.53/7.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_7984]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_7991,plain,
% 51.53/7.00      ( k5_relat_1(sK2,sK1) = sK1 | v1_funct_1(sK2) != iProver_top ),
% 51.53/7.00      inference(light_normalisation,[status(thm)],[c_7989,c_2102]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2119,plain,
% 51.53/7.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k5_relat_1(sK2,sK1)
% 51.53/7.00      | k5_relat_1(sK2,sK1) = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 51.53/7.00      | k5_relat_1(sK2,sK1) != k5_relat_1(sK2,sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1850]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_966,plain,( X0 = X0 ),theory(equality) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2507,plain,
% 51.53/7.00      ( k5_relat_1(sK2,sK1) = k5_relat_1(sK2,sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_966]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1896,plain,
% 51.53/7.00      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_967]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3078,plain,
% 51.53/7.00      ( X0 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 51.53/7.00      | X0 = sK1
% 51.53/7.00      | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1896]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_4818,plain,
% 51.53/7.00      ( k5_relat_1(sK2,sK1) != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 51.53/7.00      | k5_relat_1(sK2,sK1) = sK1
% 51.53/7.00      | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_3078]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8061,plain,
% 51.53/7.00      ( k5_relat_1(sK2,sK1) = sK1 ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_7991,c_47,c_45,c_44,c_42,c_569,c_1725,c_1959,c_2119,
% 51.53/7.00                 c_2507,c_4818]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3594,plain,
% 51.53/7.00      ( v1_relat_1(sK1) = iProver_top ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_3052,c_160]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_5,plain,
% 51.53/7.00      ( ~ v1_relat_1(X0)
% 51.53/7.00      | ~ v1_relat_1(X1)
% 51.53/7.00      | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 51.53/7.00      inference(cnf_transformation,[],[f79]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1669,plain,
% 51.53/7.00      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 51.53/7.00      | v1_relat_1(X1) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_4141,plain,
% 51.53/7.00      ( k9_relat_1(sK1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK1))
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_3594,c_1669]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_5670,plain,
% 51.53/7.00      ( k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_3386,c_4141]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8063,plain,
% 51.53/7.00      ( k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(sK1) ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_8061,c_5670]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_6,plain,
% 51.53/7.00      ( ~ v1_relat_1(X0)
% 51.53/7.00      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f80]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1668,plain,
% 51.53/7.00      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3599,plain,
% 51.53/7.00      ( k10_relat_1(sK1,k2_relat_1(sK1)) = k1_relat_1(sK1) ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_3594,c_1668]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8072,plain,
% 51.53/7.00      ( k10_relat_1(sK1,k2_relat_1(sK1)) = sK0 ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_8067,c_3599]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_28406,plain,
% 51.53/7.00      ( k2_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(light_normalisation,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_28397,c_8063,c_8072]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1650,plain,
% 51.53/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 51.53/7.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 51.53/7.00      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_funct_1(X3) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8895,plain,
% 51.53/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 51.53/7.00      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_funct_1(X3) != iProver_top
% 51.53/7.00      | v1_relat_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top
% 51.53/7.00      | v1_relat_1(k2_zfmisc_1(X4,X2)) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1650,c_1672]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1639,plain,
% 51.53/7.00      ( v1_funct_1(sK2) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_17,plain,
% 51.53/7.00      ( ~ v1_funct_1(X0)
% 51.53/7.00      | ~ v2_funct_1(X0)
% 51.53/7.00      | ~ v1_relat_1(X0)
% 51.53/7.00      | v1_relat_1(k2_funct_1(X0)) ),
% 51.53/7.00      inference(cnf_transformation,[],[f89]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1660,plain,
% 51.53/7.00      ( v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v2_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_4745,plain,
% 51.53/7.00      ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v2_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(X1) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1660,c_1669]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_17502,plain,
% 51.53/7.00      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2)))
% 51.53/7.00      | v2_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1639,c_4745]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_17600,plain,
% 51.53/7.00      ( v1_relat_1(X0) != iProver_top
% 51.53/7.00      | k9_relat_1(k2_funct_1(sK2),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2))) ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_17502,c_47,c_48,c_49,c_45,c_50,c_44,c_51,c_52,c_42,
% 51.53/7.00                 c_53,c_55,c_131,c_134,c_160,c_569,c_1725,c_1798,c_1959,
% 51.53/7.00                 c_2105,c_2536,c_2662,c_3051,c_3436,c_3727,c_6966,c_9872,
% 51.53/7.00                 c_11198]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_17601,plain,
% 51.53/7.00      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK2)))
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(renaming,[status(thm)],[c_17600]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_28993,plain,
% 51.53/7.00      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) = k2_relat_1(k5_relat_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k2_funct_1(sK2)))
% 51.53/7.00      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 51.53/7.00      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | v1_funct_1(X5) != iProver_top
% 51.53/7.00      | v1_funct_1(X4) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_zfmisc_1(X0,X3)) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_8895,c_17601]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_29281,plain,
% 51.53/7.00      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2))) = k2_relat_1(k5_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2),k2_funct_1(sK2)))
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | v1_funct_1(X2) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_28993]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_29362,plain,
% 51.53/7.00      ( v1_funct_1(X2) != iProver_top
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | k9_relat_1(k2_funct_1(sK2),k2_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2))) = k2_relat_1(k5_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2),k2_funct_1(sK2)))
% 51.53/7.00      | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_29281,c_51]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_29363,plain,
% 51.53/7.00      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2))) = k2_relat_1(k5_relat_1(k1_partfun1(X0,X1,sK0,sK0,X2,sK2),k2_funct_1(sK2)))
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.53/7.00      | v1_funct_1(X2) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_zfmisc_1(X0,sK0)) != iProver_top ),
% 51.53/7.00      inference(renaming,[status(thm)],[c_29362]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_29369,plain,
% 51.53/7.00      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2))) = k2_relat_1(k5_relat_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2),k2_funct_1(sK2)))
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1641,c_29363]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1636,plain,
% 51.53/7.00      ( v1_funct_1(sK1) = iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_17608,plain,
% 51.53/7.00      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k2_funct_1(X0))) = k2_relat_1(k5_relat_1(k2_funct_1(X0),k2_funct_1(sK2)))
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v2_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1660,c_17601]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_20150,plain,
% 51.53/7.00      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(k2_funct_1(sK1))) = k2_relat_1(k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)))
% 51.53/7.00      | v2_funct_1(sK1) != iProver_top
% 51.53/7.00      | v1_relat_1(sK1) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1636,c_17608]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_20,plain,
% 51.53/7.00      ( ~ v1_funct_1(X0)
% 51.53/7.00      | ~ v2_funct_1(X0)
% 51.53/7.00      | ~ v1_relat_1(X0)
% 51.53/7.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f95]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1657,plain,
% 51.53/7.00      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v2_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_6158,plain,
% 51.53/7.00      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
% 51.53/7.00      | v2_funct_1(sK1) != iProver_top
% 51.53/7.00      | v1_relat_1(sK1) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1636,c_1657]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_6338,plain,
% 51.53/7.00      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_6158,c_55,c_160,c_3052]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8070,plain,
% 51.53/7.00      ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_8067,c_6338]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_22,plain,
% 51.53/7.00      ( ~ v1_funct_1(X0)
% 51.53/7.00      | ~ v1_funct_1(X1)
% 51.53/7.00      | ~ v2_funct_1(X0)
% 51.53/7.00      | ~ v2_funct_1(X1)
% 51.53/7.00      | ~ v1_relat_1(X0)
% 51.53/7.00      | ~ v1_relat_1(X1)
% 51.53/7.00      | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
% 51.53/7.00      inference(cnf_transformation,[],[f96]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1655,plain,
% 51.53/7.00      ( k5_relat_1(k2_funct_1(X0),k2_funct_1(X1)) = k2_funct_1(k5_relat_1(X1,X0))
% 51.53/7.00      | v1_funct_1(X1) != iProver_top
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v2_funct_1(X1) != iProver_top
% 51.53/7.00      | v2_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(X1) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8946,plain,
% 51.53/7.00      ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v2_funct_1(X0) != iProver_top
% 51.53/7.00      | v2_funct_1(sK1) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(sK1) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1636,c_1655]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_10542,plain,
% 51.53/7.00      ( v1_relat_1(X0) != iProver_top
% 51.53/7.00      | k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v2_funct_1(X0) != iProver_top ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_8946,c_55,c_160,c_3052]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_10543,plain,
% 51.53/7.00      ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v2_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(renaming,[status(thm)],[c_10542]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_10550,plain,
% 51.53/7.00      ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,sK1))
% 51.53/7.00      | v2_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1639,c_10543]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_10552,plain,
% 51.53/7.00      ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK1)
% 51.53/7.00      | v2_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(light_normalisation,[status(thm)],[c_10550,c_8061]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_11749,plain,
% 51.53/7.00      ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK1) ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_10552,c_47,c_48,c_49,c_45,c_50,c_44,c_51,c_52,c_42,
% 51.53/7.00                 c_53,c_55,c_131,c_134,c_160,c_569,c_1725,c_1798,c_1959,
% 51.53/7.00                 c_2105,c_2536,c_2662,c_3051,c_3436,c_3727,c_6966,c_9872,
% 51.53/7.00                 c_11198]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_20154,plain,
% 51.53/7.00      ( k9_relat_1(k2_funct_1(sK2),sK0) = sK0
% 51.53/7.00      | v2_funct_1(sK1) != iProver_top
% 51.53/7.00      | v1_relat_1(sK1) != iProver_top ),
% 51.53/7.00      inference(light_normalisation,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_20150,c_8070,c_11749]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_20168,plain,
% 51.53/7.00      ( k9_relat_1(k2_funct_1(sK2),sK0) = sK0 ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_20154,c_55,c_160,c_3052]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_28476,plain,
% 51.53/7.00      ( k2_relat_1(sK2) = sK0 ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_28406,c_160,c_3051]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_4140,plain,
% 51.53/7.00      ( k9_relat_1(sK2,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK2))
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_3386,c_1669]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_5580,plain,
% 51.53/7.00      ( k9_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,sK2)) ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_3386,c_4140]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_28518,plain,
% 51.53/7.00      ( k2_relat_1(k5_relat_1(sK2,sK2)) = k9_relat_1(sK2,sK0) ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_28476,c_5580]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_28519,plain,
% 51.53/7.00      ( k9_relat_1(sK2,sK0) = sK0 ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_28476,c_4509]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_28521,plain,
% 51.53/7.00      ( k2_relat_1(k5_relat_1(sK2,sK2)) = sK0 ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_28518,c_28519]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_29378,plain,
% 51.53/7.00      ( k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k2_funct_1(sK2))) = sK0
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top ),
% 51.53/7.00      inference(light_normalisation,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_29369,c_7605,c_20168,c_28521]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_29447,plain,
% 51.53/7.00      ( k2_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k2_funct_1(sK2))) = sK0 ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_29378,c_51,c_160]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8,plain,
% 51.53/7.00      ( ~ v1_relat_1(X0)
% 51.53/7.00      | k2_relat_1(X0) != k1_xboole_0
% 51.53/7.00      | k1_xboole_0 = X0 ),
% 51.53/7.00      inference(cnf_transformation,[],[f83]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1667,plain,
% 51.53/7.00      ( k2_relat_1(X0) != k1_xboole_0
% 51.53/7.00      | k1_xboole_0 = X0
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_29452,plain,
% 51.53/7.00      ( k5_relat_1(k5_relat_1(sK2,sK2),k2_funct_1(sK2)) = k1_xboole_0
% 51.53/7.00      | sK0 != k1_xboole_0
% 51.53/7.00      | v1_relat_1(k5_relat_1(k5_relat_1(sK2,sK2),k2_funct_1(sK2))) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_29447,c_1667]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1741,plain,
% 51.53/7.00      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_967]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1751,plain,
% 51.53/7.00      ( X0 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 51.53/7.00      | sK1 = X0
% 51.53/7.00      | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1741]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1756,plain,
% 51.53/7.00      ( sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) | sK1 = sK1 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1751]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8075,plain,
% 51.53/7.00      ( sK1 = k1_xboole_0
% 51.53/7.00      | sK0 != k1_xboole_0
% 51.53/7.00      | v1_relat_1(sK1) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_8067,c_1666]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1738,plain,
% 51.53/7.00      ( X0 != X1 | sK2 != X1 | sK2 = X0 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_967]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1799,plain,
% 51.53/7.00      ( X0 != k1_xboole_0 | sK2 = X0 | sK2 != k1_xboole_0 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1738]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_16328,plain,
% 51.53/7.00      ( sK1 != k1_xboole_0 | sK2 = sK1 | sK2 != k1_xboole_0 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1799]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1753,plain,
% 51.53/7.00      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1741]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_24978,plain,
% 51.53/7.00      ( sK1 != sK1 | sK1 = sK2 | sK2 != sK1 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1753]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_19,plain,
% 51.53/7.00      ( ~ v1_funct_1(X0)
% 51.53/7.00      | ~ v1_funct_1(X1)
% 51.53/7.00      | ~ v1_relat_1(X0)
% 51.53/7.00      | ~ v1_relat_1(X1)
% 51.53/7.00      | k5_relat_1(X0,X1) != X0
% 51.53/7.00      | k6_partfun1(k1_relat_1(X1)) = X1
% 51.53/7.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f128]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1658,plain,
% 51.53/7.00      ( k5_relat_1(X0,X1) != X0
% 51.53/7.00      | k6_partfun1(k1_relat_1(X1)) = X1
% 51.53/7.00      | k1_relat_1(X1) != k2_relat_1(X0)
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_funct_1(X1) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(X1) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8064,plain,
% 51.53/7.00      ( k6_partfun1(k1_relat_1(sK1)) = sK1
% 51.53/7.00      | k1_relat_1(sK1) != k2_relat_1(sK2)
% 51.53/7.00      | sK1 != sK2
% 51.53/7.00      | v1_funct_1(sK1) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(sK1) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_8061,c_1658]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_159,plain,
% 51.53/7.00      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_3]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3053,plain,
% 51.53/7.00      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK2) ),
% 51.53/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_3051]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_3054,plain,
% 51.53/7.00      ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK0)) | v1_relat_1(sK1) ),
% 51.53/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_3052]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_8065,plain,
% 51.53/7.00      ( ~ v1_funct_1(sK1)
% 51.53/7.00      | ~ v1_funct_1(sK2)
% 51.53/7.00      | ~ v1_relat_1(sK1)
% 51.53/7.00      | ~ v1_relat_1(sK2)
% 51.53/7.00      | k6_partfun1(k1_relat_1(sK1)) = sK1
% 51.53/7.00      | k1_relat_1(sK1) != k2_relat_1(sK2)
% 51.53/7.00      | sK1 != sK2 ),
% 51.53/7.00      inference(predicate_to_equality_rev,[status(thm)],[c_8064]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_27517,plain,
% 51.53/7.00      ( k6_partfun1(k1_relat_1(sK1)) = sK1
% 51.53/7.00      | k1_relat_1(sK1) != k2_relat_1(sK2)
% 51.53/7.00      | sK1 != sK2 ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_8064,c_47,c_44,c_159,c_3053,c_3054,c_8065]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_27519,plain,
% 51.53/7.00      ( k6_partfun1(sK0) = sK1 | k2_relat_1(sK2) != sK0 | sK1 != sK2 ),
% 51.53/7.00      inference(light_normalisation,[status(thm)],[c_27517,c_8067]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_39,negated_conjecture,
% 51.53/7.00      ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
% 51.53/7.00      inference(cnf_transformation,[],[f122]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_582,plain,
% 51.53/7.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK2
% 51.53/7.00      | k6_partfun1(sK0) != sK1
% 51.53/7.00      | sK0 != sK0 ),
% 51.53/7.00      inference(resolution_lifted,[status(thm)],[c_39,c_41]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_689,plain,
% 51.53/7.00      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK2
% 51.53/7.00      | k6_partfun1(sK0) != sK1 ),
% 51.53/7.00      inference(equality_resolution_simp,[status(thm)],[c_582]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2104,plain,
% 51.53/7.00      ( k6_partfun1(sK0) != sK1 | sK1 != sK2 ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_2102,c_689]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_27520,plain,
% 51.53/7.00      ( k2_relat_1(sK2) != sK0 | sK1 != sK2 ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_27519,c_2104]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_29661,plain,
% 51.53/7.00      ( sK0 != k1_xboole_0 ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_29452,c_47,c_45,c_44,c_42,c_160,c_569,c_1725,c_1756,
% 51.53/7.00                 c_2104,c_3051,c_3052,c_8075,c_11198,c_16328,c_24978,
% 51.53/7.00                 c_27519,c_28406]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_173435,plain,
% 51.53/7.00      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK0) ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_15950,c_47,c_45,c_44,c_43,c_42,c_160,c_569,c_1725,
% 51.53/7.00                 c_1756,c_2104,c_3051,c_3052,c_8075,c_11198,c_15629,
% 51.53/7.00                 c_15952,c_16328,c_24978,c_27519,c_28406]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_11751,plain,
% 51.53/7.00      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2)
% 51.53/7.00      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1))
% 51.53/7.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 51.53/7.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_funct_1(sK1)) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_11749,c_1658]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_11752,plain,
% 51.53/7.00      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2)
% 51.53/7.00      | k1_relat_1(k2_funct_1(sK2)) != sK0
% 51.53/7.00      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 51.53/7.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_funct_1(sK1)) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 51.53/7.00      inference(light_normalisation,[status(thm)],[c_11751,c_8070]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_16,plain,
% 51.53/7.00      ( ~ v1_funct_1(X0)
% 51.53/7.00      | v1_funct_1(k2_funct_1(X0))
% 51.53/7.00      | ~ v2_funct_1(X0)
% 51.53/7.00      | ~ v1_relat_1(X0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f90]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2644,plain,
% 51.53/7.00      ( v1_funct_1(k2_funct_1(sK2))
% 51.53/7.00      | ~ v1_funct_1(sK2)
% 51.53/7.00      | ~ v2_funct_1(sK2)
% 51.53/7.00      | ~ v1_relat_1(sK2) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_16]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2645,plain,
% 51.53/7.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v2_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_2644]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2647,plain,
% 51.53/7.00      ( v1_funct_1(k2_funct_1(sK1))
% 51.53/7.00      | ~ v1_funct_1(sK1)
% 51.53/7.00      | ~ v2_funct_1(sK1)
% 51.53/7.00      | ~ v1_relat_1(sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_16]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_2648,plain,
% 51.53/7.00      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top
% 51.53/7.00      | v1_funct_1(sK1) != iProver_top
% 51.53/7.00      | v2_funct_1(sK1) != iProver_top
% 51.53/7.00      | v1_relat_1(sK1) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_2647]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_5130,plain,
% 51.53/7.00      ( ~ v1_funct_1(sK2)
% 51.53/7.00      | ~ v2_funct_1(sK2)
% 51.53/7.00      | v1_relat_1(k2_funct_1(sK2))
% 51.53/7.00      | ~ v1_relat_1(sK2) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_17]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_5131,plain,
% 51.53/7.00      ( v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v2_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_5130]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_5133,plain,
% 51.53/7.00      ( ~ v1_funct_1(sK1)
% 51.53/7.00      | ~ v2_funct_1(sK1)
% 51.53/7.00      | v1_relat_1(k2_funct_1(sK1))
% 51.53/7.00      | ~ v1_relat_1(sK1) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_17]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_5134,plain,
% 51.53/7.00      ( v1_funct_1(sK1) != iProver_top
% 51.53/7.00      | v2_funct_1(sK1) != iProver_top
% 51.53/7.00      | v1_relat_1(k2_funct_1(sK1)) = iProver_top
% 51.53/7.00      | v1_relat_1(sK1) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_5133]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_21,plain,
% 51.53/7.00      ( ~ v1_funct_1(X0)
% 51.53/7.00      | ~ v2_funct_1(X0)
% 51.53/7.00      | ~ v1_relat_1(X0)
% 51.53/7.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 51.53/7.00      inference(cnf_transformation,[],[f94]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1656,plain,
% 51.53/7.00      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 51.53/7.00      | v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v2_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_5262,plain,
% 51.53/7.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 51.53/7.00      | v2_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_1639,c_1656]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_5270,plain,
% 51.53/7.00      ( v2_funct_1(sK2) != iProver_top
% 51.53/7.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_5262,c_160,c_3051]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_5271,plain,
% 51.53/7.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 51.53/7.00      | v2_funct_1(sK2) != iProver_top ),
% 51.53/7.00      inference(renaming,[status(thm)],[c_5270]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_15632,plain,
% 51.53/7.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_15627,c_5271]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_28514,plain,
% 51.53/7.00      ( k1_relat_1(k2_funct_1(sK2)) = sK0 ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_28476,c_15632]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_51055,plain,
% 51.53/7.00      ( k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2) ),
% 51.53/7.00      inference(global_propositional_subsumption,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_11752,c_47,c_48,c_49,c_45,c_50,c_44,c_51,c_52,c_42,
% 51.53/7.00                 c_53,c_55,c_131,c_134,c_160,c_569,c_1725,c_1798,c_1959,
% 51.53/7.00                 c_2105,c_2536,c_2645,c_2648,c_2662,c_3051,c_3052,c_3436,
% 51.53/7.00                 c_3727,c_5131,c_5134,c_6966,c_9872,c_11198,c_28514]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_51057,plain,
% 51.53/7.00      ( k2_funct_1(sK2) = k6_partfun1(sK0) ),
% 51.53/7.00      inference(light_normalisation,[status(thm)],[c_51055,c_28514]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_173437,plain,
% 51.53/7.00      ( k5_relat_1(k6_partfun1(sK0),sK2) = k6_partfun1(sK0) ),
% 51.53/7.00      inference(light_normalisation,[status(thm)],[c_173435,c_51057]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_173438,plain,
% 51.53/7.00      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 51.53/7.00      | k2_relat_1(k6_partfun1(sK0)) != k1_relat_1(sK2)
% 51.53/7.00      | v1_funct_1(k6_partfun1(sK0)) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(k6_partfun1(sK0)) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_173437,c_1658]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_173441,plain,
% 51.53/7.00      ( k6_partfun1(sK0) = sK2
% 51.53/7.00      | k2_relat_1(k6_partfun1(sK0)) != sK0
% 51.53/7.00      | v1_funct_1(k6_partfun1(sK0)) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(k6_partfun1(sK0)) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(light_normalisation,[status(thm)],[c_173438,c_11190]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_10,plain,
% 51.53/7.00      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 51.53/7.00      inference(cnf_transformation,[],[f123]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_173442,plain,
% 51.53/7.00      ( k6_partfun1(sK0) = sK2
% 51.53/7.00      | sK0 != sK0
% 51.53/7.00      | v1_funct_1(k6_partfun1(sK0)) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(k6_partfun1(sK0)) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(demodulation,[status(thm)],[c_173441,c_10]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_173443,plain,
% 51.53/7.00      ( k6_partfun1(sK0) = sK2
% 51.53/7.00      | v1_funct_1(k6_partfun1(sK0)) != iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(k6_partfun1(sK0)) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(equality_resolution_simp,[status(thm)],[c_173442]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_970,plain,
% 51.53/7.00      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 51.53/7.00      theory(equality) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_57140,plain,
% 51.53/7.00      ( ~ m1_subset_1(X0,X1)
% 51.53/7.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 51.53/7.00      | X2 != X0
% 51.53/7.00      | k1_zfmisc_1(k2_zfmisc_1(X3,X4)) != X1 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_970]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_60075,plain,
% 51.53/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | X0 != sK2
% 51.53/7.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_57140]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_61006,plain,
% 51.53/7.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | X0 != sK2
% 51.53/7.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_60075]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_65065,plain,
% 51.53/7.00      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | k6_partfun1(sK0) != sK2
% 51.53/7.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_61006]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_969,plain,
% 51.53/7.00      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 51.53/7.00      theory(equality) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_61012,plain,
% 51.53/7.00      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK0,sK0)
% 51.53/7.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_969]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_61014,plain,
% 51.53/7.00      ( k2_zfmisc_1(sK0,sK0) != k2_zfmisc_1(sK0,sK0)
% 51.53/7.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)) ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_61012]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1661,plain,
% 51.53/7.00      ( v1_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 51.53/7.00      | v2_funct_1(X0) != iProver_top
% 51.53/7.00      | v1_relat_1(X0) != iProver_top ),
% 51.53/7.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_51206,plain,
% 51.53/7.00      ( v1_funct_1(k6_partfun1(sK0)) = iProver_top
% 51.53/7.00      | v1_funct_1(sK2) != iProver_top
% 51.53/7.00      | v2_funct_1(sK2) != iProver_top
% 51.53/7.00      | v1_relat_1(sK2) != iProver_top ),
% 51.53/7.00      inference(superposition,[status(thm)],[c_51057,c_1661]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1744,plain,
% 51.53/7.00      ( sK2 = sK2 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_966]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1737,plain,
% 51.53/7.00      ( k6_partfun1(sK0) != sK2 | sK2 = k6_partfun1(sK0) | sK2 != sK2 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_1723]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_1001,plain,
% 51.53/7.00      ( sK0 = sK0 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_966]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_973,plain,
% 51.53/7.00      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 51.53/7.00      theory(equality) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_989,plain,
% 51.53/7.00      ( k2_zfmisc_1(sK0,sK0) = k2_zfmisc_1(sK0,sK0) | sK0 != sK0 ),
% 51.53/7.00      inference(instantiation,[status(thm)],[c_973]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_27,plain,
% 51.53/7.00      ( r2_relset_1(X0,X1,X2,X2)
% 51.53/7.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 51.53/7.00      inference(cnf_transformation,[],[f129]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_558,plain,
% 51.53/7.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.53/7.00      | k6_partfun1(sK0) != X0
% 51.53/7.00      | sK2 != X0
% 51.53/7.00      | sK0 != X2
% 51.53/7.00      | sK0 != X1 ),
% 51.53/7.00      inference(resolution_lifted,[status(thm)],[c_27,c_39]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(c_559,plain,
% 51.53/7.00      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.53/7.00      | sK2 != k6_partfun1(sK0) ),
% 51.53/7.00      inference(unflattening,[status(thm)],[c_558]) ).
% 51.53/7.00  
% 51.53/7.00  cnf(contradiction,plain,
% 51.53/7.00      ( $false ),
% 51.53/7.00      inference(minisat,
% 51.53/7.00                [status(thm)],
% 51.53/7.00                [c_173443,c_65065,c_61014,c_51206,c_15627,c_3051,c_1744,
% 51.53/7.00                 c_1737,c_1001,c_989,c_559,c_160,c_131,c_42,c_51]) ).
% 51.53/7.00  
% 51.53/7.00  
% 51.53/7.00  % SZS output end CNFRefutation for theBenchmark.p
% 51.53/7.00  
% 51.53/7.00  ------                               Statistics
% 51.53/7.00  
% 51.53/7.00  ------ General
% 51.53/7.00  
% 51.53/7.00  abstr_ref_over_cycles:                  0
% 51.53/7.00  abstr_ref_under_cycles:                 0
% 51.53/7.00  gc_basic_clause_elim:                   0
% 51.53/7.00  forced_gc_time:                         0
% 51.53/7.00  parsing_time:                           0.016
% 51.53/7.00  unif_index_cands_time:                  0.
% 51.53/7.00  unif_index_add_time:                    0.
% 51.53/7.00  orderings_time:                         0.
% 51.53/7.00  out_proof_time:                         0.055
% 51.53/7.00  total_time:                             6.206
% 51.53/7.00  num_of_symbols:                         59
% 51.53/7.00  num_of_terms:                           164965
% 51.53/7.00  
% 51.53/7.00  ------ Preprocessing
% 51.53/7.00  
% 51.53/7.00  num_of_splits:                          0
% 51.53/7.00  num_of_split_atoms:                     0
% 51.53/7.00  num_of_reused_defs:                     0
% 51.53/7.00  num_eq_ax_congr_red:                    58
% 51.53/7.00  num_of_sem_filtered_clauses:            1
% 51.53/7.00  num_of_subtypes:                        0
% 51.53/7.00  monotx_restored_types:                  0
% 51.53/7.00  sat_num_of_epr_types:                   0
% 51.53/7.00  sat_num_of_non_cyclic_types:            0
% 51.53/7.00  sat_guarded_non_collapsed_types:        0
% 51.53/7.00  num_pure_diseq_elim:                    0
% 51.53/7.00  simp_replaced_by:                       0
% 51.53/7.00  res_preprocessed:                       217
% 51.53/7.00  prep_upred:                             0
% 51.53/7.00  prep_unflattend:                        15
% 51.53/7.00  smt_new_axioms:                         0
% 51.53/7.00  pred_elim_cands:                        6
% 51.53/7.00  pred_elim:                              3
% 51.53/7.00  pred_elim_cl:                           4
% 51.53/7.00  pred_elim_cycles:                       5
% 51.53/7.00  merged_defs:                            0
% 51.53/7.00  merged_defs_ncl:                        0
% 51.53/7.00  bin_hyper_res:                          0
% 51.53/7.00  prep_cycles:                            4
% 51.53/7.00  pred_elim_time:                         0.018
% 51.53/7.00  splitting_time:                         0.
% 51.53/7.00  sem_filter_time:                        0.
% 51.53/7.00  monotx_time:                            0.001
% 51.53/7.00  subtype_inf_time:                       0.
% 51.53/7.00  
% 51.53/7.00  ------ Problem properties
% 51.53/7.00  
% 51.53/7.00  clauses:                                44
% 51.53/7.00  conjectures:                            7
% 51.53/7.00  epr:                                    5
% 51.53/7.00  horn:                                   41
% 51.53/7.00  ground:                                 10
% 51.53/7.00  unary:                                  12
% 51.53/7.00  binary:                                 9
% 51.53/7.00  lits:                                   140
% 51.53/7.00  lits_eq:                                35
% 51.53/7.00  fd_pure:                                0
% 51.53/7.00  fd_pseudo:                              0
% 51.53/7.00  fd_cond:                                5
% 51.53/7.00  fd_pseudo_cond:                         0
% 51.53/7.00  ac_symbols:                             0
% 51.53/7.00  
% 51.53/7.00  ------ Propositional Solver
% 51.53/7.00  
% 51.53/7.00  prop_solver_calls:                      84
% 51.53/7.00  prop_fast_solver_calls:                 7516
% 51.53/7.00  smt_solver_calls:                       0
% 51.53/7.00  smt_fast_solver_calls:                  0
% 51.53/7.00  prop_num_of_clauses:                    83377
% 51.53/7.00  prop_preprocess_simplified:             145082
% 51.53/7.00  prop_fo_subsumed:                       1598
% 51.53/7.00  prop_solver_time:                       0.
% 51.53/7.00  smt_solver_time:                        0.
% 51.53/7.00  smt_fast_solver_time:                   0.
% 51.53/7.00  prop_fast_solver_time:                  0.
% 51.53/7.00  prop_unsat_core_time:                   0.012
% 51.53/7.00  
% 51.53/7.00  ------ QBF
% 51.53/7.00  
% 51.53/7.00  qbf_q_res:                              0
% 51.53/7.00  qbf_num_tautologies:                    0
% 51.53/7.00  qbf_prep_cycles:                        0
% 51.53/7.00  
% 51.53/7.00  ------ BMC1
% 51.53/7.00  
% 51.53/7.00  bmc1_current_bound:                     -1
% 51.53/7.00  bmc1_last_solved_bound:                 -1
% 51.53/7.00  bmc1_unsat_core_size:                   -1
% 51.53/7.00  bmc1_unsat_core_parents_size:           -1
% 51.53/7.00  bmc1_merge_next_fun:                    0
% 51.53/7.00  bmc1_unsat_core_clauses_time:           0.
% 51.53/7.00  
% 51.53/7.00  ------ Instantiation
% 51.53/7.00  
% 51.53/7.00  inst_num_of_clauses:                    18975
% 51.53/7.00  inst_num_in_passive:                    7473
% 51.53/7.00  inst_num_in_active:                     6232
% 51.53/7.00  inst_num_in_unprocessed:                7397
% 51.53/7.00  inst_num_of_loops:                      7599
% 51.53/7.00  inst_num_of_learning_restarts:          1
% 51.53/7.00  inst_num_moves_active_passive:          1360
% 51.53/7.00  inst_lit_activity:                      0
% 51.53/7.00  inst_lit_activity_moves:                5
% 51.53/7.00  inst_num_tautologies:                   0
% 51.53/7.00  inst_num_prop_implied:                  0
% 51.53/7.00  inst_num_existing_simplified:           0
% 51.53/7.00  inst_num_eq_res_simplified:             0
% 51.53/7.00  inst_num_child_elim:                    0
% 51.53/7.00  inst_num_of_dismatching_blockings:      15006
% 51.53/7.00  inst_num_of_non_proper_insts:           25342
% 51.53/7.00  inst_num_of_duplicates:                 0
% 51.53/7.00  inst_inst_num_from_inst_to_res:         0
% 51.53/7.00  inst_dismatching_checking_time:         0.
% 51.53/7.00  
% 51.53/7.00  ------ Resolution
% 51.53/7.00  
% 51.53/7.00  res_num_of_clauses:                     62
% 51.53/7.00  res_num_in_passive:                     62
% 51.53/7.00  res_num_in_active:                      0
% 51.53/7.00  res_num_of_loops:                       221
% 51.53/7.00  res_forward_subset_subsumed:            821
% 51.53/7.00  res_backward_subset_subsumed:           2
% 51.53/7.00  res_forward_subsumed:                   0
% 51.53/7.00  res_backward_subsumed:                  0
% 51.53/7.00  res_forward_subsumption_resolution:     0
% 51.53/7.00  res_backward_subsumption_resolution:    0
% 51.53/7.00  res_clause_to_clause_subsumption:       15099
% 51.53/7.00  res_orphan_elimination:                 0
% 51.53/7.00  res_tautology_del:                      1967
% 51.53/7.00  res_num_eq_res_simplified:              1
% 51.53/7.00  res_num_sel_changes:                    0
% 51.53/7.00  res_moves_from_active_to_pass:          0
% 51.53/7.00  
% 51.53/7.00  ------ Superposition
% 51.53/7.00  
% 51.53/7.00  sup_time_total:                         0.
% 51.53/7.00  sup_time_generating:                    0.
% 51.53/7.00  sup_time_sim_full:                      0.
% 51.53/7.00  sup_time_sim_immed:                     0.
% 51.53/7.00  
% 51.53/7.00  sup_num_of_clauses:                     5707
% 51.53/7.00  sup_num_in_active:                      1321
% 51.53/7.00  sup_num_in_passive:                     4386
% 51.53/7.00  sup_num_of_loops:                       1518
% 51.53/7.00  sup_fw_superposition:                   2531
% 51.53/7.00  sup_bw_superposition:                   4022
% 51.53/7.00  sup_immediate_simplified:               3000
% 51.53/7.00  sup_given_eliminated:                   4
% 51.53/7.00  comparisons_done:                       0
% 51.53/7.00  comparisons_avoided:                    0
% 51.53/7.00  
% 51.53/7.00  ------ Simplifications
% 51.53/7.00  
% 51.53/7.00  
% 51.53/7.00  sim_fw_subset_subsumed:                 56
% 51.53/7.00  sim_bw_subset_subsumed:                 181
% 51.53/7.00  sim_fw_subsumed:                        82
% 51.53/7.00  sim_bw_subsumed:                        14
% 51.53/7.00  sim_fw_subsumption_res:                 0
% 51.53/7.00  sim_bw_subsumption_res:                 0
% 51.53/7.00  sim_tautology_del:                      8
% 51.53/7.00  sim_eq_tautology_del:                   392
% 51.53/7.00  sim_eq_res_simp:                        7
% 51.53/7.00  sim_fw_demodulated:                     278
% 51.53/7.00  sim_bw_demodulated:                     225
% 51.53/7.00  sim_light_normalised:                   3052
% 51.53/7.00  sim_joinable_taut:                      0
% 51.53/7.00  sim_joinable_simp:                      0
% 51.53/7.00  sim_ac_normalised:                      0
% 51.53/7.00  sim_smt_subsumption:                    0
% 51.53/7.00  
%------------------------------------------------------------------------------
