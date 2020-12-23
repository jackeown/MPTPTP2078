%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:22 EST 2020

% Result     : Theorem 31.57s
% Output     : CNFRefutation 31.57s
% Verified   : 
% Statistics : Number of formulae       :  357 (6038 expanded)
%              Number of clauses        :  225 (1906 expanded)
%              Number of leaves         :   33 (1489 expanded)
%              Depth                    :   28
%              Number of atoms          : 1330 (48830 expanded)
%              Number of equality atoms :  685 (17643 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,negated_conjecture,(
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
    inference(negated_conjecture,[],[f39])).

fof(f92,plain,(
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
    inference(ennf_transformation,[],[f40])).

fof(f93,plain,(
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
    inference(flattening,[],[f92])).

fof(f100,plain,(
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

fof(f99,plain,
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

fof(f101,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f93,f100,f99])).

fof(f166,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f101])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f105,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f107,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f169,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f101])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f25,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f135,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f34,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f152,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f34])).

fof(f184,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f135,f152])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f114,plain,(
    ! [X0] :
      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f164,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f24,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f69,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f68])).

fof(f133,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f55,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f121,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f172,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f101])).

fof(f170,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f101])).

fof(f38,axiom,(
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

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f90])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f165,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f101])).

fof(f174,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f101])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f116,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f177,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f116,f152])).

fof(f113,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f23,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X0] :
      ( ( k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f66])).

fof(f131,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f91])).

fof(f167,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f101])).

fof(f168,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f101])).

fof(f173,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f101])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f94])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f95])).

fof(f186,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f104,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f37,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f88])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f56])).

fof(f122,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f106,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f29,axiom,(
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

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f29])).

fof(f77,plain,(
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
    inference(flattening,[],[f76])).

fof(f97,plain,(
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
    inference(nnf_transformation,[],[f77])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f97])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f62])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f183,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f128,f152])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f83,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f82])).

fof(f151,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f171,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f101])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f80,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f81,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f80])).

fof(f149,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f28,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f74])).

fof(f96,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f75])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f96])).

fof(f32,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f32])).

fof(f150,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f36,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f87,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f86])).

fof(f157,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | k1_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f18,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f125,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f181,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f125,f152])).

fof(f123,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f108,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f13,axiom,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f118,plain,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f178,plain,(
    ! [X0] : k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f118,f152,f152])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f78])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f79])).

fof(f146,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f35,axiom,(
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

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( v2_funct_2(X3,X0)
            & v2_funct_1(X2) )
          | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f84])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_funct_2(X3,X0)
      | ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f26])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f175,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_70,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f166])).

cnf(c_2593,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_2649,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_6338,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2593,c_2649])).

cnf(c_75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_70])).

cnf(c_3355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_5314,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_3355])).

cnf(c_5315,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5314])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_5592,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5593,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5592])).

cnf(c_6422,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6338,c_75,c_5315,c_5593])).

cnf(c_67,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f169])).

cnf(c_2596,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_6337,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2596,c_2649])).

cnf(c_78,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_67])).

cnf(c_2841,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3212,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2841])).

cnf(c_4788,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3212])).

cnf(c_4789,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4788])).

cnf(c_5589,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_5590,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5589])).

cnf(c_6401,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6337,c_78,c_4789,c_5590])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2639,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_6809,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6401,c_2639])).

cnf(c_14267,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_6422,c_6809])).

cnf(c_33,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f184])).

cnf(c_2622,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_14682,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k4_relat_1(k5_relat_1(sK2,sK3))
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14267,c_2622])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2641,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6411,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6401,c_2641])).

cnf(c_72,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f164])).

cnf(c_2591,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_32,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_2623,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_8539,plain,
    ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2591,c_2623])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2636,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7388,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2591,c_2636])).

cnf(c_64,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f172])).

cnf(c_80,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64])).

cnf(c_7636,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7388,c_75,c_80,c_5315,c_5593])).

cnf(c_66,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f170])).

cnf(c_59,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f163])).

cnf(c_2600,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_4687,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_66,c_2600])).

cnf(c_71,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f165])).

cnf(c_62,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f174])).

cnf(c_2748,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_59])).

cnf(c_3048,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2748])).

cnf(c_3321,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3048])).

cnf(c_4825,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4687,c_72,c_71,c_70,c_66,c_64,c_62,c_3321])).

cnf(c_7644,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_7636,c_4825])).

cnf(c_8542,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8539,c_7636,c_7644])).

cnf(c_15,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f177])).

cnf(c_8543,plain,
    ( k2_relat_1(sK2) = sK1
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8542,c_15])).

cnf(c_8552,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8543,c_75,c_80,c_5315,c_5593])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2640,plain,
    ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_6433,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_6422,c_2640])).

cnf(c_8556,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_8552,c_6433])).

cnf(c_30,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_2625,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_9565,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2591,c_2625])).

cnf(c_60,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f162])).

cnf(c_2599,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_3893,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_66,c_2599])).

cnf(c_2749,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_60])).

cnf(c_3090,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_2749])).

cnf(c_3343,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_3090])).

cnf(c_4440,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3893,c_72,c_71,c_70,c_66,c_64,c_62,c_3343])).

cnf(c_7645,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_7636,c_4440])).

cnf(c_9568,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9565,c_7636,c_7645])).

cnf(c_9569,plain,
    ( k1_relat_1(sK2) = sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9568,c_15])).

cnf(c_9577,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9569,c_75,c_80,c_5315,c_5593])).

cnf(c_6432,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_6422,c_2641])).

cnf(c_9581,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = sK0 ),
    inference(demodulation,[status(thm)],[c_9577,c_6432])).

cnf(c_14685,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(sK3) != sK1
    | k4_relat_1(k5_relat_1(sK2,sK3)) != k6_partfun1(sK0)
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_14682,c_6411,c_8556,c_9581])).

cnf(c_73,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_72])).

cnf(c_69,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f167])).

cnf(c_76,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_68,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f168])).

cnf(c_77,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_68])).

cnf(c_63,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f173])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f186])).

cnf(c_244,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_248,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1625,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2834,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_2835,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2834])).

cnf(c_56,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f161])).

cnf(c_2603,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_6738,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_66,c_2603])).

cnf(c_74,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_71])).

cnf(c_3687,plain,
    ( ~ v1_funct_2(X0,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(sK0,X1,X0) != X1 ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_5171,plain,
    ( ~ v1_funct_2(sK2,sK0,X0)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,X0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_3687])).

cnf(c_5733,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1 ),
    inference(instantiation,[status(thm)],[c_5171])).

cnf(c_5734,plain,
    ( k2_relset_1(sK0,sK1,sK2) != sK1
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5733])).

cnf(c_6946,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6738,c_73,c_74,c_75,c_66,c_80,c_5734])).

cnf(c_6950,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6946,c_2649])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_4557,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_4558,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4557])).

cnf(c_7059,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6950,c_73,c_75,c_4558,c_5315,c_5593])).

cnf(c_7638,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7636,c_7059])).

cnf(c_58,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f159])).

cnf(c_2601,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(X2)) = iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_5575,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_66,c_2601])).

cnf(c_5830,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5575,c_73,c_74,c_75,c_80])).

cnf(c_7643,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7636,c_5830])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_9031,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_9039,plain,
    ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9031])).

cnf(c_43,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2613,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_10985,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2596,c_2613])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_2621,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_5756,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2596,c_2621])).

cnf(c_10989,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10985,c_5756])).

cnf(c_26,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f183])).

cnf(c_2629,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_11617,plain,
    ( k6_partfun1(k1_relat_1(k4_relat_1(sK2))) != k6_partfun1(sK1)
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7644,c_2629])).

cnf(c_11622,plain,
    ( k6_partfun1(sK1) != k6_partfun1(sK1)
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11617,c_8556])).

cnf(c_11623,plain,
    ( v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_11622])).

cnf(c_49,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_2609,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_11706,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2596,c_2609])).

cnf(c_12025,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11706,c_76])).

cnf(c_12026,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_12025])).

cnf(c_12033,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2593,c_12026])).

cnf(c_12121,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_12033,c_73])).

cnf(c_65,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f171])).

cnf(c_2597,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_65])).

cnf(c_12123,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12121,c_2597])).

cnf(c_46,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_2612,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_12250,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_12121,c_2612])).

cnf(c_18931,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12250,c_73,c_75,c_76,c_78])).

cnf(c_37,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f138])).

cnf(c_2619,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_18943,plain,
    ( k5_relat_1(sK2,sK3) = X0
    | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_18931,c_2619])).

cnf(c_56783,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_12123,c_18943])).

cnf(c_48,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_3495,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_48])).

cnf(c_3496,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3495])).

cnf(c_56824,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_56783,c_3496])).

cnf(c_53,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | k2_relset_1(X4,X1,X3) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f157])).

cnf(c_2606,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_9397,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_66,c_2606])).

cnf(c_9805,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9397,c_73,c_74,c_75])).

cnf(c_9806,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9805])).

cnf(c_12128,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_12121,c_9806])).

cnf(c_14059,plain,
    ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12128,c_76,c_77,c_78,c_63,c_244,c_248,c_2835])).

cnf(c_56863,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(demodulation,[status(thm)],[c_56824,c_14059])).

cnf(c_22,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f181])).

cnf(c_10267,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_10268,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10267])).

cnf(c_56931,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56863,c_10268])).

cnf(c_2594,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_69])).

cnf(c_7387,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2594,c_2636])).

cnf(c_7580,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7387,c_78,c_4789,c_5590])).

cnf(c_7581,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_7580])).

cnf(c_56943,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_56931,c_7581])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_2635,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_57173,plain,
    ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_56943,c_2635])).

cnf(c_102191,plain,
    ( k4_relat_1(k5_relat_1(sK2,sK3)) != k6_partfun1(sK0)
    | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_14685,c_73,c_75,c_76,c_77,c_78,c_63,c_244,c_248,c_2835,c_4789,c_5315,c_5590,c_5593,c_7638,c_7643,c_9039,c_10989,c_11623,c_57173])).

cnf(c_102192,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k4_relat_1(k5_relat_1(sK2,sK3)) != k6_partfun1(sK0) ),
    inference(renaming,[status(thm)],[c_102191])).

cnf(c_7641,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7636,c_6946])).

cnf(c_11708,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,k4_relat_1(sK2)) = k5_relat_1(X2,k4_relat_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7641,c_2609])).

cnf(c_18187,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,k4_relat_1(sK2)) = k5_relat_1(X2,k4_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11708,c_7643])).

cnf(c_18188,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,k4_relat_1(sK2)) = k5_relat_1(X2,k4_relat_1(sK2))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_18187])).

cnf(c_18196,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) = k5_relat_1(sK2,k4_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2593,c_18188])).

cnf(c_18201,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_18196,c_7645])).

cnf(c_18276,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_18201,c_73])).

cnf(c_18282,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_18276,c_9806])).

cnf(c_18395,plain,
    ( v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_18282,c_73,c_75,c_5315,c_5593,c_7638,c_7643,c_11623])).

cnf(c_7389,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5830,c_2636])).

cnf(c_8649,plain,
    ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7389,c_73,c_75,c_4558,c_5315,c_5593])).

cnf(c_8650,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8649])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2646,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6434,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_6422,c_2646])).

cnf(c_8653,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8650,c_6434,c_7636])).

cnf(c_18399,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_18395,c_8653])).

cnf(c_102193,plain,
    ( k4_relat_1(k6_partfun1(sK0)) != k6_partfun1(sK0)
    | k4_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_102192,c_18399,c_56824])).

cnf(c_16,plain,
    ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f178])).

cnf(c_102194,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | k4_relat_1(sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_102193,c_16])).

cnf(c_102195,plain,
    ( k4_relat_1(sK3) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_102194])).

cnf(c_59699,plain,
    ( v1_funct_1(k4_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_57173,c_76,c_78,c_4789,c_5590])).

cnf(c_59723,plain,
    ( k2_funct_1(k4_relat_1(sK3)) = k4_relat_1(k4_relat_1(sK3))
    | v2_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_59699,c_2636])).

cnf(c_6413,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_6401,c_2646])).

cnf(c_59725,plain,
    ( k2_funct_1(k4_relat_1(sK3)) = sK3
    | v2_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_59723,c_6413])).

cnf(c_7386,plain,
    ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2635,c_2636])).

cnf(c_194,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_35477,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7386,c_194])).

cnf(c_35478,plain,
    ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_35477])).

cnf(c_57172,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3))
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_56943,c_35478])).

cnf(c_57175,plain,
    ( k2_funct_1(k4_relat_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_57172,c_6413,c_56943])).

cnf(c_56862,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) ),
    inference(demodulation,[status(thm)],[c_56824,c_14267])).

cnf(c_56866,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_56862,c_16])).

cnf(c_57718,plain,
    ( k6_partfun1(k1_relat_1(k4_relat_1(sK3))) != k6_partfun1(sK0)
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_56866,c_2629])).

cnf(c_6412,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_6401,c_2640])).

cnf(c_45,plain,
    ( ~ v2_funct_2(X0,X1)
    | ~ v5_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f146])).

cnf(c_50,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | v2_funct_2(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_787,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v5_relat_1(X4,X5)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | ~ v1_relat_1(X4)
    | X3 != X4
    | X0 != X5
    | k2_relat_1(X4) = X5 ),
    inference(resolution_lifted,[status(thm)],[c_45,c_50])).

cnf(c_788,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v5_relat_1(X3,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) = X0 ),
    inference(unflattening,[status(thm)],[c_787])).

cnf(c_34,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_812,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X3)
    | k2_relat_1(X3) = X0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_788,c_34])).

cnf(c_2590,plain,
    ( k2_relat_1(X0) = X1
    | r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X0),k6_partfun1(X1)) != iProver_top
    | v1_funct_2(X3,X1,X2) != iProver_top
    | v1_funct_2(X0,X2,X1) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_812])).

cnf(c_3758,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2597,c_2590])).

cnf(c_3761,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_relat_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3758,c_73,c_74,c_75,c_76,c_77,c_78])).

cnf(c_6414,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(superposition,[status(thm)],[c_6401,c_3761])).

cnf(c_6415,plain,
    ( k1_relat_1(k4_relat_1(sK3)) = sK0 ),
    inference(demodulation,[status(thm)],[c_6412,c_6414])).

cnf(c_57719,plain,
    ( k6_partfun1(sK0) != k6_partfun1(sK0)
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_57718,c_6415])).

cnf(c_57720,plain,
    ( v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_57719])).

cnf(c_61279,plain,
    ( k2_funct_1(k4_relat_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_59725,c_76,c_78,c_4789,c_5590,c_7638,c_7643,c_9039,c_57173,c_57175,c_57720])).

cnf(c_102231,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_102195,c_61279])).

cnf(c_61,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f175])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_102231,c_61])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:21:36 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 31.57/4.49  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 31.57/4.49  
% 31.57/4.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.57/4.49  
% 31.57/4.49  ------  iProver source info
% 31.57/4.49  
% 31.57/4.49  git: date: 2020-06-30 10:37:57 +0100
% 31.57/4.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.57/4.49  git: non_committed_changes: false
% 31.57/4.49  git: last_make_outside_of_git: false
% 31.57/4.49  
% 31.57/4.49  ------ 
% 31.57/4.49  
% 31.57/4.49  ------ Input Options
% 31.57/4.49  
% 31.57/4.49  --out_options                           all
% 31.57/4.49  --tptp_safe_out                         true
% 31.57/4.49  --problem_path                          ""
% 31.57/4.49  --include_path                          ""
% 31.57/4.49  --clausifier                            res/vclausify_rel
% 31.57/4.49  --clausifier_options                    ""
% 31.57/4.49  --stdin                                 false
% 31.57/4.49  --stats_out                             all
% 31.57/4.49  
% 31.57/4.49  ------ General Options
% 31.57/4.49  
% 31.57/4.49  --fof                                   false
% 31.57/4.49  --time_out_real                         305.
% 31.57/4.49  --time_out_virtual                      -1.
% 31.57/4.49  --symbol_type_check                     false
% 31.57/4.49  --clausify_out                          false
% 31.57/4.49  --sig_cnt_out                           false
% 31.57/4.49  --trig_cnt_out                          false
% 31.57/4.49  --trig_cnt_out_tolerance                1.
% 31.57/4.49  --trig_cnt_out_sk_spl                   false
% 31.57/4.49  --abstr_cl_out                          false
% 31.57/4.49  
% 31.57/4.49  ------ Global Options
% 31.57/4.49  
% 31.57/4.49  --schedule                              default
% 31.57/4.49  --add_important_lit                     false
% 31.57/4.49  --prop_solver_per_cl                    1000
% 31.57/4.49  --min_unsat_core                        false
% 31.57/4.49  --soft_assumptions                      false
% 31.57/4.49  --soft_lemma_size                       3
% 31.57/4.49  --prop_impl_unit_size                   0
% 31.57/4.49  --prop_impl_unit                        []
% 31.57/4.49  --share_sel_clauses                     true
% 31.57/4.49  --reset_solvers                         false
% 31.57/4.49  --bc_imp_inh                            [conj_cone]
% 31.57/4.49  --conj_cone_tolerance                   3.
% 31.57/4.49  --extra_neg_conj                        none
% 31.57/4.49  --large_theory_mode                     true
% 31.57/4.49  --prolific_symb_bound                   200
% 31.57/4.49  --lt_threshold                          2000
% 31.57/4.49  --clause_weak_htbl                      true
% 31.57/4.49  --gc_record_bc_elim                     false
% 31.57/4.49  
% 31.57/4.49  ------ Preprocessing Options
% 31.57/4.49  
% 31.57/4.49  --preprocessing_flag                    true
% 31.57/4.49  --time_out_prep_mult                    0.1
% 31.57/4.49  --splitting_mode                        input
% 31.57/4.49  --splitting_grd                         true
% 31.57/4.49  --splitting_cvd                         false
% 31.57/4.49  --splitting_cvd_svl                     false
% 31.57/4.49  --splitting_nvd                         32
% 31.57/4.49  --sub_typing                            true
% 31.57/4.49  --prep_gs_sim                           true
% 31.57/4.49  --prep_unflatten                        true
% 31.57/4.49  --prep_res_sim                          true
% 31.57/4.49  --prep_upred                            true
% 31.57/4.49  --prep_sem_filter                       exhaustive
% 31.57/4.49  --prep_sem_filter_out                   false
% 31.57/4.49  --pred_elim                             true
% 31.57/4.49  --res_sim_input                         true
% 31.57/4.49  --eq_ax_congr_red                       true
% 31.57/4.49  --pure_diseq_elim                       true
% 31.57/4.49  --brand_transform                       false
% 31.57/4.49  --non_eq_to_eq                          false
% 31.57/4.49  --prep_def_merge                        true
% 31.57/4.49  --prep_def_merge_prop_impl              false
% 31.57/4.49  --prep_def_merge_mbd                    true
% 31.57/4.49  --prep_def_merge_tr_red                 false
% 31.57/4.49  --prep_def_merge_tr_cl                  false
% 31.57/4.49  --smt_preprocessing                     true
% 31.57/4.49  --smt_ac_axioms                         fast
% 31.57/4.49  --preprocessed_out                      false
% 31.57/4.49  --preprocessed_stats                    false
% 31.57/4.49  
% 31.57/4.49  ------ Abstraction refinement Options
% 31.57/4.49  
% 31.57/4.49  --abstr_ref                             []
% 31.57/4.49  --abstr_ref_prep                        false
% 31.57/4.49  --abstr_ref_until_sat                   false
% 31.57/4.49  --abstr_ref_sig_restrict                funpre
% 31.57/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.57/4.49  --abstr_ref_under                       []
% 31.57/4.49  
% 31.57/4.49  ------ SAT Options
% 31.57/4.49  
% 31.57/4.49  --sat_mode                              false
% 31.57/4.49  --sat_fm_restart_options                ""
% 31.57/4.49  --sat_gr_def                            false
% 31.57/4.49  --sat_epr_types                         true
% 31.57/4.49  --sat_non_cyclic_types                  false
% 31.57/4.49  --sat_finite_models                     false
% 31.57/4.49  --sat_fm_lemmas                         false
% 31.57/4.49  --sat_fm_prep                           false
% 31.57/4.49  --sat_fm_uc_incr                        true
% 31.57/4.49  --sat_out_model                         small
% 31.57/4.49  --sat_out_clauses                       false
% 31.57/4.49  
% 31.57/4.49  ------ QBF Options
% 31.57/4.49  
% 31.57/4.49  --qbf_mode                              false
% 31.57/4.49  --qbf_elim_univ                         false
% 31.57/4.49  --qbf_dom_inst                          none
% 31.57/4.49  --qbf_dom_pre_inst                      false
% 31.57/4.49  --qbf_sk_in                             false
% 31.57/4.49  --qbf_pred_elim                         true
% 31.57/4.49  --qbf_split                             512
% 31.57/4.49  
% 31.57/4.49  ------ BMC1 Options
% 31.57/4.49  
% 31.57/4.49  --bmc1_incremental                      false
% 31.57/4.49  --bmc1_axioms                           reachable_all
% 31.57/4.49  --bmc1_min_bound                        0
% 31.57/4.49  --bmc1_max_bound                        -1
% 31.57/4.49  --bmc1_max_bound_default                -1
% 31.57/4.49  --bmc1_symbol_reachability              true
% 31.57/4.49  --bmc1_property_lemmas                  false
% 31.57/4.49  --bmc1_k_induction                      false
% 31.57/4.49  --bmc1_non_equiv_states                 false
% 31.57/4.49  --bmc1_deadlock                         false
% 31.57/4.49  --bmc1_ucm                              false
% 31.57/4.49  --bmc1_add_unsat_core                   none
% 31.57/4.49  --bmc1_unsat_core_children              false
% 31.57/4.49  --bmc1_unsat_core_extrapolate_axioms    false
% 31.57/4.49  --bmc1_out_stat                         full
% 31.57/4.49  --bmc1_ground_init                      false
% 31.57/4.49  --bmc1_pre_inst_next_state              false
% 31.57/4.49  --bmc1_pre_inst_state                   false
% 31.57/4.49  --bmc1_pre_inst_reach_state             false
% 31.57/4.49  --bmc1_out_unsat_core                   false
% 31.57/4.49  --bmc1_aig_witness_out                  false
% 31.57/4.49  --bmc1_verbose                          false
% 31.57/4.49  --bmc1_dump_clauses_tptp                false
% 31.57/4.49  --bmc1_dump_unsat_core_tptp             false
% 31.57/4.49  --bmc1_dump_file                        -
% 31.57/4.49  --bmc1_ucm_expand_uc_limit              128
% 31.57/4.49  --bmc1_ucm_n_expand_iterations          6
% 31.57/4.49  --bmc1_ucm_extend_mode                  1
% 31.57/4.49  --bmc1_ucm_init_mode                    2
% 31.57/4.49  --bmc1_ucm_cone_mode                    none
% 31.57/4.49  --bmc1_ucm_reduced_relation_type        0
% 31.57/4.49  --bmc1_ucm_relax_model                  4
% 31.57/4.49  --bmc1_ucm_full_tr_after_sat            true
% 31.57/4.49  --bmc1_ucm_expand_neg_assumptions       false
% 31.57/4.49  --bmc1_ucm_layered_model                none
% 31.57/4.49  --bmc1_ucm_max_lemma_size               10
% 31.57/4.49  
% 31.57/4.49  ------ AIG Options
% 31.57/4.49  
% 31.57/4.49  --aig_mode                              false
% 31.57/4.49  
% 31.57/4.49  ------ Instantiation Options
% 31.57/4.49  
% 31.57/4.49  --instantiation_flag                    true
% 31.57/4.49  --inst_sos_flag                         true
% 31.57/4.49  --inst_sos_phase                        true
% 31.57/4.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.57/4.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.57/4.49  --inst_lit_sel_side                     num_symb
% 31.57/4.49  --inst_solver_per_active                1400
% 31.57/4.49  --inst_solver_calls_frac                1.
% 31.57/4.49  --inst_passive_queue_type               priority_queues
% 31.57/4.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.57/4.49  --inst_passive_queues_freq              [25;2]
% 31.57/4.49  --inst_dismatching                      true
% 31.57/4.49  --inst_eager_unprocessed_to_passive     true
% 31.57/4.49  --inst_prop_sim_given                   true
% 31.57/4.49  --inst_prop_sim_new                     false
% 31.57/4.49  --inst_subs_new                         false
% 31.57/4.49  --inst_eq_res_simp                      false
% 31.57/4.49  --inst_subs_given                       false
% 31.57/4.49  --inst_orphan_elimination               true
% 31.57/4.49  --inst_learning_loop_flag               true
% 31.57/4.49  --inst_learning_start                   3000
% 31.57/4.49  --inst_learning_factor                  2
% 31.57/4.49  --inst_start_prop_sim_after_learn       3
% 31.57/4.49  --inst_sel_renew                        solver
% 31.57/4.49  --inst_lit_activity_flag                true
% 31.57/4.49  --inst_restr_to_given                   false
% 31.57/4.49  --inst_activity_threshold               500
% 31.57/4.49  --inst_out_proof                        true
% 31.57/4.49  
% 31.57/4.49  ------ Resolution Options
% 31.57/4.49  
% 31.57/4.49  --resolution_flag                       true
% 31.57/4.49  --res_lit_sel                           adaptive
% 31.57/4.49  --res_lit_sel_side                      none
% 31.57/4.49  --res_ordering                          kbo
% 31.57/4.49  --res_to_prop_solver                    active
% 31.57/4.49  --res_prop_simpl_new                    false
% 31.57/4.49  --res_prop_simpl_given                  true
% 31.57/4.49  --res_passive_queue_type                priority_queues
% 31.57/4.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.57/4.49  --res_passive_queues_freq               [15;5]
% 31.57/4.49  --res_forward_subs                      full
% 31.57/4.49  --res_backward_subs                     full
% 31.57/4.49  --res_forward_subs_resolution           true
% 31.57/4.49  --res_backward_subs_resolution          true
% 31.57/4.49  --res_orphan_elimination                true
% 31.57/4.49  --res_time_limit                        2.
% 31.57/4.49  --res_out_proof                         true
% 31.57/4.49  
% 31.57/4.49  ------ Superposition Options
% 31.57/4.49  
% 31.57/4.49  --superposition_flag                    true
% 31.57/4.49  --sup_passive_queue_type                priority_queues
% 31.57/4.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.57/4.49  --sup_passive_queues_freq               [8;1;4]
% 31.57/4.49  --demod_completeness_check              fast
% 31.57/4.49  --demod_use_ground                      true
% 31.57/4.49  --sup_to_prop_solver                    passive
% 31.57/4.49  --sup_prop_simpl_new                    true
% 31.57/4.49  --sup_prop_simpl_given                  true
% 31.57/4.49  --sup_fun_splitting                     true
% 31.57/4.49  --sup_smt_interval                      50000
% 31.57/4.49  
% 31.57/4.49  ------ Superposition Simplification Setup
% 31.57/4.49  
% 31.57/4.49  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.57/4.49  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.57/4.49  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.57/4.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.57/4.49  --sup_full_triv                         [TrivRules;PropSubs]
% 31.57/4.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.57/4.49  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.57/4.49  --sup_immed_triv                        [TrivRules]
% 31.57/4.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.57/4.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.57/4.49  --sup_immed_bw_main                     []
% 31.57/4.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.57/4.49  --sup_input_triv                        [Unflattening;TrivRules]
% 31.57/4.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.57/4.49  --sup_input_bw                          []
% 31.57/4.49  
% 31.57/4.49  ------ Combination Options
% 31.57/4.49  
% 31.57/4.49  --comb_res_mult                         3
% 31.57/4.49  --comb_sup_mult                         2
% 31.57/4.49  --comb_inst_mult                        10
% 31.57/4.49  
% 31.57/4.49  ------ Debug Options
% 31.57/4.49  
% 31.57/4.49  --dbg_backtrace                         false
% 31.57/4.49  --dbg_dump_prop_clauses                 false
% 31.57/4.49  --dbg_dump_prop_clauses_file            -
% 31.57/4.49  --dbg_out_stat                          false
% 31.57/4.49  ------ Parsing...
% 31.57/4.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.57/4.49  
% 31.57/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 31.57/4.49  
% 31.57/4.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.57/4.49  
% 31.57/4.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.57/4.49  ------ Proving...
% 31.57/4.49  ------ Problem Properties 
% 31.57/4.49  
% 31.57/4.49  
% 31.57/4.49  clauses                                 69
% 31.57/4.49  conjectures                             12
% 31.57/4.49  EPR                                     9
% 31.57/4.49  Horn                                    61
% 31.57/4.49  unary                                   20
% 31.57/4.49  binary                                  12
% 31.57/4.49  lits                                    236
% 31.57/4.49  lits eq                                 57
% 31.57/4.49  fd_pure                                 0
% 31.57/4.49  fd_pseudo                               0
% 31.57/4.49  fd_cond                                 7
% 31.57/4.49  fd_pseudo_cond                          4
% 31.57/4.49  AC symbols                              0
% 31.57/4.49  
% 31.57/4.49  ------ Schedule dynamic 5 is on 
% 31.57/4.49  
% 31.57/4.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 31.57/4.49  
% 31.57/4.49  
% 31.57/4.49  ------ 
% 31.57/4.49  Current options:
% 31.57/4.49  ------ 
% 31.57/4.49  
% 31.57/4.49  ------ Input Options
% 31.57/4.49  
% 31.57/4.49  --out_options                           all
% 31.57/4.49  --tptp_safe_out                         true
% 31.57/4.49  --problem_path                          ""
% 31.57/4.49  --include_path                          ""
% 31.57/4.49  --clausifier                            res/vclausify_rel
% 31.57/4.49  --clausifier_options                    ""
% 31.57/4.49  --stdin                                 false
% 31.57/4.49  --stats_out                             all
% 31.57/4.49  
% 31.57/4.49  ------ General Options
% 31.57/4.49  
% 31.57/4.49  --fof                                   false
% 31.57/4.49  --time_out_real                         305.
% 31.57/4.49  --time_out_virtual                      -1.
% 31.57/4.49  --symbol_type_check                     false
% 31.57/4.49  --clausify_out                          false
% 31.57/4.49  --sig_cnt_out                           false
% 31.57/4.49  --trig_cnt_out                          false
% 31.57/4.49  --trig_cnt_out_tolerance                1.
% 31.57/4.49  --trig_cnt_out_sk_spl                   false
% 31.57/4.49  --abstr_cl_out                          false
% 31.57/4.49  
% 31.57/4.49  ------ Global Options
% 31.57/4.49  
% 31.57/4.49  --schedule                              default
% 31.57/4.49  --add_important_lit                     false
% 31.57/4.49  --prop_solver_per_cl                    1000
% 31.57/4.49  --min_unsat_core                        false
% 31.57/4.49  --soft_assumptions                      false
% 31.57/4.49  --soft_lemma_size                       3
% 31.57/4.49  --prop_impl_unit_size                   0
% 31.57/4.49  --prop_impl_unit                        []
% 31.57/4.49  --share_sel_clauses                     true
% 31.57/4.49  --reset_solvers                         false
% 31.57/4.49  --bc_imp_inh                            [conj_cone]
% 31.57/4.49  --conj_cone_tolerance                   3.
% 31.57/4.49  --extra_neg_conj                        none
% 31.57/4.49  --large_theory_mode                     true
% 31.57/4.49  --prolific_symb_bound                   200
% 31.57/4.49  --lt_threshold                          2000
% 31.57/4.49  --clause_weak_htbl                      true
% 31.57/4.49  --gc_record_bc_elim                     false
% 31.57/4.49  
% 31.57/4.49  ------ Preprocessing Options
% 31.57/4.49  
% 31.57/4.49  --preprocessing_flag                    true
% 31.57/4.49  --time_out_prep_mult                    0.1
% 31.57/4.49  --splitting_mode                        input
% 31.57/4.49  --splitting_grd                         true
% 31.57/4.49  --splitting_cvd                         false
% 31.57/4.49  --splitting_cvd_svl                     false
% 31.57/4.49  --splitting_nvd                         32
% 31.57/4.49  --sub_typing                            true
% 31.57/4.49  --prep_gs_sim                           true
% 31.57/4.49  --prep_unflatten                        true
% 31.57/4.49  --prep_res_sim                          true
% 31.57/4.49  --prep_upred                            true
% 31.57/4.49  --prep_sem_filter                       exhaustive
% 31.57/4.49  --prep_sem_filter_out                   false
% 31.57/4.49  --pred_elim                             true
% 31.57/4.49  --res_sim_input                         true
% 31.57/4.49  --eq_ax_congr_red                       true
% 31.57/4.49  --pure_diseq_elim                       true
% 31.57/4.49  --brand_transform                       false
% 31.57/4.49  --non_eq_to_eq                          false
% 31.57/4.49  --prep_def_merge                        true
% 31.57/4.49  --prep_def_merge_prop_impl              false
% 31.57/4.49  --prep_def_merge_mbd                    true
% 31.57/4.49  --prep_def_merge_tr_red                 false
% 31.57/4.49  --prep_def_merge_tr_cl                  false
% 31.57/4.49  --smt_preprocessing                     true
% 31.57/4.49  --smt_ac_axioms                         fast
% 31.57/4.49  --preprocessed_out                      false
% 31.57/4.49  --preprocessed_stats                    false
% 31.57/4.49  
% 31.57/4.49  ------ Abstraction refinement Options
% 31.57/4.49  
% 31.57/4.49  --abstr_ref                             []
% 31.57/4.49  --abstr_ref_prep                        false
% 31.57/4.49  --abstr_ref_until_sat                   false
% 31.57/4.49  --abstr_ref_sig_restrict                funpre
% 31.57/4.49  --abstr_ref_af_restrict_to_split_sk     false
% 31.57/4.49  --abstr_ref_under                       []
% 31.57/4.49  
% 31.57/4.49  ------ SAT Options
% 31.57/4.49  
% 31.57/4.49  --sat_mode                              false
% 31.57/4.49  --sat_fm_restart_options                ""
% 31.57/4.49  --sat_gr_def                            false
% 31.57/4.49  --sat_epr_types                         true
% 31.57/4.49  --sat_non_cyclic_types                  false
% 31.57/4.49  --sat_finite_models                     false
% 31.57/4.49  --sat_fm_lemmas                         false
% 31.57/4.49  --sat_fm_prep                           false
% 31.57/4.49  --sat_fm_uc_incr                        true
% 31.57/4.49  --sat_out_model                         small
% 31.57/4.49  --sat_out_clauses                       false
% 31.57/4.49  
% 31.57/4.49  ------ QBF Options
% 31.57/4.49  
% 31.57/4.49  --qbf_mode                              false
% 31.57/4.49  --qbf_elim_univ                         false
% 31.57/4.49  --qbf_dom_inst                          none
% 31.57/4.49  --qbf_dom_pre_inst                      false
% 31.57/4.49  --qbf_sk_in                             false
% 31.57/4.49  --qbf_pred_elim                         true
% 31.57/4.49  --qbf_split                             512
% 31.57/4.49  
% 31.57/4.49  ------ BMC1 Options
% 31.57/4.49  
% 31.57/4.49  --bmc1_incremental                      false
% 31.57/4.49  --bmc1_axioms                           reachable_all
% 31.57/4.49  --bmc1_min_bound                        0
% 31.57/4.49  --bmc1_max_bound                        -1
% 31.57/4.49  --bmc1_max_bound_default                -1
% 31.57/4.49  --bmc1_symbol_reachability              true
% 31.57/4.49  --bmc1_property_lemmas                  false
% 31.57/4.49  --bmc1_k_induction                      false
% 31.57/4.50  --bmc1_non_equiv_states                 false
% 31.57/4.50  --bmc1_deadlock                         false
% 31.57/4.50  --bmc1_ucm                              false
% 31.57/4.50  --bmc1_add_unsat_core                   none
% 31.57/4.50  --bmc1_unsat_core_children              false
% 31.57/4.50  --bmc1_unsat_core_extrapolate_axioms    false
% 31.57/4.50  --bmc1_out_stat                         full
% 31.57/4.50  --bmc1_ground_init                      false
% 31.57/4.50  --bmc1_pre_inst_next_state              false
% 31.57/4.50  --bmc1_pre_inst_state                   false
% 31.57/4.50  --bmc1_pre_inst_reach_state             false
% 31.57/4.50  --bmc1_out_unsat_core                   false
% 31.57/4.50  --bmc1_aig_witness_out                  false
% 31.57/4.50  --bmc1_verbose                          false
% 31.57/4.50  --bmc1_dump_clauses_tptp                false
% 31.57/4.50  --bmc1_dump_unsat_core_tptp             false
% 31.57/4.50  --bmc1_dump_file                        -
% 31.57/4.50  --bmc1_ucm_expand_uc_limit              128
% 31.57/4.50  --bmc1_ucm_n_expand_iterations          6
% 31.57/4.50  --bmc1_ucm_extend_mode                  1
% 31.57/4.50  --bmc1_ucm_init_mode                    2
% 31.57/4.50  --bmc1_ucm_cone_mode                    none
% 31.57/4.50  --bmc1_ucm_reduced_relation_type        0
% 31.57/4.50  --bmc1_ucm_relax_model                  4
% 31.57/4.50  --bmc1_ucm_full_tr_after_sat            true
% 31.57/4.50  --bmc1_ucm_expand_neg_assumptions       false
% 31.57/4.50  --bmc1_ucm_layered_model                none
% 31.57/4.50  --bmc1_ucm_max_lemma_size               10
% 31.57/4.50  
% 31.57/4.50  ------ AIG Options
% 31.57/4.50  
% 31.57/4.50  --aig_mode                              false
% 31.57/4.50  
% 31.57/4.50  ------ Instantiation Options
% 31.57/4.50  
% 31.57/4.50  --instantiation_flag                    true
% 31.57/4.50  --inst_sos_flag                         true
% 31.57/4.50  --inst_sos_phase                        true
% 31.57/4.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 31.57/4.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 31.57/4.50  --inst_lit_sel_side                     none
% 31.57/4.50  --inst_solver_per_active                1400
% 31.57/4.50  --inst_solver_calls_frac                1.
% 31.57/4.50  --inst_passive_queue_type               priority_queues
% 31.57/4.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 31.57/4.50  --inst_passive_queues_freq              [25;2]
% 31.57/4.50  --inst_dismatching                      true
% 31.57/4.50  --inst_eager_unprocessed_to_passive     true
% 31.57/4.50  --inst_prop_sim_given                   true
% 31.57/4.50  --inst_prop_sim_new                     false
% 31.57/4.50  --inst_subs_new                         false
% 31.57/4.50  --inst_eq_res_simp                      false
% 31.57/4.50  --inst_subs_given                       false
% 31.57/4.50  --inst_orphan_elimination               true
% 31.57/4.50  --inst_learning_loop_flag               true
% 31.57/4.50  --inst_learning_start                   3000
% 31.57/4.50  --inst_learning_factor                  2
% 31.57/4.50  --inst_start_prop_sim_after_learn       3
% 31.57/4.50  --inst_sel_renew                        solver
% 31.57/4.50  --inst_lit_activity_flag                true
% 31.57/4.50  --inst_restr_to_given                   false
% 31.57/4.50  --inst_activity_threshold               500
% 31.57/4.50  --inst_out_proof                        true
% 31.57/4.50  
% 31.57/4.50  ------ Resolution Options
% 31.57/4.50  
% 31.57/4.50  --resolution_flag                       false
% 31.57/4.50  --res_lit_sel                           adaptive
% 31.57/4.50  --res_lit_sel_side                      none
% 31.57/4.50  --res_ordering                          kbo
% 31.57/4.50  --res_to_prop_solver                    active
% 31.57/4.50  --res_prop_simpl_new                    false
% 31.57/4.50  --res_prop_simpl_given                  true
% 31.57/4.50  --res_passive_queue_type                priority_queues
% 31.57/4.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 31.57/4.50  --res_passive_queues_freq               [15;5]
% 31.57/4.50  --res_forward_subs                      full
% 31.57/4.50  --res_backward_subs                     full
% 31.57/4.50  --res_forward_subs_resolution           true
% 31.57/4.50  --res_backward_subs_resolution          true
% 31.57/4.50  --res_orphan_elimination                true
% 31.57/4.50  --res_time_limit                        2.
% 31.57/4.50  --res_out_proof                         true
% 31.57/4.50  
% 31.57/4.50  ------ Superposition Options
% 31.57/4.50  
% 31.57/4.50  --superposition_flag                    true
% 31.57/4.50  --sup_passive_queue_type                priority_queues
% 31.57/4.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 31.57/4.50  --sup_passive_queues_freq               [8;1;4]
% 31.57/4.50  --demod_completeness_check              fast
% 31.57/4.50  --demod_use_ground                      true
% 31.57/4.50  --sup_to_prop_solver                    passive
% 31.57/4.50  --sup_prop_simpl_new                    true
% 31.57/4.50  --sup_prop_simpl_given                  true
% 31.57/4.50  --sup_fun_splitting                     true
% 31.57/4.50  --sup_smt_interval                      50000
% 31.57/4.50  
% 31.57/4.50  ------ Superposition Simplification Setup
% 31.57/4.50  
% 31.57/4.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 31.57/4.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 31.57/4.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 31.57/4.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 31.57/4.50  --sup_full_triv                         [TrivRules;PropSubs]
% 31.57/4.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 31.57/4.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 31.57/4.50  --sup_immed_triv                        [TrivRules]
% 31.57/4.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 31.57/4.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.57/4.50  --sup_immed_bw_main                     []
% 31.57/4.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 31.57/4.50  --sup_input_triv                        [Unflattening;TrivRules]
% 31.57/4.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 31.57/4.50  --sup_input_bw                          []
% 31.57/4.50  
% 31.57/4.50  ------ Combination Options
% 31.57/4.50  
% 31.57/4.50  --comb_res_mult                         3
% 31.57/4.50  --comb_sup_mult                         2
% 31.57/4.50  --comb_inst_mult                        10
% 31.57/4.50  
% 31.57/4.50  ------ Debug Options
% 31.57/4.50  
% 31.57/4.50  --dbg_backtrace                         false
% 31.57/4.50  --dbg_dump_prop_clauses                 false
% 31.57/4.50  --dbg_dump_prop_clauses_file            -
% 31.57/4.50  --dbg_out_stat                          false
% 31.57/4.50  
% 31.57/4.50  
% 31.57/4.50  
% 31.57/4.50  
% 31.57/4.50  ------ Proving...
% 31.57/4.50  
% 31.57/4.50  
% 31.57/4.50  % SZS status Theorem for theBenchmark.p
% 31.57/4.50  
% 31.57/4.50  % SZS output start CNFRefutation for theBenchmark.p
% 31.57/4.50  
% 31.57/4.50  fof(f39,conjecture,(
% 31.57/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f40,negated_conjecture,(
% 31.57/4.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 31.57/4.50    inference(negated_conjecture,[],[f39])).
% 31.57/4.50  
% 31.57/4.50  fof(f92,plain,(
% 31.57/4.50    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 31.57/4.50    inference(ennf_transformation,[],[f40])).
% 31.57/4.50  
% 31.57/4.50  fof(f93,plain,(
% 31.57/4.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 31.57/4.50    inference(flattening,[],[f92])).
% 31.57/4.50  
% 31.57/4.50  fof(f100,plain,(
% 31.57/4.50    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 31.57/4.50    introduced(choice_axiom,[])).
% 31.57/4.50  
% 31.57/4.50  fof(f99,plain,(
% 31.57/4.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 31.57/4.50    introduced(choice_axiom,[])).
% 31.57/4.50  
% 31.57/4.50  fof(f101,plain,(
% 31.57/4.50    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 31.57/4.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f93,f100,f99])).
% 31.57/4.50  
% 31.57/4.50  fof(f166,plain,(
% 31.57/4.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  fof(f2,axiom,(
% 31.57/4.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f43,plain,(
% 31.57/4.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.57/4.50    inference(ennf_transformation,[],[f2])).
% 31.57/4.50  
% 31.57/4.50  fof(f105,plain,(
% 31.57/4.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f43])).
% 31.57/4.50  
% 31.57/4.50  fof(f4,axiom,(
% 31.57/4.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f107,plain,(
% 31.57/4.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.57/4.50    inference(cnf_transformation,[],[f4])).
% 31.57/4.50  
% 31.57/4.50  fof(f169,plain,(
% 31.57/4.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  fof(f11,axiom,(
% 31.57/4.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f51,plain,(
% 31.57/4.50    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 31.57/4.50    inference(ennf_transformation,[],[f11])).
% 31.57/4.50  
% 31.57/4.50  fof(f115,plain,(
% 31.57/4.50    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f51])).
% 31.57/4.50  
% 31.57/4.50  fof(f25,axiom,(
% 31.57/4.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f70,plain,(
% 31.57/4.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.57/4.50    inference(ennf_transformation,[],[f25])).
% 31.57/4.50  
% 31.57/4.50  fof(f71,plain,(
% 31.57/4.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.57/4.50    inference(flattening,[],[f70])).
% 31.57/4.50  
% 31.57/4.50  fof(f135,plain,(
% 31.57/4.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f71])).
% 31.57/4.50  
% 31.57/4.50  fof(f34,axiom,(
% 31.57/4.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f152,plain,(
% 31.57/4.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f34])).
% 31.57/4.50  
% 31.57/4.50  fof(f184,plain,(
% 31.57/4.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(definition_unfolding,[],[f135,f152])).
% 31.57/4.50  
% 31.57/4.50  fof(f10,axiom,(
% 31.57/4.50    ! [X0] : (v1_relat_1(X0) => (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f50,plain,(
% 31.57/4.50    ! [X0] : ((k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 31.57/4.50    inference(ennf_transformation,[],[f10])).
% 31.57/4.50  
% 31.57/4.50  fof(f114,plain,(
% 31.57/4.50    ( ! [X0] : (k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f50])).
% 31.57/4.50  
% 31.57/4.50  fof(f164,plain,(
% 31.57/4.50    v1_funct_1(sK2)),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  fof(f24,axiom,(
% 31.57/4.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f68,plain,(
% 31.57/4.50    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.57/4.50    inference(ennf_transformation,[],[f24])).
% 31.57/4.50  
% 31.57/4.50  fof(f69,plain,(
% 31.57/4.50    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.57/4.50    inference(flattening,[],[f68])).
% 31.57/4.50  
% 31.57/4.50  fof(f133,plain,(
% 31.57/4.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f69])).
% 31.57/4.50  
% 31.57/4.50  fof(f16,axiom,(
% 31.57/4.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f54,plain,(
% 31.57/4.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.57/4.50    inference(ennf_transformation,[],[f16])).
% 31.57/4.50  
% 31.57/4.50  fof(f55,plain,(
% 31.57/4.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.57/4.50    inference(flattening,[],[f54])).
% 31.57/4.50  
% 31.57/4.50  fof(f121,plain,(
% 31.57/4.50    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f55])).
% 31.57/4.50  
% 31.57/4.50  fof(f172,plain,(
% 31.57/4.50    v2_funct_1(sK2)),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  fof(f170,plain,(
% 31.57/4.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  fof(f38,axiom,(
% 31.57/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f90,plain,(
% 31.57/4.50    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 31.57/4.50    inference(ennf_transformation,[],[f38])).
% 31.57/4.50  
% 31.57/4.50  fof(f91,plain,(
% 31.57/4.50    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 31.57/4.50    inference(flattening,[],[f90])).
% 31.57/4.50  
% 31.57/4.50  fof(f163,plain,(
% 31.57/4.50    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f91])).
% 31.57/4.50  
% 31.57/4.50  fof(f165,plain,(
% 31.57/4.50    v1_funct_2(sK2,sK0,sK1)),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  fof(f174,plain,(
% 31.57/4.50    k1_xboole_0 != sK1),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  fof(f12,axiom,(
% 31.57/4.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f116,plain,(
% 31.57/4.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 31.57/4.50    inference(cnf_transformation,[],[f12])).
% 31.57/4.50  
% 31.57/4.50  fof(f177,plain,(
% 31.57/4.50    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 31.57/4.50    inference(definition_unfolding,[],[f116,f152])).
% 31.57/4.50  
% 31.57/4.50  fof(f113,plain,(
% 31.57/4.50    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f50])).
% 31.57/4.50  
% 31.57/4.50  fof(f23,axiom,(
% 31.57/4.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f66,plain,(
% 31.57/4.50    ! [X0] : (((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.57/4.50    inference(ennf_transformation,[],[f23])).
% 31.57/4.50  
% 31.57/4.50  fof(f67,plain,(
% 31.57/4.50    ! [X0] : ((k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.57/4.50    inference(flattening,[],[f66])).
% 31.57/4.50  
% 31.57/4.50  fof(f131,plain,(
% 31.57/4.50    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f67])).
% 31.57/4.50  
% 31.57/4.50  fof(f162,plain,(
% 31.57/4.50    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f91])).
% 31.57/4.50  
% 31.57/4.50  fof(f167,plain,(
% 31.57/4.50    v1_funct_1(sK3)),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  fof(f168,plain,(
% 31.57/4.50    v1_funct_2(sK3,sK1,sK0)),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  fof(f173,plain,(
% 31.57/4.50    k1_xboole_0 != sK0),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  fof(f1,axiom,(
% 31.57/4.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f94,plain,(
% 31.57/4.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.57/4.50    inference(nnf_transformation,[],[f1])).
% 31.57/4.50  
% 31.57/4.50  fof(f95,plain,(
% 31.57/4.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 31.57/4.50    inference(flattening,[],[f94])).
% 31.57/4.50  
% 31.57/4.50  fof(f102,plain,(
% 31.57/4.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 31.57/4.50    inference(cnf_transformation,[],[f95])).
% 31.57/4.50  
% 31.57/4.50  fof(f186,plain,(
% 31.57/4.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 31.57/4.50    inference(equality_resolution,[],[f102])).
% 31.57/4.50  
% 31.57/4.50  fof(f104,plain,(
% 31.57/4.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f95])).
% 31.57/4.50  
% 31.57/4.50  fof(f37,axiom,(
% 31.57/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f88,plain,(
% 31.57/4.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 31.57/4.50    inference(ennf_transformation,[],[f37])).
% 31.57/4.50  
% 31.57/4.50  fof(f89,plain,(
% 31.57/4.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 31.57/4.50    inference(flattening,[],[f88])).
% 31.57/4.50  
% 31.57/4.50  fof(f161,plain,(
% 31.57/4.50    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f89])).
% 31.57/4.50  
% 31.57/4.50  fof(f17,axiom,(
% 31.57/4.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f56,plain,(
% 31.57/4.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.57/4.50    inference(ennf_transformation,[],[f17])).
% 31.57/4.50  
% 31.57/4.50  fof(f57,plain,(
% 31.57/4.50    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.57/4.50    inference(flattening,[],[f56])).
% 31.57/4.50  
% 31.57/4.50  fof(f122,plain,(
% 31.57/4.50    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f57])).
% 31.57/4.50  
% 31.57/4.50  fof(f159,plain,(
% 31.57/4.50    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f89])).
% 31.57/4.50  
% 31.57/4.50  fof(f3,axiom,(
% 31.57/4.50    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f44,plain,(
% 31.57/4.50    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 31.57/4.50    inference(ennf_transformation,[],[f3])).
% 31.57/4.50  
% 31.57/4.50  fof(f106,plain,(
% 31.57/4.50    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f44])).
% 31.57/4.50  
% 31.57/4.50  fof(f29,axiom,(
% 31.57/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f76,plain,(
% 31.57/4.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.57/4.50    inference(ennf_transformation,[],[f29])).
% 31.57/4.50  
% 31.57/4.50  fof(f77,plain,(
% 31.57/4.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.57/4.50    inference(flattening,[],[f76])).
% 31.57/4.50  
% 31.57/4.50  fof(f97,plain,(
% 31.57/4.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.57/4.50    inference(nnf_transformation,[],[f77])).
% 31.57/4.50  
% 31.57/4.50  fof(f140,plain,(
% 31.57/4.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.57/4.50    inference(cnf_transformation,[],[f97])).
% 31.57/4.50  
% 31.57/4.50  fof(f27,axiom,(
% 31.57/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f73,plain,(
% 31.57/4.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.57/4.50    inference(ennf_transformation,[],[f27])).
% 31.57/4.50  
% 31.57/4.50  fof(f137,plain,(
% 31.57/4.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.57/4.50    inference(cnf_transformation,[],[f73])).
% 31.57/4.50  
% 31.57/4.50  fof(f21,axiom,(
% 31.57/4.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f62,plain,(
% 31.57/4.50    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 31.57/4.50    inference(ennf_transformation,[],[f21])).
% 31.57/4.50  
% 31.57/4.50  fof(f63,plain,(
% 31.57/4.50    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 31.57/4.50    inference(flattening,[],[f62])).
% 31.57/4.50  
% 31.57/4.50  fof(f128,plain,(
% 31.57/4.50    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f63])).
% 31.57/4.50  
% 31.57/4.50  fof(f183,plain,(
% 31.57/4.50    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(definition_unfolding,[],[f128,f152])).
% 31.57/4.50  
% 31.57/4.50  fof(f33,axiom,(
% 31.57/4.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f82,plain,(
% 31.57/4.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.57/4.50    inference(ennf_transformation,[],[f33])).
% 31.57/4.50  
% 31.57/4.50  fof(f83,plain,(
% 31.57/4.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.57/4.50    inference(flattening,[],[f82])).
% 31.57/4.50  
% 31.57/4.50  fof(f151,plain,(
% 31.57/4.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f83])).
% 31.57/4.50  
% 31.57/4.50  fof(f171,plain,(
% 31.57/4.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  fof(f31,axiom,(
% 31.57/4.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f80,plain,(
% 31.57/4.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.57/4.50    inference(ennf_transformation,[],[f31])).
% 31.57/4.50  
% 31.57/4.50  fof(f81,plain,(
% 31.57/4.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.57/4.50    inference(flattening,[],[f80])).
% 31.57/4.50  
% 31.57/4.50  fof(f149,plain,(
% 31.57/4.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f81])).
% 31.57/4.50  
% 31.57/4.50  fof(f28,axiom,(
% 31.57/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f74,plain,(
% 31.57/4.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.57/4.50    inference(ennf_transformation,[],[f28])).
% 31.57/4.50  
% 31.57/4.50  fof(f75,plain,(
% 31.57/4.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.57/4.50    inference(flattening,[],[f74])).
% 31.57/4.50  
% 31.57/4.50  fof(f96,plain,(
% 31.57/4.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.57/4.50    inference(nnf_transformation,[],[f75])).
% 31.57/4.50  
% 31.57/4.50  fof(f138,plain,(
% 31.57/4.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.57/4.50    inference(cnf_transformation,[],[f96])).
% 31.57/4.50  
% 31.57/4.50  fof(f32,axiom,(
% 31.57/4.50    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f41,plain,(
% 31.57/4.50    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 31.57/4.50    inference(pure_predicate_removal,[],[f32])).
% 31.57/4.50  
% 31.57/4.50  fof(f150,plain,(
% 31.57/4.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 31.57/4.50    inference(cnf_transformation,[],[f41])).
% 31.57/4.50  
% 31.57/4.50  fof(f36,axiom,(
% 31.57/4.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f86,plain,(
% 31.57/4.50    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 31.57/4.50    inference(ennf_transformation,[],[f36])).
% 31.57/4.50  
% 31.57/4.50  fof(f87,plain,(
% 31.57/4.50    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 31.57/4.50    inference(flattening,[],[f86])).
% 31.57/4.50  
% 31.57/4.50  fof(f157,plain,(
% 31.57/4.50    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f87])).
% 31.57/4.50  
% 31.57/4.50  fof(f18,axiom,(
% 31.57/4.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f125,plain,(
% 31.57/4.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 31.57/4.50    inference(cnf_transformation,[],[f18])).
% 31.57/4.50  
% 31.57/4.50  fof(f181,plain,(
% 31.57/4.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 31.57/4.50    inference(definition_unfolding,[],[f125,f152])).
% 31.57/4.50  
% 31.57/4.50  fof(f123,plain,(
% 31.57/4.50    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f57])).
% 31.57/4.50  
% 31.57/4.50  fof(f5,axiom,(
% 31.57/4.50    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f45,plain,(
% 31.57/4.50    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 31.57/4.50    inference(ennf_transformation,[],[f5])).
% 31.57/4.50  
% 31.57/4.50  fof(f108,plain,(
% 31.57/4.50    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f45])).
% 31.57/4.50  
% 31.57/4.50  fof(f13,axiom,(
% 31.57/4.50    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f118,plain,(
% 31.57/4.50    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f13])).
% 31.57/4.50  
% 31.57/4.50  fof(f178,plain,(
% 31.57/4.50    ( ! [X0] : (k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 31.57/4.50    inference(definition_unfolding,[],[f118,f152,f152])).
% 31.57/4.50  
% 31.57/4.50  fof(f30,axiom,(
% 31.57/4.50    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f78,plain,(
% 31.57/4.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 31.57/4.50    inference(ennf_transformation,[],[f30])).
% 31.57/4.50  
% 31.57/4.50  fof(f79,plain,(
% 31.57/4.50    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.57/4.50    inference(flattening,[],[f78])).
% 31.57/4.50  
% 31.57/4.50  fof(f98,plain,(
% 31.57/4.50    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.57/4.50    inference(nnf_transformation,[],[f79])).
% 31.57/4.50  
% 31.57/4.50  fof(f146,plain,(
% 31.57/4.50    ( ! [X0,X1] : (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f98])).
% 31.57/4.50  
% 31.57/4.50  fof(f35,axiom,(
% 31.57/4.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f84,plain,(
% 31.57/4.50    ! [X0,X1,X2] : (! [X3] : (((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 31.57/4.50    inference(ennf_transformation,[],[f35])).
% 31.57/4.50  
% 31.57/4.50  fof(f85,plain,(
% 31.57/4.50    ! [X0,X1,X2] : (! [X3] : ((v2_funct_2(X3,X0) & v2_funct_1(X2)) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 31.57/4.50    inference(flattening,[],[f84])).
% 31.57/4.50  
% 31.57/4.50  fof(f154,plain,(
% 31.57/4.50    ( ! [X2,X0,X3,X1] : (v2_funct_2(X3,X0) | ~r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.57/4.50    inference(cnf_transformation,[],[f85])).
% 31.57/4.50  
% 31.57/4.50  fof(f26,axiom,(
% 31.57/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.57/4.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 31.57/4.50  
% 31.57/4.50  fof(f42,plain,(
% 31.57/4.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 31.57/4.50    inference(pure_predicate_removal,[],[f26])).
% 31.57/4.50  
% 31.57/4.50  fof(f72,plain,(
% 31.57/4.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.57/4.50    inference(ennf_transformation,[],[f42])).
% 31.57/4.50  
% 31.57/4.50  fof(f136,plain,(
% 31.57/4.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.57/4.50    inference(cnf_transformation,[],[f72])).
% 31.57/4.50  
% 31.57/4.50  fof(f175,plain,(
% 31.57/4.50    k2_funct_1(sK2) != sK3),
% 31.57/4.50    inference(cnf_transformation,[],[f101])).
% 31.57/4.50  
% 31.57/4.50  cnf(c_70,negated_conjecture,
% 31.57/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 31.57/4.50      inference(cnf_transformation,[],[f166]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2593,plain,
% 31.57/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3,plain,
% 31.57/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.57/4.50      | ~ v1_relat_1(X1)
% 31.57/4.50      | v1_relat_1(X0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f105]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2649,plain,
% 31.57/4.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 31.57/4.50      | v1_relat_1(X1) != iProver_top
% 31.57/4.50      | v1_relat_1(X0) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6338,plain,
% 31.57/4.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) = iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2593,c_2649]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_75,plain,
% 31.57/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_70]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3355,plain,
% 31.57/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.57/4.50      | v1_relat_1(X0)
% 31.57/4.50      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_3]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5314,plain,
% 31.57/4.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.57/4.50      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 31.57/4.50      | v1_relat_1(sK2) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_3355]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5315,plain,
% 31.57/4.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.57/4.50      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_5314]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5,plain,
% 31.57/4.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.57/4.50      inference(cnf_transformation,[],[f107]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5592,plain,
% 31.57/4.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_5]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5593,plain,
% 31.57/4.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_5592]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6422,plain,
% 31.57/4.50      ( v1_relat_1(sK2) = iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_6338,c_75,c_5315,c_5593]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_67,negated_conjecture,
% 31.57/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 31.57/4.50      inference(cnf_transformation,[],[f169]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2596,plain,
% 31.57/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6337,plain,
% 31.57/4.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 31.57/4.50      | v1_relat_1(sK3) = iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2596,c_2649]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_78,plain,
% 31.57/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_67]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2841,plain,
% 31.57/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 31.57/4.50      | ~ v1_relat_1(X0)
% 31.57/4.50      | v1_relat_1(sK3) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_3]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3212,plain,
% 31.57/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.57/4.50      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 31.57/4.50      | v1_relat_1(sK3) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_2841]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_4788,plain,
% 31.57/4.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.57/4.50      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 31.57/4.50      | v1_relat_1(sK3) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_3212]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_4789,plain,
% 31.57/4.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.57/4.50      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 31.57/4.50      | v1_relat_1(sK3) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_4788]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5589,plain,
% 31.57/4.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_5]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5590,plain,
% 31.57/4.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_5589]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6401,plain,
% 31.57/4.50      ( v1_relat_1(sK3) = iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_6337,c_78,c_4789,c_5590]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_13,plain,
% 31.57/4.50      ( ~ v1_relat_1(X0)
% 31.57/4.50      | ~ v1_relat_1(X1)
% 31.57/4.50      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 31.57/4.50      inference(cnf_transformation,[],[f115]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2639,plain,
% 31.57/4.50      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 31.57/4.50      | v1_relat_1(X1) != iProver_top
% 31.57/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6809,plain,
% 31.57/4.50      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK3))
% 31.57/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_6401,c_2639]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_14267,plain,
% 31.57/4.50      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,sK3)) ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_6422,c_6809]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_33,plain,
% 31.57/4.50      ( ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v1_funct_1(X1)
% 31.57/4.50      | ~ v2_funct_1(X0)
% 31.57/4.50      | ~ v1_relat_1(X0)
% 31.57/4.50      | ~ v1_relat_1(X1)
% 31.57/4.50      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 31.57/4.50      | k2_funct_1(X0) = X1
% 31.57/4.50      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 31.57/4.50      inference(cnf_transformation,[],[f184]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2622,plain,
% 31.57/4.50      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 31.57/4.50      | k2_funct_1(X1) = X0
% 31.57/4.50      | k1_relat_1(X1) != k2_relat_1(X0)
% 31.57/4.50      | v1_funct_1(X1) != iProver_top
% 31.57/4.50      | v1_funct_1(X0) != iProver_top
% 31.57/4.50      | v2_funct_1(X1) != iProver_top
% 31.57/4.50      | v1_relat_1(X1) != iProver_top
% 31.57/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_14682,plain,
% 31.57/4.50      ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
% 31.57/4.50      | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k4_relat_1(k5_relat_1(sK2,sK3))
% 31.57/4.50      | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_14267,c_2622]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_11,plain,
% 31.57/4.50      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f114]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2641,plain,
% 31.57/4.50      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 31.57/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6411,plain,
% 31.57/4.50      ( k2_relat_1(k4_relat_1(sK3)) = k1_relat_1(sK3) ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_6401,c_2641]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_72,negated_conjecture,
% 31.57/4.50      ( v1_funct_1(sK2) ),
% 31.57/4.50      inference(cnf_transformation,[],[f164]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2591,plain,
% 31.57/4.50      ( v1_funct_1(sK2) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_32,plain,
% 31.57/4.50      ( ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v2_funct_1(X0)
% 31.57/4.50      | ~ v1_relat_1(X0)
% 31.57/4.50      | k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f133]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2623,plain,
% 31.57/4.50      ( k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
% 31.57/4.50      | v1_funct_1(X0) != iProver_top
% 31.57/4.50      | v2_funct_1(X0) != iProver_top
% 31.57/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_8539,plain,
% 31.57/4.50      ( k1_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2591,c_2623]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_19,plain,
% 31.57/4.50      ( ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v2_funct_1(X0)
% 31.57/4.50      | ~ v1_relat_1(X0)
% 31.57/4.50      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f121]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2636,plain,
% 31.57/4.50      ( k2_funct_1(X0) = k4_relat_1(X0)
% 31.57/4.50      | v1_funct_1(X0) != iProver_top
% 31.57/4.50      | v2_funct_1(X0) != iProver_top
% 31.57/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7388,plain,
% 31.57/4.50      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2591,c_2636]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_64,negated_conjecture,
% 31.57/4.50      ( v2_funct_1(sK2) ),
% 31.57/4.50      inference(cnf_transformation,[],[f172]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_80,plain,
% 31.57/4.50      ( v2_funct_1(sK2) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_64]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7636,plain,
% 31.57/4.50      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_7388,c_75,c_80,c_5315,c_5593]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_66,negated_conjecture,
% 31.57/4.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 31.57/4.50      inference(cnf_transformation,[],[f170]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_59,plain,
% 31.57/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.57/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.57/4.50      | ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v2_funct_1(X0)
% 31.57/4.50      | k2_relset_1(X1,X2,X0) != X2
% 31.57/4.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 31.57/4.50      | k1_xboole_0 = X2 ),
% 31.57/4.50      inference(cnf_transformation,[],[f163]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2600,plain,
% 31.57/4.50      ( k2_relset_1(X0,X1,X2) != X1
% 31.57/4.50      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 31.57/4.50      | k1_xboole_0 = X1
% 31.57/4.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | v1_funct_1(X2) != iProver_top
% 31.57/4.50      | v2_funct_1(X2) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_4687,plain,
% 31.57/4.50      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 31.57/4.50      | sK1 = k1_xboole_0
% 31.57/4.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.57/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_66,c_2600]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_71,negated_conjecture,
% 31.57/4.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 31.57/4.50      inference(cnf_transformation,[],[f165]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_62,negated_conjecture,
% 31.57/4.50      ( k1_xboole_0 != sK1 ),
% 31.57/4.50      inference(cnf_transformation,[],[f174]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2748,plain,
% 31.57/4.50      ( ~ v1_funct_2(X0,X1,sK1)
% 31.57/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 31.57/4.50      | ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v2_funct_1(X0)
% 31.57/4.50      | k2_relset_1(X1,sK1,X0) != sK1
% 31.57/4.50      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 31.57/4.50      | k1_xboole_0 = sK1 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_59]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3048,plain,
% 31.57/4.50      ( ~ v1_funct_2(sK2,X0,sK1)
% 31.57/4.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 31.57/4.50      | ~ v1_funct_1(sK2)
% 31.57/4.50      | ~ v2_funct_1(sK2)
% 31.57/4.50      | k2_relset_1(X0,sK1,sK2) != sK1
% 31.57/4.50      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 31.57/4.50      | k1_xboole_0 = sK1 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_2748]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3321,plain,
% 31.57/4.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 31.57/4.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.57/4.50      | ~ v1_funct_1(sK2)
% 31.57/4.50      | ~ v2_funct_1(sK2)
% 31.57/4.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 31.57/4.50      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 31.57/4.50      | k1_xboole_0 = sK1 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_3048]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_4825,plain,
% 31.57/4.50      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_4687,c_72,c_71,c_70,c_66,c_64,c_62,c_3321]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7644,plain,
% 31.57/4.50      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_7636,c_4825]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_8542,plain,
% 31.57/4.50      ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.57/4.50      inference(light_normalisation,[status(thm)],[c_8539,c_7636,c_7644]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_15,plain,
% 31.57/4.50      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 31.57/4.50      inference(cnf_transformation,[],[f177]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_8543,plain,
% 31.57/4.50      ( k2_relat_1(sK2) = sK1
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_8542,c_15]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_8552,plain,
% 31.57/4.50      ( k2_relat_1(sK2) = sK1 ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_8543,c_75,c_80,c_5315,c_5593]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_12,plain,
% 31.57/4.50      ( ~ v1_relat_1(X0) | k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f113]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2640,plain,
% 31.57/4.50      ( k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)
% 31.57/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6433,plain,
% 31.57/4.50      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_6422,c_2640]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_8556,plain,
% 31.57/4.50      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_8552,c_6433]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_30,plain,
% 31.57/4.50      ( ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v2_funct_1(X0)
% 31.57/4.50      | ~ v1_relat_1(X0)
% 31.57/4.50      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f131]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2625,plain,
% 31.57/4.50      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 31.57/4.50      | v1_funct_1(X0) != iProver_top
% 31.57/4.50      | v2_funct_1(X0) != iProver_top
% 31.57/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_9565,plain,
% 31.57/4.50      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2591,c_2625]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_60,plain,
% 31.57/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.57/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.57/4.50      | ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v2_funct_1(X0)
% 31.57/4.50      | k2_relset_1(X1,X2,X0) != X2
% 31.57/4.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 31.57/4.50      | k1_xboole_0 = X2 ),
% 31.57/4.50      inference(cnf_transformation,[],[f162]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2599,plain,
% 31.57/4.50      ( k2_relset_1(X0,X1,X2) != X1
% 31.57/4.50      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 31.57/4.50      | k1_xboole_0 = X1
% 31.57/4.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | v1_funct_1(X2) != iProver_top
% 31.57/4.50      | v2_funct_1(X2) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3893,plain,
% 31.57/4.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 31.57/4.50      | sK1 = k1_xboole_0
% 31.57/4.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.57/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_66,c_2599]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2749,plain,
% 31.57/4.50      ( ~ v1_funct_2(X0,X1,sK1)
% 31.57/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 31.57/4.50      | ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v2_funct_1(X0)
% 31.57/4.50      | k2_relset_1(X1,sK1,X0) != sK1
% 31.57/4.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 31.57/4.50      | k1_xboole_0 = sK1 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_60]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3090,plain,
% 31.57/4.50      ( ~ v1_funct_2(sK2,X0,sK1)
% 31.57/4.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 31.57/4.50      | ~ v1_funct_1(sK2)
% 31.57/4.50      | ~ v2_funct_1(sK2)
% 31.57/4.50      | k2_relset_1(X0,sK1,sK2) != sK1
% 31.57/4.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 31.57/4.50      | k1_xboole_0 = sK1 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_2749]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3343,plain,
% 31.57/4.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 31.57/4.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.57/4.50      | ~ v1_funct_1(sK2)
% 31.57/4.50      | ~ v2_funct_1(sK2)
% 31.57/4.50      | k2_relset_1(sK0,sK1,sK2) != sK1
% 31.57/4.50      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 31.57/4.50      | k1_xboole_0 = sK1 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_3090]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_4440,plain,
% 31.57/4.50      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_3893,c_72,c_71,c_70,c_66,c_64,c_62,c_3343]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7645,plain,
% 31.57/4.50      ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_7636,c_4440]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_9568,plain,
% 31.57/4.50      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.57/4.50      inference(light_normalisation,[status(thm)],[c_9565,c_7636,c_7645]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_9569,plain,
% 31.57/4.50      ( k1_relat_1(sK2) = sK0
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_9568,c_15]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_9577,plain,
% 31.57/4.50      ( k1_relat_1(sK2) = sK0 ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_9569,c_75,c_80,c_5315,c_5593]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6432,plain,
% 31.57/4.50      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_6422,c_2641]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_9581,plain,
% 31.57/4.50      ( k2_relat_1(k4_relat_1(sK2)) = sK0 ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_9577,c_6432]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_14685,plain,
% 31.57/4.50      ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
% 31.57/4.50      | k1_relat_1(sK3) != sK1
% 31.57/4.50      | k4_relat_1(k5_relat_1(sK2,sK3)) != k6_partfun1(sK0)
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 31.57/4.50      inference(light_normalisation,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_14682,c_6411,c_8556,c_9581]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_73,plain,
% 31.57/4.50      ( v1_funct_1(sK2) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_72]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_69,negated_conjecture,
% 31.57/4.50      ( v1_funct_1(sK3) ),
% 31.57/4.50      inference(cnf_transformation,[],[f167]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_76,plain,
% 31.57/4.50      ( v1_funct_1(sK3) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_68,negated_conjecture,
% 31.57/4.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f168]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_77,plain,
% 31.57/4.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_68]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_63,negated_conjecture,
% 31.57/4.50      ( k1_xboole_0 != sK0 ),
% 31.57/4.50      inference(cnf_transformation,[],[f173]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2,plain,
% 31.57/4.50      ( r1_tarski(X0,X0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f186]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_244,plain,
% 31.57/4.50      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_2]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_0,plain,
% 31.57/4.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 31.57/4.50      inference(cnf_transformation,[],[f104]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_248,plain,
% 31.57/4.50      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 31.57/4.50      | k1_xboole_0 = k1_xboole_0 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_0]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_1625,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2834,plain,
% 31.57/4.50      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_1625]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2835,plain,
% 31.57/4.50      ( sK0 != k1_xboole_0
% 31.57/4.50      | k1_xboole_0 = sK0
% 31.57/4.50      | k1_xboole_0 != k1_xboole_0 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_2834]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_56,plain,
% 31.57/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.57/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.57/4.50      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 31.57/4.50      | ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v2_funct_1(X0)
% 31.57/4.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 31.57/4.50      inference(cnf_transformation,[],[f161]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2603,plain,
% 31.57/4.50      ( k2_relset_1(X0,X1,X2) != X1
% 31.57/4.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 31.57/4.50      | v1_funct_1(X2) != iProver_top
% 31.57/4.50      | v2_funct_1(X2) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6738,plain,
% 31.57/4.50      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.57/4.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 31.57/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_66,c_2603]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_74,plain,
% 31.57/4.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_71]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3687,plain,
% 31.57/4.50      ( ~ v1_funct_2(X0,sK0,X1)
% 31.57/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 31.57/4.50      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 31.57/4.50      | ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v2_funct_1(X0)
% 31.57/4.50      | k2_relset_1(sK0,X1,X0) != X1 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_56]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5171,plain,
% 31.57/4.50      ( ~ v1_funct_2(sK2,sK0,X0)
% 31.57/4.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,sK0)))
% 31.57/4.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
% 31.57/4.50      | ~ v1_funct_1(sK2)
% 31.57/4.50      | ~ v2_funct_1(sK2)
% 31.57/4.50      | k2_relset_1(sK0,X0,sK2) != X0 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_3687]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5733,plain,
% 31.57/4.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 31.57/4.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 31.57/4.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 31.57/4.50      | ~ v1_funct_1(sK2)
% 31.57/4.50      | ~ v2_funct_1(sK2)
% 31.57/4.50      | k2_relset_1(sK0,sK1,sK2) != sK1 ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_5171]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5734,plain,
% 31.57/4.50      ( k2_relset_1(sK0,sK1,sK2) != sK1
% 31.57/4.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.57/4.50      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 31.57/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_5733]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6946,plain,
% 31.57/4.50      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_6738,c_73,c_74,c_75,c_66,c_80,c_5734]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6950,plain,
% 31.57/4.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 31.57/4.50      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_6946,c_2649]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_21,plain,
% 31.57/4.50      ( ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v1_relat_1(X0)
% 31.57/4.50      | v1_relat_1(k2_funct_1(X0)) ),
% 31.57/4.50      inference(cnf_transformation,[],[f122]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_4557,plain,
% 31.57/4.50      ( ~ v1_funct_1(sK2)
% 31.57/4.50      | v1_relat_1(k2_funct_1(sK2))
% 31.57/4.50      | ~ v1_relat_1(sK2) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_21]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_4558,plain,
% 31.57/4.50      ( v1_funct_1(sK2) != iProver_top
% 31.57/4.50      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 31.57/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_4557]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7059,plain,
% 31.57/4.50      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_6950,c_73,c_75,c_4558,c_5315,c_5593]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7638,plain,
% 31.57/4.50      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_7636,c_7059]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_58,plain,
% 31.57/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.57/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.57/4.50      | ~ v1_funct_1(X0)
% 31.57/4.50      | v1_funct_1(k2_funct_1(X0))
% 31.57/4.50      | ~ v2_funct_1(X0)
% 31.57/4.50      | k2_relset_1(X1,X2,X0) != X2 ),
% 31.57/4.50      inference(cnf_transformation,[],[f159]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2601,plain,
% 31.57/4.50      ( k2_relset_1(X0,X1,X2) != X1
% 31.57/4.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | v1_funct_1(X2) != iProver_top
% 31.57/4.50      | v1_funct_1(k2_funct_1(X2)) = iProver_top
% 31.57/4.50      | v2_funct_1(X2) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5575,plain,
% 31.57/4.50      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.57/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.57/4.50      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top
% 31.57/4.50      | v2_funct_1(sK2) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_66,c_2601]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5830,plain,
% 31.57/4.50      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_5575,c_73,c_74,c_75,c_80]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7643,plain,
% 31.57/4.50      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_7636,c_5830]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_4,plain,
% 31.57/4.50      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 31.57/4.50      inference(cnf_transformation,[],[f106]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_9031,plain,
% 31.57/4.50      ( v1_relat_1(k4_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_4]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_9039,plain,
% 31.57/4.50      ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 31.57/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_9031]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_43,plain,
% 31.57/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.57/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.57/4.50      | k1_relset_1(X1,X2,X0) = X1
% 31.57/4.50      | k1_xboole_0 = X2 ),
% 31.57/4.50      inference(cnf_transformation,[],[f140]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2613,plain,
% 31.57/4.50      ( k1_relset_1(X0,X1,X2) = X0
% 31.57/4.50      | k1_xboole_0 = X1
% 31.57/4.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_10985,plain,
% 31.57/4.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 31.57/4.50      | sK0 = k1_xboole_0
% 31.57/4.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2596,c_2613]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_35,plain,
% 31.57/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.57/4.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f137]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2621,plain,
% 31.57/4.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_5756,plain,
% 31.57/4.50      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2596,c_2621]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_10989,plain,
% 31.57/4.50      ( k1_relat_1(sK3) = sK1
% 31.57/4.50      | sK0 = k1_xboole_0
% 31.57/4.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_10985,c_5756]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_26,plain,
% 31.57/4.50      ( ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v1_funct_1(X1)
% 31.57/4.50      | v2_funct_1(X0)
% 31.57/4.50      | ~ v1_relat_1(X0)
% 31.57/4.50      | ~ v1_relat_1(X1)
% 31.57/4.50      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) ),
% 31.57/4.50      inference(cnf_transformation,[],[f183]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2629,plain,
% 31.57/4.50      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 31.57/4.50      | v1_funct_1(X0) != iProver_top
% 31.57/4.50      | v1_funct_1(X1) != iProver_top
% 31.57/4.50      | v2_funct_1(X0) = iProver_top
% 31.57/4.50      | v1_relat_1(X0) != iProver_top
% 31.57/4.50      | v1_relat_1(X1) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_11617,plain,
% 31.57/4.50      ( k6_partfun1(k1_relat_1(k4_relat_1(sK2))) != k6_partfun1(sK1)
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_7644,c_2629]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_11622,plain,
% 31.57/4.50      ( k6_partfun1(sK1) != k6_partfun1(sK1)
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.57/4.50      inference(light_normalisation,[status(thm)],[c_11617,c_8556]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_11623,plain,
% 31.57/4.50      ( v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v1_relat_1(sK2) != iProver_top ),
% 31.57/4.50      inference(equality_resolution_simp,[status(thm)],[c_11622]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_49,plain,
% 31.57/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.57/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.57/4.50      | ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v1_funct_1(X3)
% 31.57/4.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f151]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2609,plain,
% 31.57/4.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 31.57/4.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 31.57/4.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | v1_funct_1(X5) != iProver_top
% 31.57/4.50      | v1_funct_1(X4) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_11706,plain,
% 31.57/4.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | v1_funct_1(X2) != iProver_top
% 31.57/4.50      | v1_funct_1(sK3) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2596,c_2609]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_12025,plain,
% 31.57/4.50      ( v1_funct_1(X2) != iProver_top
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_11706,c_76]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_12026,plain,
% 31.57/4.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | v1_funct_1(X2) != iProver_top ),
% 31.57/4.50      inference(renaming,[status(thm)],[c_12025]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_12033,plain,
% 31.57/4.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2593,c_12026]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_12121,plain,
% 31.57/4.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_12033,c_73]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_65,negated_conjecture,
% 31.57/4.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 31.57/4.50      inference(cnf_transformation,[],[f171]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2597,plain,
% 31.57/4.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_65]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_12123,plain,
% 31.57/4.50      ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) = iProver_top ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_12121,c_2597]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_46,plain,
% 31.57/4.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.57/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.57/4.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 31.57/4.50      | ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v1_funct_1(X3) ),
% 31.57/4.50      inference(cnf_transformation,[],[f149]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2612,plain,
% 31.57/4.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.57/4.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 31.57/4.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 31.57/4.50      | v1_funct_1(X0) != iProver_top
% 31.57/4.50      | v1_funct_1(X3) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_12250,plain,
% 31.57/4.50      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 31.57/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.57/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.57/4.50      | v1_funct_1(sK3) != iProver_top
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_12121,c_2612]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_18931,plain,
% 31.57/4.50      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_12250,c_73,c_75,c_76,c_78]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_37,plain,
% 31.57/4.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 31.57/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.57/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.57/4.50      | X3 = X2 ),
% 31.57/4.50      inference(cnf_transformation,[],[f138]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2619,plain,
% 31.57/4.50      ( X0 = X1
% 31.57/4.50      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 31.57/4.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 31.57/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_18943,plain,
% 31.57/4.50      ( k5_relat_1(sK2,sK3) = X0
% 31.57/4.50      | r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),X0) != iProver_top
% 31.57/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_18931,c_2619]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_56783,plain,
% 31.57/4.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 31.57/4.50      | m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_12123,c_18943]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_48,plain,
% 31.57/4.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 31.57/4.50      inference(cnf_transformation,[],[f150]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3495,plain,
% 31.57/4.50      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_48]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3496,plain,
% 31.57/4.50      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_3495]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_56824,plain,
% 31.57/4.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_56783,c_3496]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_53,plain,
% 31.57/4.50      ( ~ v1_funct_2(X0,X1,X2)
% 31.57/4.50      | ~ v1_funct_2(X3,X4,X1)
% 31.57/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 31.57/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.57/4.50      | ~ v1_funct_1(X0)
% 31.57/4.50      | ~ v1_funct_1(X3)
% 31.57/4.50      | v2_funct_1(X0)
% 31.57/4.50      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 31.57/4.50      | k2_relset_1(X4,X1,X3) != X1
% 31.57/4.50      | k1_xboole_0 = X2 ),
% 31.57/4.50      inference(cnf_transformation,[],[f157]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2606,plain,
% 31.57/4.50      ( k2_relset_1(X0,X1,X2) != X1
% 31.57/4.50      | k1_xboole_0 = X3
% 31.57/4.50      | v1_funct_2(X4,X1,X3) != iProver_top
% 31.57/4.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 31.57/4.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | v1_funct_1(X4) != iProver_top
% 31.57/4.50      | v1_funct_1(X2) != iProver_top
% 31.57/4.50      | v2_funct_1(X4) = iProver_top
% 31.57/4.50      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_9397,plain,
% 31.57/4.50      ( k1_xboole_0 = X0
% 31.57/4.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 31.57/4.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.57/4.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 31.57/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.57/4.50      | v1_funct_1(X1) != iProver_top
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top
% 31.57/4.50      | v2_funct_1(X1) = iProver_top
% 31.57/4.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_66,c_2606]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_9805,plain,
% 31.57/4.50      ( v1_funct_1(X1) != iProver_top
% 31.57/4.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 31.57/4.50      | k1_xboole_0 = X0
% 31.57/4.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 31.57/4.50      | v2_funct_1(X1) = iProver_top
% 31.57/4.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_9397,c_73,c_74,c_75]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_9806,plain,
% 31.57/4.50      ( k1_xboole_0 = X0
% 31.57/4.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 31.57/4.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 31.57/4.50      | v1_funct_1(X1) != iProver_top
% 31.57/4.50      | v2_funct_1(X1) = iProver_top
% 31.57/4.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 31.57/4.50      inference(renaming,[status(thm)],[c_9805]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_12128,plain,
% 31.57/4.50      ( sK0 = k1_xboole_0
% 31.57/4.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 31.57/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.57/4.50      | v1_funct_1(sK3) != iProver_top
% 31.57/4.50      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 31.57/4.50      | v2_funct_1(sK3) = iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_12121,c_9806]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_14059,plain,
% 31.57/4.50      ( v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 31.57/4.50      | v2_funct_1(sK3) = iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_12128,c_76,c_77,c_78,c_63,c_244,c_248,c_2835]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_56863,plain,
% 31.57/4.50      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 31.57/4.50      | v2_funct_1(sK3) = iProver_top ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_56824,c_14059]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_22,plain,
% 31.57/4.50      ( v2_funct_1(k6_partfun1(X0)) ),
% 31.57/4.50      inference(cnf_transformation,[],[f181]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_10267,plain,
% 31.57/4.50      ( v2_funct_1(k6_partfun1(sK0)) ),
% 31.57/4.50      inference(instantiation,[status(thm)],[c_22]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_10268,plain,
% 31.57/4.50      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_10267]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_56931,plain,
% 31.57/4.50      ( v2_funct_1(sK3) = iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_56863,c_10268]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2594,plain,
% 31.57/4.50      ( v1_funct_1(sK3) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_69]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7387,plain,
% 31.57/4.50      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 31.57/4.50      | v2_funct_1(sK3) != iProver_top
% 31.57/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2594,c_2636]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7580,plain,
% 31.57/4.50      ( v2_funct_1(sK3) != iProver_top
% 31.57/4.50      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_7387,c_78,c_4789,c_5590]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7581,plain,
% 31.57/4.50      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 31.57/4.50      | v2_funct_1(sK3) != iProver_top ),
% 31.57/4.50      inference(renaming,[status(thm)],[c_7580]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_56943,plain,
% 31.57/4.50      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_56931,c_7581]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_20,plain,
% 31.57/4.50      ( ~ v1_funct_1(X0)
% 31.57/4.50      | v1_funct_1(k2_funct_1(X0))
% 31.57/4.50      | ~ v1_relat_1(X0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f123]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2635,plain,
% 31.57/4.50      ( v1_funct_1(X0) != iProver_top
% 31.57/4.50      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 31.57/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_57173,plain,
% 31.57/4.50      ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
% 31.57/4.50      | v1_funct_1(sK3) != iProver_top
% 31.57/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_56943,c_2635]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_102191,plain,
% 31.57/4.50      ( k4_relat_1(k5_relat_1(sK2,sK3)) != k6_partfun1(sK0)
% 31.57/4.50      | k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_14685,c_73,c_75,c_76,c_77,c_78,c_63,c_244,c_248,
% 31.57/4.50                 c_2835,c_4789,c_5315,c_5590,c_5593,c_7638,c_7643,c_9039,
% 31.57/4.50                 c_10989,c_11623,c_57173]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_102192,plain,
% 31.57/4.50      ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
% 31.57/4.50      | k4_relat_1(k5_relat_1(sK2,sK3)) != k6_partfun1(sK0) ),
% 31.57/4.50      inference(renaming,[status(thm)],[c_102191]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7641,plain,
% 31.57/4.50      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_7636,c_6946]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_11708,plain,
% 31.57/4.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,k4_relat_1(sK2)) = k5_relat_1(X2,k4_relat_1(sK2))
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | v1_funct_1(X2) != iProver_top
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_7641,c_2609]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_18187,plain,
% 31.57/4.50      ( v1_funct_1(X2) != iProver_top
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | k1_partfun1(X0,X1,sK1,sK0,X2,k4_relat_1(sK2)) = k5_relat_1(X2,k4_relat_1(sK2)) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_11708,c_7643]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_18188,plain,
% 31.57/4.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,k4_relat_1(sK2)) = k5_relat_1(X2,k4_relat_1(sK2))
% 31.57/4.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.57/4.50      | v1_funct_1(X2) != iProver_top ),
% 31.57/4.50      inference(renaming,[status(thm)],[c_18187]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_18196,plain,
% 31.57/4.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) = k5_relat_1(sK2,k4_relat_1(sK2))
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2593,c_18188]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_18201,plain,
% 31.57/4.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) = k6_partfun1(sK0)
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top ),
% 31.57/4.50      inference(light_normalisation,[status(thm)],[c_18196,c_7645]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_18276,plain,
% 31.57/4.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_18201,c_73]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_18282,plain,
% 31.57/4.50      ( sK0 = k1_xboole_0
% 31.57/4.50      | v1_funct_2(k4_relat_1(sK2),sK1,sK0) != iProver_top
% 31.57/4.50      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_18276,c_9806]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_18395,plain,
% 31.57/4.50      ( v2_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_18282,c_73,c_75,c_5315,c_5593,c_7638,c_7643,c_11623]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7389,plain,
% 31.57/4.50      ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
% 31.57/4.50      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 31.57/4.50      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_5830,c_2636]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_8649,plain,
% 31.57/4.50      ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 31.57/4.50      | k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2)) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_7389,c_73,c_75,c_4558,c_5315,c_5593]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_8650,plain,
% 31.57/4.50      ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
% 31.57/4.50      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 31.57/4.50      inference(renaming,[status(thm)],[c_8649]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6,plain,
% 31.57/4.50      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 31.57/4.50      inference(cnf_transformation,[],[f108]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2646,plain,
% 31.57/4.50      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6434,plain,
% 31.57/4.50      ( k4_relat_1(k4_relat_1(sK2)) = sK2 ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_6422,c_2646]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_8653,plain,
% 31.57/4.50      ( k2_funct_1(k4_relat_1(sK2)) = sK2
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 31.57/4.50      inference(light_normalisation,[status(thm)],[c_8650,c_6434,c_7636]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_18399,plain,
% 31.57/4.50      ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_18395,c_8653]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_102193,plain,
% 31.57/4.50      ( k4_relat_1(k6_partfun1(sK0)) != k6_partfun1(sK0)
% 31.57/4.50      | k4_relat_1(sK3) = sK2 ),
% 31.57/4.50      inference(light_normalisation,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_102192,c_18399,c_56824]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_16,plain,
% 31.57/4.50      ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 31.57/4.50      inference(cnf_transformation,[],[f178]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_102194,plain,
% 31.57/4.50      ( k6_partfun1(sK0) != k6_partfun1(sK0) | k4_relat_1(sK3) = sK2 ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_102193,c_16]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_102195,plain,
% 31.57/4.50      ( k4_relat_1(sK3) = sK2 ),
% 31.57/4.50      inference(equality_resolution_simp,[status(thm)],[c_102194]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_59699,plain,
% 31.57/4.50      ( v1_funct_1(k4_relat_1(sK3)) = iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_57173,c_76,c_78,c_4789,c_5590]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_59723,plain,
% 31.57/4.50      ( k2_funct_1(k4_relat_1(sK3)) = k4_relat_1(k4_relat_1(sK3))
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_59699,c_2636]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6413,plain,
% 31.57/4.50      ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_6401,c_2646]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_59725,plain,
% 31.57/4.50      ( k2_funct_1(k4_relat_1(sK3)) = sK3
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top ),
% 31.57/4.50      inference(light_normalisation,[status(thm)],[c_59723,c_6413]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_7386,plain,
% 31.57/4.50      ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
% 31.57/4.50      | v1_funct_1(X0) != iProver_top
% 31.57/4.50      | v2_funct_1(k2_funct_1(X0)) != iProver_top
% 31.57/4.50      | v1_relat_1(X0) != iProver_top
% 31.57/4.50      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2635,c_2636]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_194,plain,
% 31.57/4.50      ( v1_funct_1(X0) != iProver_top
% 31.57/4.50      | v1_relat_1(X0) != iProver_top
% 31.57/4.50      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_35477,plain,
% 31.57/4.50      ( v1_relat_1(X0) != iProver_top
% 31.57/4.50      | v2_funct_1(k2_funct_1(X0)) != iProver_top
% 31.57/4.50      | v1_funct_1(X0) != iProver_top
% 31.57/4.50      | k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0)) ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_7386,c_194]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_35478,plain,
% 31.57/4.50      ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
% 31.57/4.50      | v1_funct_1(X0) != iProver_top
% 31.57/4.50      | v2_funct_1(k2_funct_1(X0)) != iProver_top
% 31.57/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(renaming,[status(thm)],[c_35477]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_57172,plain,
% 31.57/4.50      ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3))
% 31.57/4.50      | v1_funct_1(sK3) != iProver_top
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_56943,c_35478]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_57175,plain,
% 31.57/4.50      ( k2_funct_1(k4_relat_1(sK3)) = sK3
% 31.57/4.50      | v1_funct_1(sK3) != iProver_top
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.57/4.50      inference(light_normalisation,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_57172,c_6413,c_56943]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_56862,plain,
% 31.57/4.50      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_56824,c_14267]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_56866,plain,
% 31.57/4.50      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k6_partfun1(sK0) ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_56862,c_16]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_57718,plain,
% 31.57/4.50      ( k6_partfun1(k1_relat_1(k4_relat_1(sK3))) != k6_partfun1(sK0)
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK3)) = iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_56866,c_2629]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6412,plain,
% 31.57/4.50      ( k1_relat_1(k4_relat_1(sK3)) = k2_relat_1(sK3) ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_6401,c_2640]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_45,plain,
% 31.57/4.50      ( ~ v2_funct_2(X0,X1)
% 31.57/4.50      | ~ v5_relat_1(X0,X1)
% 31.57/4.50      | ~ v1_relat_1(X0)
% 31.57/4.50      | k2_relat_1(X0) = X1 ),
% 31.57/4.50      inference(cnf_transformation,[],[f146]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_50,plain,
% 31.57/4.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 31.57/4.50      | ~ v1_funct_2(X2,X0,X1)
% 31.57/4.50      | ~ v1_funct_2(X3,X1,X0)
% 31.57/4.50      | v2_funct_2(X3,X0)
% 31.57/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.57/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 31.57/4.50      | ~ v1_funct_1(X3)
% 31.57/4.50      | ~ v1_funct_1(X2) ),
% 31.57/4.50      inference(cnf_transformation,[],[f154]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_787,plain,
% 31.57/4.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 31.57/4.50      | ~ v1_funct_2(X2,X0,X1)
% 31.57/4.50      | ~ v1_funct_2(X3,X1,X0)
% 31.57/4.50      | ~ v5_relat_1(X4,X5)
% 31.57/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.57/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 31.57/4.50      | ~ v1_funct_1(X2)
% 31.57/4.50      | ~ v1_funct_1(X3)
% 31.57/4.50      | ~ v1_relat_1(X4)
% 31.57/4.50      | X3 != X4
% 31.57/4.50      | X0 != X5
% 31.57/4.50      | k2_relat_1(X4) = X5 ),
% 31.57/4.50      inference(resolution_lifted,[status(thm)],[c_45,c_50]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_788,plain,
% 31.57/4.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 31.57/4.50      | ~ v1_funct_2(X2,X0,X1)
% 31.57/4.50      | ~ v1_funct_2(X3,X1,X0)
% 31.57/4.50      | ~ v5_relat_1(X3,X0)
% 31.57/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.57/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 31.57/4.50      | ~ v1_funct_1(X3)
% 31.57/4.50      | ~ v1_funct_1(X2)
% 31.57/4.50      | ~ v1_relat_1(X3)
% 31.57/4.50      | k2_relat_1(X3) = X0 ),
% 31.57/4.50      inference(unflattening,[status(thm)],[c_787]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_34,plain,
% 31.57/4.50      ( v5_relat_1(X0,X1)
% 31.57/4.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 31.57/4.50      inference(cnf_transformation,[],[f136]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_812,plain,
% 31.57/4.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 31.57/4.50      | ~ v1_funct_2(X2,X0,X1)
% 31.57/4.50      | ~ v1_funct_2(X3,X1,X0)
% 31.57/4.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.57/4.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 31.57/4.50      | ~ v1_funct_1(X3)
% 31.57/4.50      | ~ v1_funct_1(X2)
% 31.57/4.50      | ~ v1_relat_1(X3)
% 31.57/4.50      | k2_relat_1(X3) = X0 ),
% 31.57/4.50      inference(forward_subsumption_resolution,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_788,c_34]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_2590,plain,
% 31.57/4.50      ( k2_relat_1(X0) = X1
% 31.57/4.50      | r2_relset_1(X1,X1,k1_partfun1(X1,X2,X2,X1,X3,X0),k6_partfun1(X1)) != iProver_top
% 31.57/4.50      | v1_funct_2(X3,X1,X2) != iProver_top
% 31.57/4.50      | v1_funct_2(X0,X2,X1) != iProver_top
% 31.57/4.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.57/4.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 31.57/4.50      | v1_funct_1(X3) != iProver_top
% 31.57/4.50      | v1_funct_1(X0) != iProver_top
% 31.57/4.50      | v1_relat_1(X0) != iProver_top ),
% 31.57/4.50      inference(predicate_to_equality,[status(thm)],[c_812]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3758,plain,
% 31.57/4.50      ( k2_relat_1(sK3) = sK0
% 31.57/4.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 31.57/4.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 31.57/4.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 31.57/4.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 31.57/4.50      | v1_funct_1(sK3) != iProver_top
% 31.57/4.50      | v1_funct_1(sK2) != iProver_top
% 31.57/4.50      | v1_relat_1(sK3) != iProver_top ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_2597,c_2590]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_3761,plain,
% 31.57/4.50      ( k2_relat_1(sK3) = sK0 | v1_relat_1(sK3) != iProver_top ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_3758,c_73,c_74,c_75,c_76,c_77,c_78]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6414,plain,
% 31.57/4.50      ( k2_relat_1(sK3) = sK0 ),
% 31.57/4.50      inference(superposition,[status(thm)],[c_6401,c_3761]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_6415,plain,
% 31.57/4.50      ( k1_relat_1(k4_relat_1(sK3)) = sK0 ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_6412,c_6414]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_57719,plain,
% 31.57/4.50      ( k6_partfun1(sK0) != k6_partfun1(sK0)
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK3)) = iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 31.57/4.50      inference(light_normalisation,[status(thm)],[c_57718,c_6415]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_57720,plain,
% 31.57/4.50      ( v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 31.57/4.50      | v2_funct_1(k4_relat_1(sK3)) = iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 31.57/4.50      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 31.57/4.50      inference(equality_resolution_simp,[status(thm)],[c_57719]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_61279,plain,
% 31.57/4.50      ( k2_funct_1(k4_relat_1(sK3)) = sK3 ),
% 31.57/4.50      inference(global_propositional_subsumption,
% 31.57/4.50                [status(thm)],
% 31.57/4.50                [c_59725,c_76,c_78,c_4789,c_5590,c_7638,c_7643,c_9039,
% 31.57/4.50                 c_57173,c_57175,c_57720]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_102231,plain,
% 31.57/4.50      ( k2_funct_1(sK2) = sK3 ),
% 31.57/4.50      inference(demodulation,[status(thm)],[c_102195,c_61279]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(c_61,negated_conjecture,
% 31.57/4.50      ( k2_funct_1(sK2) != sK3 ),
% 31.57/4.50      inference(cnf_transformation,[],[f175]) ).
% 31.57/4.50  
% 31.57/4.50  cnf(contradiction,plain,
% 31.57/4.50      ( $false ),
% 31.57/4.50      inference(minisat,[status(thm)],[c_102231,c_61]) ).
% 31.57/4.50  
% 31.57/4.50  
% 31.57/4.50  % SZS output end CNFRefutation for theBenchmark.p
% 31.57/4.50  
% 31.57/4.50  ------                               Statistics
% 31.57/4.50  
% 31.57/4.50  ------ General
% 31.57/4.50  
% 31.57/4.50  abstr_ref_over_cycles:                  0
% 31.57/4.50  abstr_ref_under_cycles:                 0
% 31.57/4.50  gc_basic_clause_elim:                   0
% 31.57/4.50  forced_gc_time:                         0
% 31.57/4.50  parsing_time:                           0.015
% 31.57/4.50  unif_index_cands_time:                  0.
% 31.57/4.50  unif_index_add_time:                    0.
% 31.57/4.50  orderings_time:                         0.
% 31.57/4.50  out_proof_time:                         0.046
% 31.57/4.50  total_time:                             3.53
% 31.57/4.50  num_of_symbols:                         58
% 31.57/4.50  num_of_terms:                           114246
% 31.57/4.50  
% 31.57/4.50  ------ Preprocessing
% 31.57/4.50  
% 31.57/4.50  num_of_splits:                          0
% 31.57/4.50  num_of_split_atoms:                     0
% 31.57/4.50  num_of_reused_defs:                     0
% 31.57/4.50  num_eq_ax_congr_red:                    8
% 31.57/4.50  num_of_sem_filtered_clauses:            1
% 31.57/4.50  num_of_subtypes:                        0
% 31.57/4.50  monotx_restored_types:                  0
% 31.57/4.50  sat_num_of_epr_types:                   0
% 31.57/4.50  sat_num_of_non_cyclic_types:            0
% 31.57/4.50  sat_guarded_non_collapsed_types:        0
% 31.57/4.50  num_pure_diseq_elim:                    0
% 31.57/4.50  simp_replaced_by:                       0
% 31.57/4.50  res_preprocessed:                       324
% 31.57/4.50  prep_upred:                             0
% 31.57/4.50  prep_unflattend:                        38
% 31.57/4.50  smt_new_axioms:                         0
% 31.57/4.50  pred_elim_cands:                        7
% 31.57/4.50  pred_elim:                              2
% 31.57/4.50  pred_elim_cl:                           3
% 31.57/4.50  pred_elim_cycles:                       5
% 31.57/4.50  merged_defs:                            0
% 31.57/4.50  merged_defs_ncl:                        0
% 31.57/4.50  bin_hyper_res:                          0
% 31.57/4.50  prep_cycles:                            4
% 31.57/4.50  pred_elim_time:                         0.014
% 31.57/4.50  splitting_time:                         0.
% 31.57/4.50  sem_filter_time:                        0.
% 31.57/4.50  monotx_time:                            0.001
% 31.57/4.50  subtype_inf_time:                       0.
% 31.57/4.50  
% 31.57/4.50  ------ Problem properties
% 31.57/4.50  
% 31.57/4.50  clauses:                                69
% 31.57/4.50  conjectures:                            12
% 31.57/4.50  epr:                                    9
% 31.57/4.50  horn:                                   61
% 31.57/4.50  ground:                                 12
% 31.57/4.50  unary:                                  20
% 31.57/4.50  binary:                                 12
% 31.57/4.50  lits:                                   236
% 31.57/4.50  lits_eq:                                57
% 31.57/4.50  fd_pure:                                0
% 31.57/4.50  fd_pseudo:                              0
% 31.57/4.50  fd_cond:                                7
% 31.57/4.50  fd_pseudo_cond:                         4
% 31.57/4.50  ac_symbols:                             0
% 31.57/4.50  
% 31.57/4.50  ------ Propositional Solver
% 31.57/4.50  
% 31.57/4.50  prop_solver_calls:                      48
% 31.57/4.50  prop_fast_solver_calls:                 6360
% 31.57/4.50  smt_solver_calls:                       0
% 31.57/4.50  smt_fast_solver_calls:                  0
% 31.57/4.50  prop_num_of_clauses:                    42333
% 31.57/4.50  prop_preprocess_simplified:             101805
% 31.57/4.50  prop_fo_subsumed:                       1158
% 31.57/4.50  prop_solver_time:                       0.
% 31.57/4.50  smt_solver_time:                        0.
% 31.57/4.50  smt_fast_solver_time:                   0.
% 31.57/4.50  prop_fast_solver_time:                  0.
% 31.57/4.50  prop_unsat_core_time:                   0.007
% 31.57/4.50  
% 31.57/4.50  ------ QBF
% 31.57/4.50  
% 31.57/4.50  qbf_q_res:                              0
% 31.57/4.50  qbf_num_tautologies:                    0
% 31.57/4.50  qbf_prep_cycles:                        0
% 31.57/4.50  
% 31.57/4.50  ------ BMC1
% 31.57/4.50  
% 31.57/4.50  bmc1_current_bound:                     -1
% 31.57/4.50  bmc1_last_solved_bound:                 -1
% 31.57/4.50  bmc1_unsat_core_size:                   -1
% 31.57/4.50  bmc1_unsat_core_parents_size:           -1
% 31.57/4.50  bmc1_merge_next_fun:                    0
% 31.57/4.50  bmc1_unsat_core_clauses_time:           0.
% 31.57/4.50  
% 31.57/4.50  ------ Instantiation
% 31.57/4.50  
% 31.57/4.50  inst_num_of_clauses:                    5463
% 31.57/4.50  inst_num_in_passive:                    2227
% 31.57/4.50  inst_num_in_active:                     4531
% 31.57/4.50  inst_num_in_unprocessed:                1387
% 31.57/4.50  inst_num_of_loops:                      4889
% 31.57/4.50  inst_num_of_learning_restarts:          1
% 31.57/4.50  inst_num_moves_active_passive:          355
% 31.57/4.50  inst_lit_activity:                      0
% 31.57/4.50  inst_lit_activity_moves:                6
% 31.57/4.50  inst_num_tautologies:                   0
% 31.57/4.50  inst_num_prop_implied:                  0
% 31.57/4.50  inst_num_existing_simplified:           0
% 31.57/4.50  inst_num_eq_res_simplified:             0
% 31.57/4.50  inst_num_child_elim:                    0
% 31.57/4.50  inst_num_of_dismatching_blockings:      7268
% 31.57/4.50  inst_num_of_non_proper_insts:           13252
% 31.57/4.50  inst_num_of_duplicates:                 0
% 31.57/4.50  inst_inst_num_from_inst_to_res:         0
% 31.57/4.50  inst_dismatching_checking_time:         0.
% 31.57/4.50  
% 31.57/4.50  ------ Resolution
% 31.57/4.50  
% 31.57/4.50  res_num_of_clauses:                     91
% 31.57/4.50  res_num_in_passive:                     91
% 31.57/4.50  res_num_in_active:                      0
% 31.57/4.50  res_num_of_loops:                       328
% 31.57/4.50  res_forward_subset_subsumed:            691
% 31.57/4.50  res_backward_subset_subsumed:           2
% 31.57/4.50  res_forward_subsumed:                   0
% 31.57/4.50  res_backward_subsumed:                  0
% 31.57/4.50  res_forward_subsumption_resolution:     4
% 31.57/4.50  res_backward_subsumption_resolution:    0
% 31.57/4.50  res_clause_to_clause_subsumption:       7490
% 31.57/4.50  res_orphan_elimination:                 0
% 31.57/4.50  res_tautology_del:                      273
% 31.57/4.50  res_num_eq_res_simplified:              0
% 31.57/4.50  res_num_sel_changes:                    0
% 31.57/4.50  res_moves_from_active_to_pass:          0
% 31.57/4.50  
% 31.57/4.50  ------ Superposition
% 31.57/4.50  
% 31.57/4.50  sup_time_total:                         0.
% 31.57/4.50  sup_time_generating:                    0.
% 31.57/4.50  sup_time_sim_full:                      0.
% 31.57/4.50  sup_time_sim_immed:                     0.
% 31.57/4.50  
% 31.57/4.50  sup_num_of_clauses:                     2411
% 31.57/4.50  sup_num_in_active:                      678
% 31.57/4.50  sup_num_in_passive:                     1733
% 31.57/4.50  sup_num_of_loops:                       977
% 31.57/4.50  sup_fw_superposition:                   1584
% 31.57/4.50  sup_bw_superposition:                   2352
% 31.57/4.50  sup_immediate_simplified:               2281
% 31.57/4.50  sup_given_eliminated:                   0
% 31.57/4.50  comparisons_done:                       0
% 31.57/4.50  comparisons_avoided:                    1
% 31.57/4.50  
% 31.57/4.50  ------ Simplifications
% 31.57/4.50  
% 31.57/4.50  
% 31.57/4.50  sim_fw_subset_subsumed:                 183
% 31.57/4.50  sim_bw_subset_subsumed:                 151
% 31.57/4.50  sim_fw_subsumed:                        187
% 31.57/4.50  sim_bw_subsumed:                        1
% 31.57/4.50  sim_fw_subsumption_res:                 0
% 31.57/4.50  sim_bw_subsumption_res:                 0
% 31.57/4.50  sim_tautology_del:                      37
% 31.57/4.50  sim_eq_tautology_del:                   744
% 31.57/4.50  sim_eq_res_simp:                        64
% 31.57/4.50  sim_fw_demodulated:                     659
% 31.57/4.50  sim_bw_demodulated:                     309
% 31.57/4.50  sim_light_normalised:                   1611
% 31.57/4.50  sim_joinable_taut:                      0
% 31.57/4.50  sim_joinable_simp:                      0
% 31.57/4.50  sim_ac_normalised:                      0
% 31.57/4.50  sim_smt_subsumption:                    0
% 31.57/4.50  
%------------------------------------------------------------------------------
