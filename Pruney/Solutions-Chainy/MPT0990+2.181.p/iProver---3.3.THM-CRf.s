%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:35 EST 2020

% Result     : Theorem 46.94s
% Output     : CNFRefutation 46.94s
% Verified   : 
% Statistics : Number of formulae       :  208 (2293 expanded)
%              Number of clauses        :  129 ( 656 expanded)
%              Number of leaves         :   23 ( 611 expanded)
%              Depth                    :   22
%              Number of atoms          :  784 (19455 expanded)
%              Number of equality atoms :  393 (7051 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,conjecture,(
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

fof(f33,negated_conjecture,(
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
    inference(negated_conjecture,[],[f32])).

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f33])).

fof(f77,plain,(
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
    inference(flattening,[],[f76])).

fof(f80,plain,(
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

fof(f79,plain,
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

fof(f81,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f77,f80,f79])).

fof(f134,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f31,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f75,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f74])).

fof(f130,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f136,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f81])).

fof(f27,axiom,(
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

fof(f66,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f67,plain,(
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
    inference(flattening,[],[f66])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f138,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f81])).

fof(f131,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

fof(f132,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f81])).

fof(f133,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f81])).

fof(f135,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f81])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f82,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f72])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f99,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f26,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f117,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f26])).

fof(f149,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f99,f117])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f60])).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f111,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f23,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f113,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f152,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f113,f117])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f62])).

fof(f115,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f137,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f81])).

fof(f28,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f69,plain,(
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
    inference(flattening,[],[f68])).

fof(f121,plain,(
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
    inference(cnf_transformation,[],[f69])).

fof(f140,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f81])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f42,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f93,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f129,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f7,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f143,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f90,f117])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f64])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f151,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f107,f117])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f84,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f142,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f81])).

fof(f139,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_56,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_1797,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_45,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1802,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1816,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3976,plain,
    ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1802,c_1816])).

cnf(c_10164,plain,
    ( k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_3976])).

cnf(c_54,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1799,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_3923,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1799,c_1816])).

cnf(c_35,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_52,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_647,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_52])).

cnf(c_648,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_751,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_648])).

cnf(c_1791,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_2406,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1791])).

cnf(c_59,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_60,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_58,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_61,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_57,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_62,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_63,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_55,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_64,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_65,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_2661,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2406,c_60,c_61,c_62,c_63,c_64,c_65])).

cnf(c_3926,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_3923,c_2661])).

cnf(c_10173,plain,
    ( k2_relset_1(k1_relat_1(sK3),sK0,sK3) = sK0
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10164,c_3926])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2000,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2373,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_2994,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2373])).

cnf(c_2995,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2994])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_3496,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3497,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3496])).

cnf(c_10740,plain,
    ( k2_relset_1(k1_relat_1(sK3),sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10173,c_65,c_2995,c_3497])).

cnf(c_44,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1803,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_10748,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_10740,c_1803])).

cnf(c_16,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_1825,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_30,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_634,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_52])).

cnf(c_635,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_634])).

cnf(c_31,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_643,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_635,c_31])).

cnf(c_1792,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_643])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1943,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2654,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1792,c_59,c_57,c_56,c_54,c_643,c_1943])).

cnf(c_53,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k2_relset_1(X1,X2,X0) != X2
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1810,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k1_xboole_0 = X3
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X4,X1,X3) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_8691,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_53,c_1810])).

cnf(c_8728,plain,
    ( v1_funct_1(X1) != iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8691,c_60,c_61,c_62])).

cnf(c_8729,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_8728])).

cnf(c_8732,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2654,c_8729])).

cnf(c_50,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f140])).

cnf(c_1029,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1066,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_1030,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1941,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1942,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1941])).

cnf(c_8735,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8732,c_63,c_64,c_65,c_50,c_1066,c_1942])).

cnf(c_8739,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1825,c_8735])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1830,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6245,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1797,c_1830])).

cnf(c_6834,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6245,c_65,c_2995,c_3497])).

cnf(c_6835,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6834])).

cnf(c_8820,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_8739,c_6835])).

cnf(c_10749,plain,
    ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10748,c_8820])).

cnf(c_4984,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3926,c_1802])).

cnf(c_46,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1801,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_4985,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),sK0) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3926,c_1801])).

cnf(c_135062,plain,
    ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10749,c_63,c_65,c_50,c_1066,c_1942,c_2995,c_3497,c_4984,c_4985,c_8739])).

cnf(c_5790,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2661,c_1803])).

cnf(c_25120,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5790,c_63,c_64,c_65,c_50,c_1066,c_1942,c_8739])).

cnf(c_25122,plain,
    ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_25120,c_8820])).

cnf(c_135064,plain,
    ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_135062,c_25122])).

cnf(c_7,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f143])).

cnf(c_135220,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_135064,c_7])).

cnf(c_135223,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_135220,c_7])).

cnf(c_1035,plain,
    ( X0 != X1
    | k4_relat_1(X0) = k4_relat_1(X1) ),
    theory(equality)).

cnf(c_95203,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = k4_relat_1(sK2)
    | k4_relat_1(sK3) != sK2 ),
    inference(instantiation,[status(thm)],[c_1035])).

cnf(c_70537,plain,
    ( k2_funct_1(sK2) != X0
    | k2_funct_1(sK2) = k4_relat_1(k4_relat_1(sK3))
    | k4_relat_1(k4_relat_1(sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_73023,plain,
    ( k2_funct_1(sK2) = k4_relat_1(k4_relat_1(sK3))
    | k2_funct_1(sK2) != k4_relat_1(sK2)
    | k4_relat_1(k4_relat_1(sK3)) != k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_70537])).

cnf(c_1901,plain,
    ( k2_funct_1(sK2) != X0
    | k2_funct_1(sK2) = sK3
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_19331,plain,
    ( k2_funct_1(sK2) != k4_relat_1(k4_relat_1(sK3))
    | k2_funct_1(sK2) = sK3
    | sK3 != k4_relat_1(k4_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1901])).

cnf(c_1796,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_34,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1812,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_7557,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1799,c_1812])).

cnf(c_7691,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7557,c_63])).

cnf(c_7692,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7691])).

cnf(c_7700,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_7692])).

cnf(c_7702,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7700,c_2654])).

cnf(c_7834,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7702,c_60])).

cnf(c_25,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_1819,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_8243,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7834,c_1819])).

cnf(c_3924,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1796,c_1816])).

cnf(c_3925,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3924,c_53])).

cnf(c_8244,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8243,c_3925,c_3926])).

cnf(c_8245,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8244])).

cnf(c_1838,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_1839,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4033,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_1839])).

cnf(c_4599,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_4033])).

cnf(c_13923,plain,
    ( k1_relat_1(sK3) != sK1
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8245,c_60,c_63,c_65,c_2995,c_3497,c_4599,c_8739])).

cnf(c_13924,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1 ),
    inference(renaming,[status(thm)],[c_13923])).

cnf(c_13925,plain,
    ( k1_relat_1(sK3) != sK1
    | k4_relat_1(sK3) = sK2 ),
    inference(demodulation,[status(thm)],[c_13924,c_8820])).

cnf(c_2006,plain,
    ( X0 != X1
    | sK3 != X1
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_2388,plain,
    ( X0 != sK3
    | sK3 = X0
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2006])).

cnf(c_9959,plain,
    ( k4_relat_1(k4_relat_1(sK3)) != sK3
    | sK3 = k4_relat_1(k4_relat_1(sK3))
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2388])).

cnf(c_1794,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_6246,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1794,c_1830])).

cnf(c_2972,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_2670,plain,
    ( ~ v1_relat_1(sK3)
    | k4_relat_1(k4_relat_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_48,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f142])).

cnf(c_51,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_67,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_135223,c_95203,c_73023,c_19331,c_13925,c_9959,c_6246,c_4599,c_3496,c_2994,c_2972,c_2670,c_48,c_67,c_54])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:07:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 46.94/6.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 46.94/6.50  
% 46.94/6.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 46.94/6.50  
% 46.94/6.50  ------  iProver source info
% 46.94/6.50  
% 46.94/6.50  git: date: 2020-06-30 10:37:57 +0100
% 46.94/6.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 46.94/6.50  git: non_committed_changes: false
% 46.94/6.50  git: last_make_outside_of_git: false
% 46.94/6.50  
% 46.94/6.50  ------ 
% 46.94/6.50  
% 46.94/6.50  ------ Input Options
% 46.94/6.50  
% 46.94/6.50  --out_options                           all
% 46.94/6.50  --tptp_safe_out                         true
% 46.94/6.50  --problem_path                          ""
% 46.94/6.50  --include_path                          ""
% 46.94/6.50  --clausifier                            res/vclausify_rel
% 46.94/6.50  --clausifier_options                    ""
% 46.94/6.50  --stdin                                 false
% 46.94/6.50  --stats_out                             all
% 46.94/6.50  
% 46.94/6.50  ------ General Options
% 46.94/6.50  
% 46.94/6.50  --fof                                   false
% 46.94/6.50  --time_out_real                         305.
% 46.94/6.50  --time_out_virtual                      -1.
% 46.94/6.50  --symbol_type_check                     false
% 46.94/6.50  --clausify_out                          false
% 46.94/6.50  --sig_cnt_out                           false
% 46.94/6.50  --trig_cnt_out                          false
% 46.94/6.50  --trig_cnt_out_tolerance                1.
% 46.94/6.50  --trig_cnt_out_sk_spl                   false
% 46.94/6.50  --abstr_cl_out                          false
% 46.94/6.50  
% 46.94/6.50  ------ Global Options
% 46.94/6.50  
% 46.94/6.50  --schedule                              default
% 46.94/6.50  --add_important_lit                     false
% 46.94/6.50  --prop_solver_per_cl                    1000
% 46.94/6.50  --min_unsat_core                        false
% 46.94/6.50  --soft_assumptions                      false
% 46.94/6.50  --soft_lemma_size                       3
% 46.94/6.50  --prop_impl_unit_size                   0
% 46.94/6.50  --prop_impl_unit                        []
% 46.94/6.50  --share_sel_clauses                     true
% 46.94/6.50  --reset_solvers                         false
% 46.94/6.50  --bc_imp_inh                            [conj_cone]
% 46.94/6.50  --conj_cone_tolerance                   3.
% 46.94/6.50  --extra_neg_conj                        none
% 46.94/6.50  --large_theory_mode                     true
% 46.94/6.50  --prolific_symb_bound                   200
% 46.94/6.50  --lt_threshold                          2000
% 46.94/6.50  --clause_weak_htbl                      true
% 46.94/6.50  --gc_record_bc_elim                     false
% 46.94/6.50  
% 46.94/6.50  ------ Preprocessing Options
% 46.94/6.50  
% 46.94/6.50  --preprocessing_flag                    true
% 46.94/6.50  --time_out_prep_mult                    0.1
% 46.94/6.50  --splitting_mode                        input
% 46.94/6.50  --splitting_grd                         true
% 46.94/6.50  --splitting_cvd                         false
% 46.94/6.50  --splitting_cvd_svl                     false
% 46.94/6.50  --splitting_nvd                         32
% 46.94/6.50  --sub_typing                            true
% 46.94/6.50  --prep_gs_sim                           true
% 46.94/6.50  --prep_unflatten                        true
% 46.94/6.50  --prep_res_sim                          true
% 46.94/6.50  --prep_upred                            true
% 46.94/6.50  --prep_sem_filter                       exhaustive
% 46.94/6.50  --prep_sem_filter_out                   false
% 46.94/6.50  --pred_elim                             true
% 46.94/6.50  --res_sim_input                         true
% 46.94/6.50  --eq_ax_congr_red                       true
% 46.94/6.50  --pure_diseq_elim                       true
% 46.94/6.50  --brand_transform                       false
% 46.94/6.50  --non_eq_to_eq                          false
% 46.94/6.50  --prep_def_merge                        true
% 46.94/6.50  --prep_def_merge_prop_impl              false
% 46.94/6.50  --prep_def_merge_mbd                    true
% 46.94/6.50  --prep_def_merge_tr_red                 false
% 46.94/6.50  --prep_def_merge_tr_cl                  false
% 46.94/6.50  --smt_preprocessing                     true
% 46.94/6.50  --smt_ac_axioms                         fast
% 46.94/6.50  --preprocessed_out                      false
% 46.94/6.50  --preprocessed_stats                    false
% 46.94/6.50  
% 46.94/6.50  ------ Abstraction refinement Options
% 46.94/6.50  
% 46.94/6.50  --abstr_ref                             []
% 46.94/6.50  --abstr_ref_prep                        false
% 46.94/6.50  --abstr_ref_until_sat                   false
% 46.94/6.50  --abstr_ref_sig_restrict                funpre
% 46.94/6.50  --abstr_ref_af_restrict_to_split_sk     false
% 46.94/6.50  --abstr_ref_under                       []
% 46.94/6.50  
% 46.94/6.50  ------ SAT Options
% 46.94/6.50  
% 46.94/6.50  --sat_mode                              false
% 46.94/6.50  --sat_fm_restart_options                ""
% 46.94/6.50  --sat_gr_def                            false
% 46.94/6.50  --sat_epr_types                         true
% 46.94/6.50  --sat_non_cyclic_types                  false
% 46.94/6.50  --sat_finite_models                     false
% 46.94/6.50  --sat_fm_lemmas                         false
% 46.94/6.50  --sat_fm_prep                           false
% 46.94/6.50  --sat_fm_uc_incr                        true
% 46.94/6.50  --sat_out_model                         small
% 46.94/6.50  --sat_out_clauses                       false
% 46.94/6.50  
% 46.94/6.50  ------ QBF Options
% 46.94/6.50  
% 46.94/6.50  --qbf_mode                              false
% 46.94/6.50  --qbf_elim_univ                         false
% 46.94/6.50  --qbf_dom_inst                          none
% 46.94/6.50  --qbf_dom_pre_inst                      false
% 46.94/6.50  --qbf_sk_in                             false
% 46.94/6.50  --qbf_pred_elim                         true
% 46.94/6.50  --qbf_split                             512
% 46.94/6.50  
% 46.94/6.50  ------ BMC1 Options
% 46.94/6.50  
% 46.94/6.50  --bmc1_incremental                      false
% 46.94/6.50  --bmc1_axioms                           reachable_all
% 46.94/6.50  --bmc1_min_bound                        0
% 46.94/6.50  --bmc1_max_bound                        -1
% 46.94/6.50  --bmc1_max_bound_default                -1
% 46.94/6.50  --bmc1_symbol_reachability              true
% 46.94/6.50  --bmc1_property_lemmas                  false
% 46.94/6.50  --bmc1_k_induction                      false
% 46.94/6.50  --bmc1_non_equiv_states                 false
% 46.94/6.50  --bmc1_deadlock                         false
% 46.94/6.50  --bmc1_ucm                              false
% 46.94/6.50  --bmc1_add_unsat_core                   none
% 46.94/6.50  --bmc1_unsat_core_children              false
% 46.94/6.50  --bmc1_unsat_core_extrapolate_axioms    false
% 46.94/6.50  --bmc1_out_stat                         full
% 46.94/6.50  --bmc1_ground_init                      false
% 46.94/6.50  --bmc1_pre_inst_next_state              false
% 46.94/6.50  --bmc1_pre_inst_state                   false
% 46.94/6.50  --bmc1_pre_inst_reach_state             false
% 46.94/6.50  --bmc1_out_unsat_core                   false
% 46.94/6.50  --bmc1_aig_witness_out                  false
% 46.94/6.50  --bmc1_verbose                          false
% 46.94/6.50  --bmc1_dump_clauses_tptp                false
% 46.94/6.50  --bmc1_dump_unsat_core_tptp             false
% 46.94/6.50  --bmc1_dump_file                        -
% 46.94/6.50  --bmc1_ucm_expand_uc_limit              128
% 46.94/6.50  --bmc1_ucm_n_expand_iterations          6
% 46.94/6.50  --bmc1_ucm_extend_mode                  1
% 46.94/6.50  --bmc1_ucm_init_mode                    2
% 46.94/6.50  --bmc1_ucm_cone_mode                    none
% 46.94/6.50  --bmc1_ucm_reduced_relation_type        0
% 46.94/6.50  --bmc1_ucm_relax_model                  4
% 46.94/6.50  --bmc1_ucm_full_tr_after_sat            true
% 46.94/6.50  --bmc1_ucm_expand_neg_assumptions       false
% 46.94/6.50  --bmc1_ucm_layered_model                none
% 46.94/6.50  --bmc1_ucm_max_lemma_size               10
% 46.94/6.50  
% 46.94/6.50  ------ AIG Options
% 46.94/6.50  
% 46.94/6.50  --aig_mode                              false
% 46.94/6.50  
% 46.94/6.50  ------ Instantiation Options
% 46.94/6.50  
% 46.94/6.50  --instantiation_flag                    true
% 46.94/6.50  --inst_sos_flag                         true
% 46.94/6.50  --inst_sos_phase                        true
% 46.94/6.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 46.94/6.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 46.94/6.50  --inst_lit_sel_side                     num_symb
% 46.94/6.50  --inst_solver_per_active                1400
% 46.94/6.50  --inst_solver_calls_frac                1.
% 46.94/6.50  --inst_passive_queue_type               priority_queues
% 46.94/6.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 46.94/6.50  --inst_passive_queues_freq              [25;2]
% 46.94/6.50  --inst_dismatching                      true
% 46.94/6.50  --inst_eager_unprocessed_to_passive     true
% 46.94/6.50  --inst_prop_sim_given                   true
% 46.94/6.50  --inst_prop_sim_new                     false
% 46.94/6.50  --inst_subs_new                         false
% 46.94/6.50  --inst_eq_res_simp                      false
% 46.94/6.50  --inst_subs_given                       false
% 46.94/6.50  --inst_orphan_elimination               true
% 46.94/6.50  --inst_learning_loop_flag               true
% 46.94/6.50  --inst_learning_start                   3000
% 46.94/6.50  --inst_learning_factor                  2
% 46.94/6.50  --inst_start_prop_sim_after_learn       3
% 46.94/6.50  --inst_sel_renew                        solver
% 46.94/6.50  --inst_lit_activity_flag                true
% 46.94/6.50  --inst_restr_to_given                   false
% 46.94/6.50  --inst_activity_threshold               500
% 46.94/6.50  --inst_out_proof                        true
% 46.94/6.50  
% 46.94/6.50  ------ Resolution Options
% 46.94/6.50  
% 46.94/6.50  --resolution_flag                       true
% 46.94/6.50  --res_lit_sel                           adaptive
% 46.94/6.50  --res_lit_sel_side                      none
% 46.94/6.50  --res_ordering                          kbo
% 46.94/6.50  --res_to_prop_solver                    active
% 46.94/6.50  --res_prop_simpl_new                    false
% 46.94/6.50  --res_prop_simpl_given                  true
% 46.94/6.50  --res_passive_queue_type                priority_queues
% 46.94/6.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 46.94/6.50  --res_passive_queues_freq               [15;5]
% 46.94/6.50  --res_forward_subs                      full
% 46.94/6.50  --res_backward_subs                     full
% 46.94/6.50  --res_forward_subs_resolution           true
% 46.94/6.50  --res_backward_subs_resolution          true
% 46.94/6.50  --res_orphan_elimination                true
% 46.94/6.50  --res_time_limit                        2.
% 46.94/6.50  --res_out_proof                         true
% 46.94/6.50  
% 46.94/6.50  ------ Superposition Options
% 46.94/6.50  
% 46.94/6.50  --superposition_flag                    true
% 46.94/6.50  --sup_passive_queue_type                priority_queues
% 46.94/6.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 46.94/6.50  --sup_passive_queues_freq               [8;1;4]
% 46.94/6.50  --demod_completeness_check              fast
% 46.94/6.50  --demod_use_ground                      true
% 46.94/6.50  --sup_to_prop_solver                    passive
% 46.94/6.50  --sup_prop_simpl_new                    true
% 46.94/6.50  --sup_prop_simpl_given                  true
% 46.94/6.50  --sup_fun_splitting                     true
% 46.94/6.50  --sup_smt_interval                      50000
% 46.94/6.50  
% 46.94/6.50  ------ Superposition Simplification Setup
% 46.94/6.50  
% 46.94/6.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 46.94/6.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 46.94/6.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 46.94/6.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 46.94/6.50  --sup_full_triv                         [TrivRules;PropSubs]
% 46.94/6.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 46.94/6.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 46.94/6.50  --sup_immed_triv                        [TrivRules]
% 46.94/6.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 46.94/6.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 46.94/6.50  --sup_immed_bw_main                     []
% 46.94/6.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 46.94/6.50  --sup_input_triv                        [Unflattening;TrivRules]
% 46.94/6.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 46.94/6.50  --sup_input_bw                          []
% 46.94/6.50  
% 46.94/6.50  ------ Combination Options
% 46.94/6.50  
% 46.94/6.50  --comb_res_mult                         3
% 46.94/6.50  --comb_sup_mult                         2
% 46.94/6.50  --comb_inst_mult                        10
% 46.94/6.50  
% 46.94/6.50  ------ Debug Options
% 46.94/6.50  
% 46.94/6.50  --dbg_backtrace                         false
% 46.94/6.50  --dbg_dump_prop_clauses                 false
% 46.94/6.50  --dbg_dump_prop_clauses_file            -
% 46.94/6.50  --dbg_out_stat                          false
% 46.94/6.50  ------ Parsing...
% 46.94/6.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 46.94/6.50  
% 46.94/6.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 46.94/6.50  
% 46.94/6.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 46.94/6.50  
% 46.94/6.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 46.94/6.50  ------ Proving...
% 46.94/6.50  ------ Problem Properties 
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  clauses                                 55
% 46.94/6.50  conjectures                             11
% 46.94/6.50  EPR                                     7
% 46.94/6.50  Horn                                    51
% 46.94/6.50  unary                                   18
% 46.94/6.50  binary                                  9
% 46.94/6.50  lits                                    198
% 46.94/6.50  lits eq                                 44
% 46.94/6.50  fd_pure                                 0
% 46.94/6.50  fd_pseudo                               0
% 46.94/6.50  fd_cond                                 4
% 46.94/6.50  fd_pseudo_cond                          1
% 46.94/6.50  AC symbols                              0
% 46.94/6.50  
% 46.94/6.50  ------ Schedule dynamic 5 is on 
% 46.94/6.50  
% 46.94/6.50  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  ------ 
% 46.94/6.50  Current options:
% 46.94/6.50  ------ 
% 46.94/6.50  
% 46.94/6.50  ------ Input Options
% 46.94/6.50  
% 46.94/6.50  --out_options                           all
% 46.94/6.50  --tptp_safe_out                         true
% 46.94/6.50  --problem_path                          ""
% 46.94/6.50  --include_path                          ""
% 46.94/6.50  --clausifier                            res/vclausify_rel
% 46.94/6.50  --clausifier_options                    ""
% 46.94/6.50  --stdin                                 false
% 46.94/6.50  --stats_out                             all
% 46.94/6.50  
% 46.94/6.50  ------ General Options
% 46.94/6.50  
% 46.94/6.50  --fof                                   false
% 46.94/6.50  --time_out_real                         305.
% 46.94/6.50  --time_out_virtual                      -1.
% 46.94/6.50  --symbol_type_check                     false
% 46.94/6.50  --clausify_out                          false
% 46.94/6.50  --sig_cnt_out                           false
% 46.94/6.50  --trig_cnt_out                          false
% 46.94/6.50  --trig_cnt_out_tolerance                1.
% 46.94/6.50  --trig_cnt_out_sk_spl                   false
% 46.94/6.50  --abstr_cl_out                          false
% 46.94/6.50  
% 46.94/6.50  ------ Global Options
% 46.94/6.50  
% 46.94/6.50  --schedule                              default
% 46.94/6.50  --add_important_lit                     false
% 46.94/6.50  --prop_solver_per_cl                    1000
% 46.94/6.50  --min_unsat_core                        false
% 46.94/6.50  --soft_assumptions                      false
% 46.94/6.50  --soft_lemma_size                       3
% 46.94/6.50  --prop_impl_unit_size                   0
% 46.94/6.50  --prop_impl_unit                        []
% 46.94/6.50  --share_sel_clauses                     true
% 46.94/6.50  --reset_solvers                         false
% 46.94/6.50  --bc_imp_inh                            [conj_cone]
% 46.94/6.50  --conj_cone_tolerance                   3.
% 46.94/6.50  --extra_neg_conj                        none
% 46.94/6.50  --large_theory_mode                     true
% 46.94/6.50  --prolific_symb_bound                   200
% 46.94/6.50  --lt_threshold                          2000
% 46.94/6.50  --clause_weak_htbl                      true
% 46.94/6.50  --gc_record_bc_elim                     false
% 46.94/6.50  
% 46.94/6.50  ------ Preprocessing Options
% 46.94/6.50  
% 46.94/6.50  --preprocessing_flag                    true
% 46.94/6.50  --time_out_prep_mult                    0.1
% 46.94/6.50  --splitting_mode                        input
% 46.94/6.50  --splitting_grd                         true
% 46.94/6.50  --splitting_cvd                         false
% 46.94/6.50  --splitting_cvd_svl                     false
% 46.94/6.50  --splitting_nvd                         32
% 46.94/6.50  --sub_typing                            true
% 46.94/6.50  --prep_gs_sim                           true
% 46.94/6.50  --prep_unflatten                        true
% 46.94/6.50  --prep_res_sim                          true
% 46.94/6.50  --prep_upred                            true
% 46.94/6.50  --prep_sem_filter                       exhaustive
% 46.94/6.50  --prep_sem_filter_out                   false
% 46.94/6.50  --pred_elim                             true
% 46.94/6.50  --res_sim_input                         true
% 46.94/6.50  --eq_ax_congr_red                       true
% 46.94/6.50  --pure_diseq_elim                       true
% 46.94/6.50  --brand_transform                       false
% 46.94/6.50  --non_eq_to_eq                          false
% 46.94/6.50  --prep_def_merge                        true
% 46.94/6.50  --prep_def_merge_prop_impl              false
% 46.94/6.50  --prep_def_merge_mbd                    true
% 46.94/6.50  --prep_def_merge_tr_red                 false
% 46.94/6.50  --prep_def_merge_tr_cl                  false
% 46.94/6.50  --smt_preprocessing                     true
% 46.94/6.50  --smt_ac_axioms                         fast
% 46.94/6.50  --preprocessed_out                      false
% 46.94/6.50  --preprocessed_stats                    false
% 46.94/6.50  
% 46.94/6.50  ------ Abstraction refinement Options
% 46.94/6.50  
% 46.94/6.50  --abstr_ref                             []
% 46.94/6.50  --abstr_ref_prep                        false
% 46.94/6.50  --abstr_ref_until_sat                   false
% 46.94/6.50  --abstr_ref_sig_restrict                funpre
% 46.94/6.50  --abstr_ref_af_restrict_to_split_sk     false
% 46.94/6.50  --abstr_ref_under                       []
% 46.94/6.50  
% 46.94/6.50  ------ SAT Options
% 46.94/6.50  
% 46.94/6.50  --sat_mode                              false
% 46.94/6.50  --sat_fm_restart_options                ""
% 46.94/6.50  --sat_gr_def                            false
% 46.94/6.50  --sat_epr_types                         true
% 46.94/6.50  --sat_non_cyclic_types                  false
% 46.94/6.50  --sat_finite_models                     false
% 46.94/6.50  --sat_fm_lemmas                         false
% 46.94/6.50  --sat_fm_prep                           false
% 46.94/6.50  --sat_fm_uc_incr                        true
% 46.94/6.50  --sat_out_model                         small
% 46.94/6.50  --sat_out_clauses                       false
% 46.94/6.50  
% 46.94/6.50  ------ QBF Options
% 46.94/6.50  
% 46.94/6.50  --qbf_mode                              false
% 46.94/6.50  --qbf_elim_univ                         false
% 46.94/6.50  --qbf_dom_inst                          none
% 46.94/6.50  --qbf_dom_pre_inst                      false
% 46.94/6.50  --qbf_sk_in                             false
% 46.94/6.50  --qbf_pred_elim                         true
% 46.94/6.50  --qbf_split                             512
% 46.94/6.50  
% 46.94/6.50  ------ BMC1 Options
% 46.94/6.50  
% 46.94/6.50  --bmc1_incremental                      false
% 46.94/6.50  --bmc1_axioms                           reachable_all
% 46.94/6.50  --bmc1_min_bound                        0
% 46.94/6.50  --bmc1_max_bound                        -1
% 46.94/6.50  --bmc1_max_bound_default                -1
% 46.94/6.50  --bmc1_symbol_reachability              true
% 46.94/6.50  --bmc1_property_lemmas                  false
% 46.94/6.50  --bmc1_k_induction                      false
% 46.94/6.50  --bmc1_non_equiv_states                 false
% 46.94/6.50  --bmc1_deadlock                         false
% 46.94/6.50  --bmc1_ucm                              false
% 46.94/6.50  --bmc1_add_unsat_core                   none
% 46.94/6.50  --bmc1_unsat_core_children              false
% 46.94/6.50  --bmc1_unsat_core_extrapolate_axioms    false
% 46.94/6.50  --bmc1_out_stat                         full
% 46.94/6.50  --bmc1_ground_init                      false
% 46.94/6.50  --bmc1_pre_inst_next_state              false
% 46.94/6.50  --bmc1_pre_inst_state                   false
% 46.94/6.50  --bmc1_pre_inst_reach_state             false
% 46.94/6.50  --bmc1_out_unsat_core                   false
% 46.94/6.50  --bmc1_aig_witness_out                  false
% 46.94/6.50  --bmc1_verbose                          false
% 46.94/6.50  --bmc1_dump_clauses_tptp                false
% 46.94/6.50  --bmc1_dump_unsat_core_tptp             false
% 46.94/6.50  --bmc1_dump_file                        -
% 46.94/6.50  --bmc1_ucm_expand_uc_limit              128
% 46.94/6.50  --bmc1_ucm_n_expand_iterations          6
% 46.94/6.50  --bmc1_ucm_extend_mode                  1
% 46.94/6.50  --bmc1_ucm_init_mode                    2
% 46.94/6.50  --bmc1_ucm_cone_mode                    none
% 46.94/6.50  --bmc1_ucm_reduced_relation_type        0
% 46.94/6.50  --bmc1_ucm_relax_model                  4
% 46.94/6.50  --bmc1_ucm_full_tr_after_sat            true
% 46.94/6.50  --bmc1_ucm_expand_neg_assumptions       false
% 46.94/6.50  --bmc1_ucm_layered_model                none
% 46.94/6.50  --bmc1_ucm_max_lemma_size               10
% 46.94/6.50  
% 46.94/6.50  ------ AIG Options
% 46.94/6.50  
% 46.94/6.50  --aig_mode                              false
% 46.94/6.50  
% 46.94/6.50  ------ Instantiation Options
% 46.94/6.50  
% 46.94/6.50  --instantiation_flag                    true
% 46.94/6.50  --inst_sos_flag                         true
% 46.94/6.50  --inst_sos_phase                        true
% 46.94/6.50  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 46.94/6.50  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 46.94/6.50  --inst_lit_sel_side                     none
% 46.94/6.50  --inst_solver_per_active                1400
% 46.94/6.50  --inst_solver_calls_frac                1.
% 46.94/6.50  --inst_passive_queue_type               priority_queues
% 46.94/6.50  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 46.94/6.50  --inst_passive_queues_freq              [25;2]
% 46.94/6.50  --inst_dismatching                      true
% 46.94/6.50  --inst_eager_unprocessed_to_passive     true
% 46.94/6.50  --inst_prop_sim_given                   true
% 46.94/6.50  --inst_prop_sim_new                     false
% 46.94/6.50  --inst_subs_new                         false
% 46.94/6.50  --inst_eq_res_simp                      false
% 46.94/6.50  --inst_subs_given                       false
% 46.94/6.50  --inst_orphan_elimination               true
% 46.94/6.50  --inst_learning_loop_flag               true
% 46.94/6.50  --inst_learning_start                   3000
% 46.94/6.50  --inst_learning_factor                  2
% 46.94/6.50  --inst_start_prop_sim_after_learn       3
% 46.94/6.50  --inst_sel_renew                        solver
% 46.94/6.50  --inst_lit_activity_flag                true
% 46.94/6.50  --inst_restr_to_given                   false
% 46.94/6.50  --inst_activity_threshold               500
% 46.94/6.50  --inst_out_proof                        true
% 46.94/6.50  
% 46.94/6.50  ------ Resolution Options
% 46.94/6.50  
% 46.94/6.50  --resolution_flag                       false
% 46.94/6.50  --res_lit_sel                           adaptive
% 46.94/6.50  --res_lit_sel_side                      none
% 46.94/6.50  --res_ordering                          kbo
% 46.94/6.50  --res_to_prop_solver                    active
% 46.94/6.50  --res_prop_simpl_new                    false
% 46.94/6.50  --res_prop_simpl_given                  true
% 46.94/6.50  --res_passive_queue_type                priority_queues
% 46.94/6.50  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 46.94/6.50  --res_passive_queues_freq               [15;5]
% 46.94/6.50  --res_forward_subs                      full
% 46.94/6.50  --res_backward_subs                     full
% 46.94/6.50  --res_forward_subs_resolution           true
% 46.94/6.50  --res_backward_subs_resolution          true
% 46.94/6.50  --res_orphan_elimination                true
% 46.94/6.50  --res_time_limit                        2.
% 46.94/6.50  --res_out_proof                         true
% 46.94/6.50  
% 46.94/6.50  ------ Superposition Options
% 46.94/6.50  
% 46.94/6.50  --superposition_flag                    true
% 46.94/6.50  --sup_passive_queue_type                priority_queues
% 46.94/6.50  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 46.94/6.50  --sup_passive_queues_freq               [8;1;4]
% 46.94/6.50  --demod_completeness_check              fast
% 46.94/6.50  --demod_use_ground                      true
% 46.94/6.50  --sup_to_prop_solver                    passive
% 46.94/6.50  --sup_prop_simpl_new                    true
% 46.94/6.50  --sup_prop_simpl_given                  true
% 46.94/6.50  --sup_fun_splitting                     true
% 46.94/6.50  --sup_smt_interval                      50000
% 46.94/6.50  
% 46.94/6.50  ------ Superposition Simplification Setup
% 46.94/6.50  
% 46.94/6.50  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 46.94/6.50  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 46.94/6.50  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 46.94/6.50  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 46.94/6.50  --sup_full_triv                         [TrivRules;PropSubs]
% 46.94/6.50  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 46.94/6.50  --sup_full_bw                           [BwDemod;BwSubsumption]
% 46.94/6.50  --sup_immed_triv                        [TrivRules]
% 46.94/6.50  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 46.94/6.50  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 46.94/6.50  --sup_immed_bw_main                     []
% 46.94/6.50  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 46.94/6.50  --sup_input_triv                        [Unflattening;TrivRules]
% 46.94/6.50  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 46.94/6.50  --sup_input_bw                          []
% 46.94/6.50  
% 46.94/6.50  ------ Combination Options
% 46.94/6.50  
% 46.94/6.50  --comb_res_mult                         3
% 46.94/6.50  --comb_sup_mult                         2
% 46.94/6.50  --comb_inst_mult                        10
% 46.94/6.50  
% 46.94/6.50  ------ Debug Options
% 46.94/6.50  
% 46.94/6.50  --dbg_backtrace                         false
% 46.94/6.50  --dbg_dump_prop_clauses                 false
% 46.94/6.50  --dbg_dump_prop_clauses_file            -
% 46.94/6.50  --dbg_out_stat                          false
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  ------ Proving...
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  % SZS status Theorem for theBenchmark.p
% 46.94/6.50  
% 46.94/6.50  % SZS output start CNFRefutation for theBenchmark.p
% 46.94/6.50  
% 46.94/6.50  fof(f32,conjecture,(
% 46.94/6.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f33,negated_conjecture,(
% 46.94/6.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 46.94/6.50    inference(negated_conjecture,[],[f32])).
% 46.94/6.50  
% 46.94/6.50  fof(f76,plain,(
% 46.94/6.50    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 46.94/6.50    inference(ennf_transformation,[],[f33])).
% 46.94/6.50  
% 46.94/6.50  fof(f77,plain,(
% 46.94/6.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 46.94/6.50    inference(flattening,[],[f76])).
% 46.94/6.50  
% 46.94/6.50  fof(f80,plain,(
% 46.94/6.50    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 46.94/6.50    introduced(choice_axiom,[])).
% 46.94/6.50  
% 46.94/6.50  fof(f79,plain,(
% 46.94/6.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 46.94/6.50    introduced(choice_axiom,[])).
% 46.94/6.50  
% 46.94/6.50  fof(f81,plain,(
% 46.94/6.50    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 46.94/6.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f77,f80,f79])).
% 46.94/6.50  
% 46.94/6.50  fof(f134,plain,(
% 46.94/6.50    v1_funct_1(sK3)),
% 46.94/6.50    inference(cnf_transformation,[],[f81])).
% 46.94/6.50  
% 46.94/6.50  fof(f31,axiom,(
% 46.94/6.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f74,plain,(
% 46.94/6.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 46.94/6.50    inference(ennf_transformation,[],[f31])).
% 46.94/6.50  
% 46.94/6.50  fof(f75,plain,(
% 46.94/6.50    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 46.94/6.50    inference(flattening,[],[f74])).
% 46.94/6.50  
% 46.94/6.50  fof(f130,plain,(
% 46.94/6.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f75])).
% 46.94/6.50  
% 46.94/6.50  fof(f21,axiom,(
% 46.94/6.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f59,plain,(
% 46.94/6.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 46.94/6.50    inference(ennf_transformation,[],[f21])).
% 46.94/6.50  
% 46.94/6.50  fof(f110,plain,(
% 46.94/6.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 46.94/6.50    inference(cnf_transformation,[],[f59])).
% 46.94/6.50  
% 46.94/6.50  fof(f136,plain,(
% 46.94/6.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 46.94/6.50    inference(cnf_transformation,[],[f81])).
% 46.94/6.50  
% 46.94/6.50  fof(f27,axiom,(
% 46.94/6.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f66,plain,(
% 46.94/6.50    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 46.94/6.50    inference(ennf_transformation,[],[f27])).
% 46.94/6.50  
% 46.94/6.50  fof(f67,plain,(
% 46.94/6.50    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 46.94/6.50    inference(flattening,[],[f66])).
% 46.94/6.50  
% 46.94/6.50  fof(f118,plain,(
% 46.94/6.50    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f67])).
% 46.94/6.50  
% 46.94/6.50  fof(f138,plain,(
% 46.94/6.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 46.94/6.50    inference(cnf_transformation,[],[f81])).
% 46.94/6.50  
% 46.94/6.50  fof(f131,plain,(
% 46.94/6.50    v1_funct_1(sK2)),
% 46.94/6.50    inference(cnf_transformation,[],[f81])).
% 46.94/6.50  
% 46.94/6.50  fof(f132,plain,(
% 46.94/6.50    v1_funct_2(sK2,sK0,sK1)),
% 46.94/6.50    inference(cnf_transformation,[],[f81])).
% 46.94/6.50  
% 46.94/6.50  fof(f133,plain,(
% 46.94/6.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 46.94/6.50    inference(cnf_transformation,[],[f81])).
% 46.94/6.50  
% 46.94/6.50  fof(f135,plain,(
% 46.94/6.50    v1_funct_2(sK3,sK1,sK0)),
% 46.94/6.50    inference(cnf_transformation,[],[f81])).
% 46.94/6.50  
% 46.94/6.50  fof(f1,axiom,(
% 46.94/6.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f34,plain,(
% 46.94/6.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 46.94/6.50    inference(ennf_transformation,[],[f1])).
% 46.94/6.50  
% 46.94/6.50  fof(f82,plain,(
% 46.94/6.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f34])).
% 46.94/6.50  
% 46.94/6.50  fof(f2,axiom,(
% 46.94/6.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f83,plain,(
% 46.94/6.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 46.94/6.50    inference(cnf_transformation,[],[f2])).
% 46.94/6.50  
% 46.94/6.50  fof(f30,axiom,(
% 46.94/6.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f72,plain,(
% 46.94/6.50    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 46.94/6.50    inference(ennf_transformation,[],[f30])).
% 46.94/6.50  
% 46.94/6.50  fof(f73,plain,(
% 46.94/6.50    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 46.94/6.50    inference(flattening,[],[f72])).
% 46.94/6.50  
% 46.94/6.50  fof(f126,plain,(
% 46.94/6.50    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f73])).
% 46.94/6.50  
% 46.94/6.50  fof(f13,axiom,(
% 46.94/6.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f99,plain,(
% 46.94/6.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 46.94/6.50    inference(cnf_transformation,[],[f13])).
% 46.94/6.50  
% 46.94/6.50  fof(f26,axiom,(
% 46.94/6.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f117,plain,(
% 46.94/6.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f26])).
% 46.94/6.50  
% 46.94/6.50  fof(f149,plain,(
% 46.94/6.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 46.94/6.50    inference(definition_unfolding,[],[f99,f117])).
% 46.94/6.50  
% 46.94/6.50  fof(f22,axiom,(
% 46.94/6.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f60,plain,(
% 46.94/6.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 46.94/6.50    inference(ennf_transformation,[],[f22])).
% 46.94/6.50  
% 46.94/6.50  fof(f61,plain,(
% 46.94/6.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 46.94/6.50    inference(flattening,[],[f60])).
% 46.94/6.50  
% 46.94/6.50  fof(f78,plain,(
% 46.94/6.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 46.94/6.50    inference(nnf_transformation,[],[f61])).
% 46.94/6.50  
% 46.94/6.50  fof(f111,plain,(
% 46.94/6.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 46.94/6.50    inference(cnf_transformation,[],[f78])).
% 46.94/6.50  
% 46.94/6.50  fof(f23,axiom,(
% 46.94/6.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f113,plain,(
% 46.94/6.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 46.94/6.50    inference(cnf_transformation,[],[f23])).
% 46.94/6.50  
% 46.94/6.50  fof(f152,plain,(
% 46.94/6.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 46.94/6.50    inference(definition_unfolding,[],[f113,f117])).
% 46.94/6.50  
% 46.94/6.50  fof(f24,axiom,(
% 46.94/6.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f62,plain,(
% 46.94/6.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 46.94/6.50    inference(ennf_transformation,[],[f24])).
% 46.94/6.50  
% 46.94/6.50  fof(f63,plain,(
% 46.94/6.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 46.94/6.50    inference(flattening,[],[f62])).
% 46.94/6.50  
% 46.94/6.50  fof(f115,plain,(
% 46.94/6.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f63])).
% 46.94/6.50  
% 46.94/6.50  fof(f137,plain,(
% 46.94/6.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 46.94/6.50    inference(cnf_transformation,[],[f81])).
% 46.94/6.50  
% 46.94/6.50  fof(f28,axiom,(
% 46.94/6.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f68,plain,(
% 46.94/6.50    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 46.94/6.50    inference(ennf_transformation,[],[f28])).
% 46.94/6.50  
% 46.94/6.50  fof(f69,plain,(
% 46.94/6.50    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 46.94/6.50    inference(flattening,[],[f68])).
% 46.94/6.50  
% 46.94/6.50  fof(f121,plain,(
% 46.94/6.50    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f69])).
% 46.94/6.50  
% 46.94/6.50  fof(f140,plain,(
% 46.94/6.50    k1_xboole_0 != sK0),
% 46.94/6.50    inference(cnf_transformation,[],[f81])).
% 46.94/6.50  
% 46.94/6.50  fof(f10,axiom,(
% 46.94/6.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f41,plain,(
% 46.94/6.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 46.94/6.50    inference(ennf_transformation,[],[f10])).
% 46.94/6.50  
% 46.94/6.50  fof(f42,plain,(
% 46.94/6.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 46.94/6.50    inference(flattening,[],[f41])).
% 46.94/6.50  
% 46.94/6.50  fof(f93,plain,(
% 46.94/6.50    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f42])).
% 46.94/6.50  
% 46.94/6.50  fof(f129,plain,(
% 46.94/6.50    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f75])).
% 46.94/6.50  
% 46.94/6.50  fof(f7,axiom,(
% 46.94/6.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f90,plain,(
% 46.94/6.50    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 46.94/6.50    inference(cnf_transformation,[],[f7])).
% 46.94/6.50  
% 46.94/6.50  fof(f143,plain,(
% 46.94/6.50    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 46.94/6.50    inference(definition_unfolding,[],[f90,f117])).
% 46.94/6.50  
% 46.94/6.50  fof(f25,axiom,(
% 46.94/6.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f64,plain,(
% 46.94/6.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 46.94/6.50    inference(ennf_transformation,[],[f25])).
% 46.94/6.50  
% 46.94/6.50  fof(f65,plain,(
% 46.94/6.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 46.94/6.50    inference(flattening,[],[f64])).
% 46.94/6.50  
% 46.94/6.50  fof(f116,plain,(
% 46.94/6.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f65])).
% 46.94/6.50  
% 46.94/6.50  fof(f18,axiom,(
% 46.94/6.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f53,plain,(
% 46.94/6.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 46.94/6.50    inference(ennf_transformation,[],[f18])).
% 46.94/6.50  
% 46.94/6.50  fof(f54,plain,(
% 46.94/6.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 46.94/6.50    inference(flattening,[],[f53])).
% 46.94/6.50  
% 46.94/6.50  fof(f107,plain,(
% 46.94/6.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f54])).
% 46.94/6.50  
% 46.94/6.50  fof(f151,plain,(
% 46.94/6.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 46.94/6.50    inference(definition_unfolding,[],[f107,f117])).
% 46.94/6.50  
% 46.94/6.50  fof(f3,axiom,(
% 46.94/6.50    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 46.94/6.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 46.94/6.50  
% 46.94/6.50  fof(f35,plain,(
% 46.94/6.50    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 46.94/6.50    inference(ennf_transformation,[],[f3])).
% 46.94/6.50  
% 46.94/6.50  fof(f84,plain,(
% 46.94/6.50    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 46.94/6.50    inference(cnf_transformation,[],[f35])).
% 46.94/6.50  
% 46.94/6.50  fof(f142,plain,(
% 46.94/6.50    k2_funct_1(sK2) != sK3),
% 46.94/6.50    inference(cnf_transformation,[],[f81])).
% 46.94/6.50  
% 46.94/6.50  fof(f139,plain,(
% 46.94/6.50    v2_funct_1(sK2)),
% 46.94/6.50    inference(cnf_transformation,[],[f81])).
% 46.94/6.50  
% 46.94/6.50  cnf(c_56,negated_conjecture,
% 46.94/6.50      ( v1_funct_1(sK3) ),
% 46.94/6.50      inference(cnf_transformation,[],[f134]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1797,plain,
% 46.94/6.50      ( v1_funct_1(sK3) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_45,plain,
% 46.94/6.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 46.94/6.50      | ~ v1_funct_1(X0)
% 46.94/6.50      | ~ v1_relat_1(X0) ),
% 46.94/6.50      inference(cnf_transformation,[],[f130]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1802,plain,
% 46.94/6.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 46.94/6.50      | v1_funct_1(X0) != iProver_top
% 46.94/6.50      | v1_relat_1(X0) != iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_28,plain,
% 46.94/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.94/6.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 46.94/6.50      inference(cnf_transformation,[],[f110]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1816,plain,
% 46.94/6.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 46.94/6.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_3976,plain,
% 46.94/6.50      ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
% 46.94/6.50      | v1_funct_1(X0) != iProver_top
% 46.94/6.50      | v1_relat_1(X0) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_1802,c_1816]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_10164,plain,
% 46.94/6.50      ( k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) = k2_relat_1(sK3)
% 46.94/6.50      | v1_relat_1(sK3) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_1797,c_3976]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_54,negated_conjecture,
% 46.94/6.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 46.94/6.50      inference(cnf_transformation,[],[f136]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1799,plain,
% 46.94/6.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_3923,plain,
% 46.94/6.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_1799,c_1816]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_35,plain,
% 46.94/6.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 46.94/6.50      | ~ v1_funct_2(X2,X0,X1)
% 46.94/6.50      | ~ v1_funct_2(X3,X1,X0)
% 46.94/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 46.94/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 46.94/6.50      | ~ v1_funct_1(X2)
% 46.94/6.50      | ~ v1_funct_1(X3)
% 46.94/6.50      | k2_relset_1(X1,X0,X3) = X0 ),
% 46.94/6.50      inference(cnf_transformation,[],[f118]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_52,negated_conjecture,
% 46.94/6.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 46.94/6.50      inference(cnf_transformation,[],[f138]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_647,plain,
% 46.94/6.50      ( ~ v1_funct_2(X0,X1,X2)
% 46.94/6.50      | ~ v1_funct_2(X3,X2,X1)
% 46.94/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 46.94/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.94/6.50      | ~ v1_funct_1(X3)
% 46.94/6.50      | ~ v1_funct_1(X0)
% 46.94/6.50      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 46.94/6.50      | k2_relset_1(X2,X1,X3) = X1
% 46.94/6.50      | k6_partfun1(X1) != k6_partfun1(sK0)
% 46.94/6.50      | sK0 != X1 ),
% 46.94/6.50      inference(resolution_lifted,[status(thm)],[c_35,c_52]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_648,plain,
% 46.94/6.50      ( ~ v1_funct_2(X0,X1,sK0)
% 46.94/6.50      | ~ v1_funct_2(X2,sK0,X1)
% 46.94/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 46.94/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 46.94/6.50      | ~ v1_funct_1(X2)
% 46.94/6.50      | ~ v1_funct_1(X0)
% 46.94/6.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 46.94/6.50      | k2_relset_1(X1,sK0,X0) = sK0
% 46.94/6.50      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 46.94/6.50      inference(unflattening,[status(thm)],[c_647]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_751,plain,
% 46.94/6.50      ( ~ v1_funct_2(X0,X1,sK0)
% 46.94/6.50      | ~ v1_funct_2(X2,sK0,X1)
% 46.94/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 46.94/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 46.94/6.50      | ~ v1_funct_1(X0)
% 46.94/6.50      | ~ v1_funct_1(X2)
% 46.94/6.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 46.94/6.50      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 46.94/6.50      inference(equality_resolution_simp,[status(thm)],[c_648]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1791,plain,
% 46.94/6.50      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 46.94/6.50      | k2_relset_1(X0,sK0,X2) = sK0
% 46.94/6.50      | v1_funct_2(X2,X0,sK0) != iProver_top
% 46.94/6.50      | v1_funct_2(X1,sK0,X0) != iProver_top
% 46.94/6.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 46.94/6.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 46.94/6.50      | v1_funct_1(X2) != iProver_top
% 46.94/6.50      | v1_funct_1(X1) != iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2406,plain,
% 46.94/6.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 46.94/6.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 46.94/6.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 46.94/6.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 46.94/6.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 46.94/6.50      | v1_funct_1(sK3) != iProver_top
% 46.94/6.50      | v1_funct_1(sK2) != iProver_top ),
% 46.94/6.50      inference(equality_resolution,[status(thm)],[c_1791]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_59,negated_conjecture,
% 46.94/6.50      ( v1_funct_1(sK2) ),
% 46.94/6.50      inference(cnf_transformation,[],[f131]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_60,plain,
% 46.94/6.50      ( v1_funct_1(sK2) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_58,negated_conjecture,
% 46.94/6.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 46.94/6.50      inference(cnf_transformation,[],[f132]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_61,plain,
% 46.94/6.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_57,negated_conjecture,
% 46.94/6.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 46.94/6.50      inference(cnf_transformation,[],[f133]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_62,plain,
% 46.94/6.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_63,plain,
% 46.94/6.50      ( v1_funct_1(sK3) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_55,negated_conjecture,
% 46.94/6.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 46.94/6.50      inference(cnf_transformation,[],[f135]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_64,plain,
% 46.94/6.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_65,plain,
% 46.94/6.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2661,plain,
% 46.94/6.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 46.94/6.50      inference(global_propositional_subsumption,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_2406,c_60,c_61,c_62,c_63,c_64,c_65]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_3926,plain,
% 46.94/6.50      ( k2_relat_1(sK3) = sK0 ),
% 46.94/6.50      inference(light_normalisation,[status(thm)],[c_3923,c_2661]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_10173,plain,
% 46.94/6.50      ( k2_relset_1(k1_relat_1(sK3),sK0,sK3) = sK0
% 46.94/6.50      | v1_relat_1(sK3) != iProver_top ),
% 46.94/6.50      inference(light_normalisation,[status(thm)],[c_10164,c_3926]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_0,plain,
% 46.94/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 46.94/6.50      | ~ v1_relat_1(X1)
% 46.94/6.50      | v1_relat_1(X0) ),
% 46.94/6.50      inference(cnf_transformation,[],[f82]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2000,plain,
% 46.94/6.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 46.94/6.50      | ~ v1_relat_1(X0)
% 46.94/6.50      | v1_relat_1(sK3) ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_0]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2373,plain,
% 46.94/6.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 46.94/6.50      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 46.94/6.50      | v1_relat_1(sK3) ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_2000]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2994,plain,
% 46.94/6.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 46.94/6.50      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 46.94/6.50      | v1_relat_1(sK3) ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_2373]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2995,plain,
% 46.94/6.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 46.94/6.50      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 46.94/6.50      | v1_relat_1(sK3) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_2994]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1,plain,
% 46.94/6.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 46.94/6.50      inference(cnf_transformation,[],[f83]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_3496,plain,
% 46.94/6.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_1]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_3497,plain,
% 46.94/6.50      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_3496]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_10740,plain,
% 46.94/6.50      ( k2_relset_1(k1_relat_1(sK3),sK0,sK3) = sK0 ),
% 46.94/6.50      inference(global_propositional_subsumption,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_10173,c_65,c_2995,c_3497]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_44,plain,
% 46.94/6.50      ( ~ v1_funct_2(X0,X1,X2)
% 46.94/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.94/6.50      | ~ v1_funct_1(X0)
% 46.94/6.50      | ~ v2_funct_1(X0)
% 46.94/6.50      | k2_relset_1(X1,X2,X0) != X2
% 46.94/6.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 46.94/6.50      | k1_xboole_0 = X2 ),
% 46.94/6.50      inference(cnf_transformation,[],[f126]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1803,plain,
% 46.94/6.50      ( k2_relset_1(X0,X1,X2) != X1
% 46.94/6.50      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 46.94/6.50      | k1_xboole_0 = X1
% 46.94/6.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 46.94/6.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.94/6.50      | v1_funct_1(X2) != iProver_top
% 46.94/6.50      | v2_funct_1(X2) != iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_10748,plain,
% 46.94/6.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 46.94/6.50      | sK0 = k1_xboole_0
% 46.94/6.50      | v1_funct_2(sK3,k1_relat_1(sK3),sK0) != iProver_top
% 46.94/6.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) != iProver_top
% 46.94/6.50      | v1_funct_1(sK3) != iProver_top
% 46.94/6.50      | v2_funct_1(sK3) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_10740,c_1803]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_16,plain,
% 46.94/6.50      ( v2_funct_1(k6_partfun1(X0)) ),
% 46.94/6.50      inference(cnf_transformation,[],[f149]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1825,plain,
% 46.94/6.50      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_30,plain,
% 46.94/6.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 46.94/6.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 46.94/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 46.94/6.50      | X3 = X2 ),
% 46.94/6.50      inference(cnf_transformation,[],[f111]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_634,plain,
% 46.94/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.94/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.94/6.50      | X3 = X0
% 46.94/6.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 46.94/6.50      | k6_partfun1(sK0) != X3
% 46.94/6.50      | sK0 != X2
% 46.94/6.50      | sK0 != X1 ),
% 46.94/6.50      inference(resolution_lifted,[status(thm)],[c_30,c_52]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_635,plain,
% 46.94/6.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 46.94/6.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 46.94/6.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 46.94/6.50      inference(unflattening,[status(thm)],[c_634]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_31,plain,
% 46.94/6.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 46.94/6.50      inference(cnf_transformation,[],[f152]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_643,plain,
% 46.94/6.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 46.94/6.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 46.94/6.50      inference(forward_subsumption_resolution,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_635,c_31]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1792,plain,
% 46.94/6.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 46.94/6.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_643]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_32,plain,
% 46.94/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.94/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 46.94/6.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 46.94/6.50      | ~ v1_funct_1(X0)
% 46.94/6.50      | ~ v1_funct_1(X3) ),
% 46.94/6.50      inference(cnf_transformation,[],[f115]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1943,plain,
% 46.94/6.50      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 46.94/6.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 46.94/6.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 46.94/6.50      | ~ v1_funct_1(sK3)
% 46.94/6.50      | ~ v1_funct_1(sK2) ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_32]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2654,plain,
% 46.94/6.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 46.94/6.50      inference(global_propositional_subsumption,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_1792,c_59,c_57,c_56,c_54,c_643,c_1943]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_53,negated_conjecture,
% 46.94/6.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 46.94/6.50      inference(cnf_transformation,[],[f137]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_37,plain,
% 46.94/6.50      ( ~ v1_funct_2(X0,X1,X2)
% 46.94/6.50      | ~ v1_funct_2(X3,X2,X4)
% 46.94/6.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.94/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 46.94/6.50      | ~ v1_funct_1(X3)
% 46.94/6.50      | ~ v1_funct_1(X0)
% 46.94/6.50      | v2_funct_1(X3)
% 46.94/6.50      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 46.94/6.50      | k2_relset_1(X1,X2,X0) != X2
% 46.94/6.50      | k1_xboole_0 = X4 ),
% 46.94/6.50      inference(cnf_transformation,[],[f121]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1810,plain,
% 46.94/6.50      ( k2_relset_1(X0,X1,X2) != X1
% 46.94/6.50      | k1_xboole_0 = X3
% 46.94/6.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 46.94/6.50      | v1_funct_2(X4,X1,X3) != iProver_top
% 46.94/6.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.94/6.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 46.94/6.50      | v1_funct_1(X2) != iProver_top
% 46.94/6.50      | v1_funct_1(X4) != iProver_top
% 46.94/6.50      | v2_funct_1(X4) = iProver_top
% 46.94/6.50      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_8691,plain,
% 46.94/6.50      ( k1_xboole_0 = X0
% 46.94/6.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 46.94/6.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 46.94/6.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 46.94/6.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 46.94/6.50      | v1_funct_1(X1) != iProver_top
% 46.94/6.50      | v1_funct_1(sK2) != iProver_top
% 46.94/6.50      | v2_funct_1(X1) = iProver_top
% 46.94/6.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_53,c_1810]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_8728,plain,
% 46.94/6.50      ( v1_funct_1(X1) != iProver_top
% 46.94/6.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 46.94/6.50      | k1_xboole_0 = X0
% 46.94/6.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 46.94/6.50      | v2_funct_1(X1) = iProver_top
% 46.94/6.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 46.94/6.50      inference(global_propositional_subsumption,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_8691,c_60,c_61,c_62]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_8729,plain,
% 46.94/6.50      ( k1_xboole_0 = X0
% 46.94/6.50      | v1_funct_2(X1,sK1,X0) != iProver_top
% 46.94/6.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 46.94/6.50      | v1_funct_1(X1) != iProver_top
% 46.94/6.50      | v2_funct_1(X1) = iProver_top
% 46.94/6.50      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top ),
% 46.94/6.50      inference(renaming,[status(thm)],[c_8728]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_8732,plain,
% 46.94/6.50      ( sK0 = k1_xboole_0
% 46.94/6.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 46.94/6.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 46.94/6.50      | v1_funct_1(sK3) != iProver_top
% 46.94/6.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 46.94/6.50      | v2_funct_1(sK3) = iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_2654,c_8729]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_50,negated_conjecture,
% 46.94/6.50      ( k1_xboole_0 != sK0 ),
% 46.94/6.50      inference(cnf_transformation,[],[f140]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1029,plain,( X0 = X0 ),theory(equality) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1066,plain,
% 46.94/6.50      ( k1_xboole_0 = k1_xboole_0 ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_1029]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1030,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1941,plain,
% 46.94/6.50      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_1030]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1942,plain,
% 46.94/6.50      ( sK0 != k1_xboole_0
% 46.94/6.50      | k1_xboole_0 = sK0
% 46.94/6.50      | k1_xboole_0 != k1_xboole_0 ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_1941]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_8735,plain,
% 46.94/6.50      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 46.94/6.50      | v2_funct_1(sK3) = iProver_top ),
% 46.94/6.50      inference(global_propositional_subsumption,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_8732,c_63,c_64,c_65,c_50,c_1066,c_1942]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_8739,plain,
% 46.94/6.50      ( v2_funct_1(sK3) = iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_1825,c_8735]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_11,plain,
% 46.94/6.50      ( ~ v1_funct_1(X0)
% 46.94/6.50      | ~ v2_funct_1(X0)
% 46.94/6.50      | ~ v1_relat_1(X0)
% 46.94/6.50      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 46.94/6.50      inference(cnf_transformation,[],[f93]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1830,plain,
% 46.94/6.50      ( k2_funct_1(X0) = k4_relat_1(X0)
% 46.94/6.50      | v1_funct_1(X0) != iProver_top
% 46.94/6.50      | v2_funct_1(X0) != iProver_top
% 46.94/6.50      | v1_relat_1(X0) != iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_6245,plain,
% 46.94/6.50      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 46.94/6.50      | v2_funct_1(sK3) != iProver_top
% 46.94/6.50      | v1_relat_1(sK3) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_1797,c_1830]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_6834,plain,
% 46.94/6.50      ( v2_funct_1(sK3) != iProver_top
% 46.94/6.50      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 46.94/6.50      inference(global_propositional_subsumption,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_6245,c_65,c_2995,c_3497]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_6835,plain,
% 46.94/6.50      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 46.94/6.50      | v2_funct_1(sK3) != iProver_top ),
% 46.94/6.50      inference(renaming,[status(thm)],[c_6834]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_8820,plain,
% 46.94/6.50      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_8739,c_6835]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_10749,plain,
% 46.94/6.50      ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 46.94/6.50      | sK0 = k1_xboole_0
% 46.94/6.50      | v1_funct_2(sK3,k1_relat_1(sK3),sK0) != iProver_top
% 46.94/6.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) != iProver_top
% 46.94/6.50      | v1_funct_1(sK3) != iProver_top
% 46.94/6.50      | v2_funct_1(sK3) != iProver_top ),
% 46.94/6.50      inference(light_normalisation,[status(thm)],[c_10748,c_8820]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_4984,plain,
% 46.94/6.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),sK0))) = iProver_top
% 46.94/6.50      | v1_funct_1(sK3) != iProver_top
% 46.94/6.50      | v1_relat_1(sK3) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_3926,c_1802]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_46,plain,
% 46.94/6.50      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 46.94/6.50      | ~ v1_funct_1(X0)
% 46.94/6.50      | ~ v1_relat_1(X0) ),
% 46.94/6.50      inference(cnf_transformation,[],[f129]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1801,plain,
% 46.94/6.50      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 46.94/6.50      | v1_funct_1(X0) != iProver_top
% 46.94/6.50      | v1_relat_1(X0) != iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_4985,plain,
% 46.94/6.50      ( v1_funct_2(sK3,k1_relat_1(sK3),sK0) = iProver_top
% 46.94/6.50      | v1_funct_1(sK3) != iProver_top
% 46.94/6.50      | v1_relat_1(sK3) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_3926,c_1801]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_135062,plain,
% 46.94/6.50      ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(k1_relat_1(sK3)) ),
% 46.94/6.50      inference(global_propositional_subsumption,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_10749,c_63,c_65,c_50,c_1066,c_1942,c_2995,c_3497,
% 46.94/6.50                 c_4984,c_4985,c_8739]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_5790,plain,
% 46.94/6.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 46.94/6.50      | sK0 = k1_xboole_0
% 46.94/6.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 46.94/6.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 46.94/6.50      | v1_funct_1(sK3) != iProver_top
% 46.94/6.50      | v2_funct_1(sK3) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_2661,c_1803]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_25120,plain,
% 46.94/6.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 46.94/6.50      inference(global_propositional_subsumption,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_5790,c_63,c_64,c_65,c_50,c_1066,c_1942,c_8739]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_25122,plain,
% 46.94/6.50      ( k5_relat_1(sK3,k4_relat_1(sK3)) = k6_partfun1(sK1) ),
% 46.94/6.50      inference(light_normalisation,[status(thm)],[c_25120,c_8820]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_135064,plain,
% 46.94/6.50      ( k6_partfun1(k1_relat_1(sK3)) = k6_partfun1(sK1) ),
% 46.94/6.50      inference(light_normalisation,[status(thm)],[c_135062,c_25122]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_7,plain,
% 46.94/6.50      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 46.94/6.50      inference(cnf_transformation,[],[f143]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_135220,plain,
% 46.94/6.50      ( k2_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3) ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_135064,c_7]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_135223,plain,
% 46.94/6.50      ( k1_relat_1(sK3) = sK1 ),
% 46.94/6.50      inference(demodulation,[status(thm)],[c_135220,c_7]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1035,plain,
% 46.94/6.50      ( X0 != X1 | k4_relat_1(X0) = k4_relat_1(X1) ),
% 46.94/6.50      theory(equality) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_95203,plain,
% 46.94/6.50      ( k4_relat_1(k4_relat_1(sK3)) = k4_relat_1(sK2)
% 46.94/6.50      | k4_relat_1(sK3) != sK2 ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_1035]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_70537,plain,
% 46.94/6.50      ( k2_funct_1(sK2) != X0
% 46.94/6.50      | k2_funct_1(sK2) = k4_relat_1(k4_relat_1(sK3))
% 46.94/6.50      | k4_relat_1(k4_relat_1(sK3)) != X0 ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_1030]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_73023,plain,
% 46.94/6.50      ( k2_funct_1(sK2) = k4_relat_1(k4_relat_1(sK3))
% 46.94/6.50      | k2_funct_1(sK2) != k4_relat_1(sK2)
% 46.94/6.50      | k4_relat_1(k4_relat_1(sK3)) != k4_relat_1(sK2) ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_70537]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1901,plain,
% 46.94/6.50      ( k2_funct_1(sK2) != X0 | k2_funct_1(sK2) = sK3 | sK3 != X0 ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_1030]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_19331,plain,
% 46.94/6.50      ( k2_funct_1(sK2) != k4_relat_1(k4_relat_1(sK3))
% 46.94/6.50      | k2_funct_1(sK2) = sK3
% 46.94/6.50      | sK3 != k4_relat_1(k4_relat_1(sK3)) ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_1901]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1796,plain,
% 46.94/6.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_34,plain,
% 46.94/6.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 46.94/6.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 46.94/6.50      | ~ v1_funct_1(X0)
% 46.94/6.50      | ~ v1_funct_1(X3)
% 46.94/6.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 46.94/6.50      inference(cnf_transformation,[],[f116]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1812,plain,
% 46.94/6.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 46.94/6.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 46.94/6.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.94/6.50      | v1_funct_1(X5) != iProver_top
% 46.94/6.50      | v1_funct_1(X4) != iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_7557,plain,
% 46.94/6.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 46.94/6.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.94/6.50      | v1_funct_1(X2) != iProver_top
% 46.94/6.50      | v1_funct_1(sK3) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_1799,c_1812]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_7691,plain,
% 46.94/6.50      ( v1_funct_1(X2) != iProver_top
% 46.94/6.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.94/6.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 46.94/6.50      inference(global_propositional_subsumption,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_7557,c_63]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_7692,plain,
% 46.94/6.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 46.94/6.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 46.94/6.50      | v1_funct_1(X2) != iProver_top ),
% 46.94/6.50      inference(renaming,[status(thm)],[c_7691]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_7700,plain,
% 46.94/6.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 46.94/6.50      | v1_funct_1(sK2) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_1796,c_7692]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_7702,plain,
% 46.94/6.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 46.94/6.50      | v1_funct_1(sK2) != iProver_top ),
% 46.94/6.50      inference(light_normalisation,[status(thm)],[c_7700,c_2654]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_7834,plain,
% 46.94/6.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 46.94/6.50      inference(global_propositional_subsumption,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_7702,c_60]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_25,plain,
% 46.94/6.50      ( ~ v1_funct_1(X0)
% 46.94/6.50      | ~ v1_funct_1(X1)
% 46.94/6.50      | ~ v2_funct_1(X0)
% 46.94/6.50      | ~ v1_relat_1(X0)
% 46.94/6.50      | ~ v1_relat_1(X1)
% 46.94/6.50      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 46.94/6.50      | k2_funct_1(X0) = X1
% 46.94/6.50      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 46.94/6.50      inference(cnf_transformation,[],[f151]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1819,plain,
% 46.94/6.50      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 46.94/6.50      | k2_funct_1(X1) = X0
% 46.94/6.50      | k2_relat_1(X0) != k1_relat_1(X1)
% 46.94/6.50      | v1_funct_1(X1) != iProver_top
% 46.94/6.50      | v1_funct_1(X0) != iProver_top
% 46.94/6.50      | v2_funct_1(X1) != iProver_top
% 46.94/6.50      | v1_relat_1(X1) != iProver_top
% 46.94/6.50      | v1_relat_1(X0) != iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_8243,plain,
% 46.94/6.50      ( k2_funct_1(sK3) = sK2
% 46.94/6.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 46.94/6.50      | k2_relat_1(sK2) != k1_relat_1(sK3)
% 46.94/6.50      | v1_funct_1(sK3) != iProver_top
% 46.94/6.50      | v1_funct_1(sK2) != iProver_top
% 46.94/6.50      | v2_funct_1(sK3) != iProver_top
% 46.94/6.50      | v1_relat_1(sK3) != iProver_top
% 46.94/6.50      | v1_relat_1(sK2) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_7834,c_1819]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_3924,plain,
% 46.94/6.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_1796,c_1816]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_3925,plain,
% 46.94/6.50      ( k2_relat_1(sK2) = sK1 ),
% 46.94/6.50      inference(light_normalisation,[status(thm)],[c_3924,c_53]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_8244,plain,
% 46.94/6.50      ( k2_funct_1(sK3) = sK2
% 46.94/6.50      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 46.94/6.50      | k1_relat_1(sK3) != sK1
% 46.94/6.50      | v1_funct_1(sK3) != iProver_top
% 46.94/6.50      | v1_funct_1(sK2) != iProver_top
% 46.94/6.50      | v2_funct_1(sK3) != iProver_top
% 46.94/6.50      | v1_relat_1(sK3) != iProver_top
% 46.94/6.50      | v1_relat_1(sK2) != iProver_top ),
% 46.94/6.50      inference(light_normalisation,[status(thm)],[c_8243,c_3925,c_3926]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_8245,plain,
% 46.94/6.50      ( k2_funct_1(sK3) = sK2
% 46.94/6.50      | k1_relat_1(sK3) != sK1
% 46.94/6.50      | v1_funct_1(sK3) != iProver_top
% 46.94/6.50      | v1_funct_1(sK2) != iProver_top
% 46.94/6.50      | v2_funct_1(sK3) != iProver_top
% 46.94/6.50      | v1_relat_1(sK3) != iProver_top
% 46.94/6.50      | v1_relat_1(sK2) != iProver_top ),
% 46.94/6.50      inference(equality_resolution_simp,[status(thm)],[c_8244]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1838,plain,
% 46.94/6.50      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1839,plain,
% 46.94/6.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 46.94/6.50      | v1_relat_1(X1) != iProver_top
% 46.94/6.50      | v1_relat_1(X0) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_4033,plain,
% 46.94/6.50      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 46.94/6.50      | v1_relat_1(sK2) = iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_1796,c_1839]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_4599,plain,
% 46.94/6.50      ( v1_relat_1(sK2) = iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_1838,c_4033]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_13923,plain,
% 46.94/6.50      ( k1_relat_1(sK3) != sK1 | k2_funct_1(sK3) = sK2 ),
% 46.94/6.50      inference(global_propositional_subsumption,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_8245,c_60,c_63,c_65,c_2995,c_3497,c_4599,c_8739]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_13924,plain,
% 46.94/6.50      ( k2_funct_1(sK3) = sK2 | k1_relat_1(sK3) != sK1 ),
% 46.94/6.50      inference(renaming,[status(thm)],[c_13923]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_13925,plain,
% 46.94/6.50      ( k1_relat_1(sK3) != sK1 | k4_relat_1(sK3) = sK2 ),
% 46.94/6.50      inference(demodulation,[status(thm)],[c_13924,c_8820]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2006,plain,
% 46.94/6.50      ( X0 != X1 | sK3 != X1 | sK3 = X0 ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_1030]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2388,plain,
% 46.94/6.50      ( X0 != sK3 | sK3 = X0 | sK3 != sK3 ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_2006]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_9959,plain,
% 46.94/6.50      ( k4_relat_1(k4_relat_1(sK3)) != sK3
% 46.94/6.50      | sK3 = k4_relat_1(k4_relat_1(sK3))
% 46.94/6.50      | sK3 != sK3 ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_2388]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_1794,plain,
% 46.94/6.50      ( v1_funct_1(sK2) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_6246,plain,
% 46.94/6.50      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 46.94/6.50      | v2_funct_1(sK2) != iProver_top
% 46.94/6.50      | v1_relat_1(sK2) != iProver_top ),
% 46.94/6.50      inference(superposition,[status(thm)],[c_1794,c_1830]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2972,plain,
% 46.94/6.50      ( sK3 = sK3 ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_1029]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2,plain,
% 46.94/6.50      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 46.94/6.50      inference(cnf_transformation,[],[f84]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_2670,plain,
% 46.94/6.50      ( ~ v1_relat_1(sK3) | k4_relat_1(k4_relat_1(sK3)) = sK3 ),
% 46.94/6.50      inference(instantiation,[status(thm)],[c_2]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_48,negated_conjecture,
% 46.94/6.50      ( k2_funct_1(sK2) != sK3 ),
% 46.94/6.50      inference(cnf_transformation,[],[f142]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_51,negated_conjecture,
% 46.94/6.50      ( v2_funct_1(sK2) ),
% 46.94/6.50      inference(cnf_transformation,[],[f139]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(c_67,plain,
% 46.94/6.50      ( v2_funct_1(sK2) = iProver_top ),
% 46.94/6.50      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 46.94/6.50  
% 46.94/6.50  cnf(contradiction,plain,
% 46.94/6.50      ( $false ),
% 46.94/6.50      inference(minisat,
% 46.94/6.50                [status(thm)],
% 46.94/6.50                [c_135223,c_95203,c_73023,c_19331,c_13925,c_9959,c_6246,
% 46.94/6.50                 c_4599,c_3496,c_2994,c_2972,c_2670,c_48,c_67,c_54]) ).
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  % SZS output end CNFRefutation for theBenchmark.p
% 46.94/6.50  
% 46.94/6.50  ------                               Statistics
% 46.94/6.50  
% 46.94/6.50  ------ General
% 46.94/6.50  
% 46.94/6.50  abstr_ref_over_cycles:                  0
% 46.94/6.50  abstr_ref_under_cycles:                 0
% 46.94/6.50  gc_basic_clause_elim:                   0
% 46.94/6.50  forced_gc_time:                         0
% 46.94/6.50  parsing_time:                           0.012
% 46.94/6.50  unif_index_cands_time:                  0.
% 46.94/6.50  unif_index_add_time:                    0.
% 46.94/6.50  orderings_time:                         0.
% 46.94/6.50  out_proof_time:                         0.043
% 46.94/6.50  total_time:                             5.659
% 46.94/6.50  num_of_symbols:                         54
% 46.94/6.50  num_of_terms:                           211365
% 46.94/6.50  
% 46.94/6.50  ------ Preprocessing
% 46.94/6.50  
% 46.94/6.50  num_of_splits:                          0
% 46.94/6.50  num_of_split_atoms:                     0
% 46.94/6.50  num_of_reused_defs:                     0
% 46.94/6.50  num_eq_ax_congr_red:                    3
% 46.94/6.50  num_of_sem_filtered_clauses:            1
% 46.94/6.50  num_of_subtypes:                        0
% 46.94/6.50  monotx_restored_types:                  0
% 46.94/6.50  sat_num_of_epr_types:                   0
% 46.94/6.50  sat_num_of_non_cyclic_types:            0
% 46.94/6.50  sat_guarded_non_collapsed_types:        0
% 46.94/6.50  num_pure_diseq_elim:                    0
% 46.94/6.50  simp_replaced_by:                       0
% 46.94/6.50  res_preprocessed:                       260
% 46.94/6.50  prep_upred:                             0
% 46.94/6.50  prep_unflattend:                        12
% 46.94/6.50  smt_new_axioms:                         0
% 46.94/6.50  pred_elim_cands:                        5
% 46.94/6.50  pred_elim:                              1
% 46.94/6.50  pred_elim_cl:                           1
% 46.94/6.50  pred_elim_cycles:                       3
% 46.94/6.50  merged_defs:                            0
% 46.94/6.50  merged_defs_ncl:                        0
% 46.94/6.50  bin_hyper_res:                          0
% 46.94/6.50  prep_cycles:                            4
% 46.94/6.50  pred_elim_time:                         0.006
% 46.94/6.50  splitting_time:                         0.
% 46.94/6.50  sem_filter_time:                        0.
% 46.94/6.50  monotx_time:                            0.001
% 46.94/6.50  subtype_inf_time:                       0.
% 46.94/6.50  
% 46.94/6.50  ------ Problem properties
% 46.94/6.50  
% 46.94/6.50  clauses:                                55
% 46.94/6.50  conjectures:                            11
% 46.94/6.50  epr:                                    7
% 46.94/6.50  horn:                                   51
% 46.94/6.50  ground:                                 12
% 46.94/6.50  unary:                                  18
% 46.94/6.50  binary:                                 9
% 46.94/6.50  lits:                                   198
% 46.94/6.50  lits_eq:                                44
% 46.94/6.50  fd_pure:                                0
% 46.94/6.50  fd_pseudo:                              0
% 46.94/6.50  fd_cond:                                4
% 46.94/6.50  fd_pseudo_cond:                         1
% 46.94/6.50  ac_symbols:                             0
% 46.94/6.50  
% 46.94/6.50  ------ Propositional Solver
% 46.94/6.50  
% 46.94/6.50  prop_solver_calls:                      70
% 46.94/6.50  prop_fast_solver_calls:                 7430
% 46.94/6.50  smt_solver_calls:                       0
% 46.94/6.50  smt_fast_solver_calls:                  0
% 46.94/6.50  prop_num_of_clauses:                    69176
% 46.94/6.50  prop_preprocess_simplified:             102512
% 46.94/6.50  prop_fo_subsumed:                       1793
% 46.94/6.50  prop_solver_time:                       0.
% 46.94/6.50  smt_solver_time:                        0.
% 46.94/6.50  smt_fast_solver_time:                   0.
% 46.94/6.50  prop_fast_solver_time:                  0.
% 46.94/6.50  prop_unsat_core_time:                   0.013
% 46.94/6.50  
% 46.94/6.50  ------ QBF
% 46.94/6.50  
% 46.94/6.50  qbf_q_res:                              0
% 46.94/6.50  qbf_num_tautologies:                    0
% 46.94/6.50  qbf_prep_cycles:                        0
% 46.94/6.50  
% 46.94/6.50  ------ BMC1
% 46.94/6.50  
% 46.94/6.50  bmc1_current_bound:                     -1
% 46.94/6.50  bmc1_last_solved_bound:                 -1
% 46.94/6.50  bmc1_unsat_core_size:                   -1
% 46.94/6.50  bmc1_unsat_core_parents_size:           -1
% 46.94/6.50  bmc1_merge_next_fun:                    0
% 46.94/6.50  bmc1_unsat_core_clauses_time:           0.
% 46.94/6.50  
% 46.94/6.50  ------ Instantiation
% 46.94/6.50  
% 46.94/6.50  inst_num_of_clauses:                    8241
% 46.94/6.50  inst_num_in_passive:                    1459
% 46.94/6.50  inst_num_in_active:                     5491
% 46.94/6.50  inst_num_in_unprocessed:                3804
% 46.94/6.50  inst_num_of_loops:                      6029
% 46.94/6.50  inst_num_of_learning_restarts:          1
% 46.94/6.50  inst_num_moves_active_passive:          534
% 46.94/6.50  inst_lit_activity:                      0
% 46.94/6.50  inst_lit_activity_moves:                7
% 46.94/6.50  inst_num_tautologies:                   0
% 46.94/6.50  inst_num_prop_implied:                  0
% 46.94/6.50  inst_num_existing_simplified:           0
% 46.94/6.50  inst_num_eq_res_simplified:             0
% 46.94/6.50  inst_num_child_elim:                    0
% 46.94/6.50  inst_num_of_dismatching_blockings:      12708
% 46.94/6.50  inst_num_of_non_proper_insts:           14283
% 46.94/6.50  inst_num_of_duplicates:                 0
% 46.94/6.50  inst_inst_num_from_inst_to_res:         0
% 46.94/6.50  inst_dismatching_checking_time:         0.
% 46.94/6.50  
% 46.94/6.50  ------ Resolution
% 46.94/6.50  
% 46.94/6.50  res_num_of_clauses:                     74
% 46.94/6.50  res_num_in_passive:                     74
% 46.94/6.50  res_num_in_active:                      0
% 46.94/6.50  res_num_of_loops:                       264
% 46.94/6.50  res_forward_subset_subsumed:            524
% 46.94/6.50  res_backward_subset_subsumed:           0
% 46.94/6.50  res_forward_subsumed:                   0
% 46.94/6.50  res_backward_subsumed:                  0
% 46.94/6.50  res_forward_subsumption_resolution:     2
% 46.94/6.50  res_backward_subsumption_resolution:    0
% 46.94/6.50  res_clause_to_clause_subsumption:       18890
% 46.94/6.50  res_orphan_elimination:                 0
% 46.94/6.50  res_tautology_del:                      377
% 46.94/6.50  res_num_eq_res_simplified:              1
% 46.94/6.50  res_num_sel_changes:                    0
% 46.94/6.50  res_moves_from_active_to_pass:          0
% 46.94/6.50  
% 46.94/6.50  ------ Superposition
% 46.94/6.50  
% 46.94/6.50  sup_time_total:                         0.
% 46.94/6.50  sup_time_generating:                    0.
% 46.94/6.50  sup_time_sim_full:                      0.
% 46.94/6.50  sup_time_sim_immed:                     0.
% 46.94/6.50  
% 46.94/6.50  sup_num_of_clauses:                     6187
% 46.94/6.50  sup_num_in_active:                      893
% 46.94/6.50  sup_num_in_passive:                     5294
% 46.94/6.50  sup_num_of_loops:                       1205
% 46.94/6.50  sup_fw_superposition:                   3419
% 46.94/6.50  sup_bw_superposition:                   5398
% 46.94/6.50  sup_immediate_simplified:               5236
% 46.94/6.50  sup_given_eliminated:                   2
% 46.94/6.50  comparisons_done:                       0
% 46.94/6.50  comparisons_avoided:                    2
% 46.94/6.50  
% 46.94/6.50  ------ Simplifications
% 46.94/6.50  
% 46.94/6.50  
% 46.94/6.50  sim_fw_subset_subsumed:                 203
% 46.94/6.50  sim_bw_subset_subsumed:                 503
% 46.94/6.50  sim_fw_subsumed:                        203
% 46.94/6.50  sim_bw_subsumed:                        10
% 46.94/6.51  sim_fw_subsumption_res:                 0
% 46.94/6.51  sim_bw_subsumption_res:                 0
% 46.94/6.51  sim_tautology_del:                      102
% 46.94/6.51  sim_eq_tautology_del:                   1359
% 46.94/6.51  sim_eq_res_simp:                        48
% 46.94/6.51  sim_fw_demodulated:                     459
% 46.94/6.51  sim_bw_demodulated:                     185
% 46.94/6.51  sim_light_normalised:                   4843
% 46.94/6.51  sim_joinable_taut:                      0
% 46.94/6.51  sim_joinable_simp:                      0
% 46.94/6.51  sim_ac_normalised:                      0
% 46.94/6.51  sim_smt_subsumption:                    0
% 46.94/6.51  
%------------------------------------------------------------------------------
