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
% DateTime   : Thu Dec  3 12:02:56 EST 2020

% Result     : Theorem 27.81s
% Output     : CNFRefutation 27.81s
% Verified   : 
% Statistics : Number of formulae       :  273 (8684 expanded)
%              Number of clauses        :  175 (2324 expanded)
%              Number of leaves         :   24 (2269 expanded)
%              Depth                    :   26
%              Number of atoms          :  847 (74945 expanded)
%              Number of equality atoms :  431 (26886 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
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
    inference(negated_conjecture,[],[f22])).

fof(f52,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f53,plain,(
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
    inference(flattening,[],[f52])).

fof(f59,plain,(
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

fof(f58,plain,
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

fof(f60,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f59,f58])).

fof(f98,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f60])).

fof(f95,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f60])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f89,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f96,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f60])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f74,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f101,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f60])).

fof(f21,axiom,(
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

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f60])).

fof(f99,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f60])).

fof(f103,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f60])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f44])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f100,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f60])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f88,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f90,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f107,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f72,f90])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f105,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f71,f90])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f41,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f81,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f66,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f73,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f108,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f73,f90])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f68,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f106,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f70,f90])).

fof(f104,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1301,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1299,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1302,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3746,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1299,c_1302])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_43,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_3997,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3746,c_43])).

cnf(c_3998,plain,
    ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3997])).

cnf(c_4005,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_3998])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_46,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4016,plain,
    ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4005,c_46])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1305,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4018,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4016,c_1305])).

cnf(c_45,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_48,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5966,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4018,c_43,c_45,c_46,c_48])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1306,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5972,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5966,c_1306])).

cnf(c_2403,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1299,c_1306])).

cnf(c_1298,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1308,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1312,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2895,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1308,c_1312])).

cnf(c_11254,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1298,c_2895])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_576,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_34])).

cnf(c_577,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_576])).

cnf(c_579,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_577,c_42])).

cnf(c_1291,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_579])).

cnf(c_1387,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1468,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1387])).

cnf(c_1756,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1291,c_42,c_40,c_577,c_1468])).

cnf(c_11260,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11254,c_1756])).

cnf(c_1469,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_31293,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11260,c_45,c_1469])).

cnf(c_31294,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_31293])).

cnf(c_31301,plain,
    ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X0) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2403,c_31294])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_502,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_41])).

cnf(c_503,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_502])).

cnf(c_36,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_505,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_503,c_42,c_40,c_36,c_34,c_32])).

cnf(c_1758,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_1756,c_505])).

cnf(c_31308,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_31301,c_1758])).

cnf(c_31345,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,k5_relat_1(sK3,sK2))) = k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) ),
    inference(superposition,[status(thm)],[c_5972,c_31308])).

cnf(c_2402,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_1306])).

cnf(c_2896,plain,
    ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2403,c_1312])).

cnf(c_3480,plain,
    ( k5_relat_1(k5_relat_1(sK2,sK3),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2402,c_2896])).

cnf(c_3745,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_1302])).

cnf(c_3894,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3745,c_46])).

cnf(c_3895,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3894])).

cnf(c_3903,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1299,c_3895])).

cnf(c_24,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_35,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_443,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_444,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_443])).

cnf(c_27,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_61,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_446,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_444,c_61])).

cnf(c_1296,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_446])).

cnf(c_1374,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1908,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1296,c_42,c_40,c_39,c_37,c_61,c_444,c_1374])).

cnf(c_3904,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3903,c_1908])).

cnf(c_4123,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3904,c_43])).

cnf(c_4132,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3480,c_4123])).

cnf(c_4138,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(superposition,[status(thm)],[c_2403,c_4132])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1311,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2467,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2) = sK2 ),
    inference(superposition,[status(thm)],[c_2403,c_1311])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_562,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_34])).

cnf(c_563,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_565,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_42])).

cnf(c_1292,plain,
    ( k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_494,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_495,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_497,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_42,c_40,c_36,c_34,c_32])).

cnf(c_1318,plain,
    ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1292,c_497])).

cnf(c_9,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1319,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1318,c_9])).

cnf(c_1331,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1319])).

cnf(c_2035,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1319,c_40,c_1331,c_1468])).

cnf(c_2474,plain,
    ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2467,c_2035])).

cnf(c_4141,plain,
    ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4138,c_2474])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_4,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_420,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_4])).

cnf(c_424,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_420,c_21])).

cnf(c_425,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_424])).

cnf(c_1297,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_425])).

cnf(c_5973,plain,
    ( r1_tarski(k1_relat_1(k5_relat_1(sK3,sK2)),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_5966,c_1297])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1317,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7889,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK2)) = sK1
    | r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5973,c_1317])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1304,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4019,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,sK2)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4016,c_1304])).

cnf(c_16,plain,
    ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1307,plain,
    ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_7201,plain,
    ( r1_tarski(k2_relat_1(sK2),k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top
    | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4141,c_1307])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_534,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_34])).

cnf(c_535,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_537,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_535,c_42])).

cnf(c_1294,plain,
    ( k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_537])).

cnf(c_1322,plain,
    ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1294,c_505])).

cnf(c_1323,plain,
    ( k2_relat_1(sK2) = sK1
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1322,c_9])).

cnf(c_1338,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = sK1 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1323])).

cnf(c_2163,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1323,c_40,c_1338,c_1468])).

cnf(c_7202,plain,
    ( r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top
    | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7201,c_2163])).

cnf(c_11289,plain,
    ( k1_relat_1(k5_relat_1(sK3,sK2)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7889,c_43,c_45,c_46,c_48,c_1469,c_4019,c_5972,c_7202])).

cnf(c_6130,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(k5_relat_1(sK3,sK2))),k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,sK2) ),
    inference(superposition,[status(thm)],[c_5972,c_1311])).

cnf(c_11292,plain,
    ( k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,sK2) ),
    inference(demodulation,[status(thm)],[c_11289,c_6130])).

cnf(c_31346,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_31345,c_1758,c_4141,c_11292])).

cnf(c_5961,plain,
    ( v1_funct_1(k5_relat_1(sK3,sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4019,c_43,c_45,c_46,c_48])).

cnf(c_31806,plain,
    ( v1_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_31346,c_5961])).

cnf(c_1303,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3901,plain,
    ( k1_partfun1(X0,X0,sK1,sK0,k6_partfun1(X0),sK3) = k5_relat_1(k6_partfun1(X0),sK3)
    | v1_funct_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1303,c_3895])).

cnf(c_91543,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k6_partfun1(sK1),sK3) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_31806,c_3901])).

cnf(c_2897,plain,
    ( k5_relat_1(sK3,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK3,X0),X1)
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2402,c_1312])).

cnf(c_5123,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK2),X0) = k5_relat_1(sK3,k5_relat_1(sK2,X0))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2403,c_2897])).

cnf(c_5145,plain,
    ( k5_relat_1(sK3,k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK3,sK2),sK3) ),
    inference(superposition,[status(thm)],[c_2402,c_5123])).

cnf(c_5147,plain,
    ( k5_relat_1(k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(light_normalisation,[status(thm)],[c_5145,c_4123])).

cnf(c_31797,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(demodulation,[status(thm)],[c_31346,c_5147])).

cnf(c_31340,plain,
    ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2402,c_31308])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1315,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1310,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2355,plain,
    ( k5_relat_1(k4_relat_1(X0),k6_partfun1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1315,c_1310])).

cnf(c_4258,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2)))) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2403,c_2355])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1314,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2469,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2403,c_1314])).

cnf(c_2472,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_2469,c_2035])).

cnf(c_4263,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k4_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4258,c_2472])).

cnf(c_31348,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = k4_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_31340,c_4123,c_4263])).

cnf(c_31814,plain,
    ( k5_relat_1(sK3,k6_partfun1(sK0)) = k4_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_31797,c_31348])).

cnf(c_3900,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,k1_partfun1(X0,X2,X3,X1,X4,X5),sK3) = k5_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5),sK3)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(k1_partfun1(X0,X2,X3,X1,X4,X5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1305,c_3895])).

cnf(c_6186,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),sK3) = k5_relat_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),sK3)
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4016,c_3900])).

cnf(c_6189,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k6_partfun1(sK0))
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6186,c_4016,c_5147])).

cnf(c_5971,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(k5_relat_1(sK3,sK2),sK3)
    | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5966,c_3895])).

cnf(c_5975,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k6_partfun1(sK0))
    | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5971,c_5147])).

cnf(c_6370,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6189,c_43,c_45,c_46,c_48,c_4019,c_5975])).

cnf(c_31803,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k6_partfun1(sK1),sK3) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(demodulation,[status(thm)],[c_31346,c_6370])).

cnf(c_31815,plain,
    ( k1_partfun1(sK1,sK1,sK1,sK0,k6_partfun1(sK1),sK3) = k4_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_31814,c_31803])).

cnf(c_4126,plain,
    ( k1_relat_1(k6_partfun1(sK0)) != k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4123,c_1307])).

cnf(c_4127,plain,
    ( k1_relat_1(k6_partfun1(sK0)) != sK0
    | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4126,c_2035,c_2163])).

cnf(c_10,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_4128,plain,
    ( sK0 != sK0
    | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4127,c_10])).

cnf(c_4129,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4128])).

cnf(c_1561,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1562,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1561])).

cnf(c_22125,plain,
    ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4129,c_43,c_45,c_46,c_48,c_1469,c_1562])).

cnf(c_2038,plain,
    ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1301,c_1297])).

cnf(c_2696,plain,
    ( k1_relat_1(sK3) = sK1
    | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2038,c_1317])).

cnf(c_22130,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(superposition,[status(thm)],[c_22125,c_2696])).

cnf(c_2410,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_2402,c_1311])).

cnf(c_90650,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_22130,c_2410])).

cnf(c_91544,plain,
    ( k4_relat_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_91543,c_31815,c_90650])).

cnf(c_31,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1760,plain,
    ( k4_relat_1(sK2) != sK3 ),
    inference(demodulation,[status(thm)],[c_1756,c_31])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_91544,c_1760])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n009.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 16:57:41 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 27.48/3.93  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 27.48/3.93  
% 27.48/3.93  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 27.48/3.93  
% 27.48/3.93  ------  iProver source info
% 27.48/3.93  
% 27.48/3.93  git: date: 2020-06-30 10:37:57 +0100
% 27.48/3.93  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 27.48/3.93  git: non_committed_changes: false
% 27.48/3.93  git: last_make_outside_of_git: false
% 27.48/3.93  
% 27.48/3.93  ------ 
% 27.48/3.93  
% 27.48/3.93  ------ Input Options
% 27.48/3.93  
% 27.48/3.93  --out_options                           all
% 27.48/3.93  --tptp_safe_out                         true
% 27.48/3.93  --problem_path                          ""
% 27.48/3.93  --include_path                          ""
% 27.48/3.93  --clausifier                            res/vclausify_rel
% 27.48/3.93  --clausifier_options                    ""
% 27.48/3.93  --stdin                                 false
% 27.48/3.93  --stats_out                             all
% 27.48/3.93  
% 27.48/3.93  ------ General Options
% 27.48/3.93  
% 27.48/3.93  --fof                                   false
% 27.48/3.93  --time_out_real                         305.
% 27.48/3.93  --time_out_virtual                      -1.
% 27.48/3.93  --symbol_type_check                     false
% 27.48/3.93  --clausify_out                          false
% 27.48/3.93  --sig_cnt_out                           false
% 27.48/3.93  --trig_cnt_out                          false
% 27.48/3.93  --trig_cnt_out_tolerance                1.
% 27.48/3.93  --trig_cnt_out_sk_spl                   false
% 27.48/3.93  --abstr_cl_out                          false
% 27.48/3.93  
% 27.48/3.93  ------ Global Options
% 27.48/3.93  
% 27.48/3.93  --schedule                              default
% 27.48/3.93  --add_important_lit                     false
% 27.48/3.93  --prop_solver_per_cl                    1000
% 27.48/3.93  --min_unsat_core                        false
% 27.48/3.93  --soft_assumptions                      false
% 27.48/3.93  --soft_lemma_size                       3
% 27.48/3.93  --prop_impl_unit_size                   0
% 27.48/3.93  --prop_impl_unit                        []
% 27.48/3.93  --share_sel_clauses                     true
% 27.48/3.93  --reset_solvers                         false
% 27.48/3.93  --bc_imp_inh                            [conj_cone]
% 27.48/3.93  --conj_cone_tolerance                   3.
% 27.48/3.93  --extra_neg_conj                        none
% 27.48/3.93  --large_theory_mode                     true
% 27.48/3.93  --prolific_symb_bound                   200
% 27.48/3.93  --lt_threshold                          2000
% 27.48/3.93  --clause_weak_htbl                      true
% 27.48/3.93  --gc_record_bc_elim                     false
% 27.48/3.93  
% 27.48/3.93  ------ Preprocessing Options
% 27.48/3.93  
% 27.48/3.93  --preprocessing_flag                    true
% 27.48/3.93  --time_out_prep_mult                    0.1
% 27.48/3.93  --splitting_mode                        input
% 27.48/3.93  --splitting_grd                         true
% 27.48/3.93  --splitting_cvd                         false
% 27.48/3.93  --splitting_cvd_svl                     false
% 27.48/3.93  --splitting_nvd                         32
% 27.48/3.93  --sub_typing                            true
% 27.48/3.93  --prep_gs_sim                           true
% 27.48/3.93  --prep_unflatten                        true
% 27.48/3.93  --prep_res_sim                          true
% 27.48/3.93  --prep_upred                            true
% 27.48/3.93  --prep_sem_filter                       exhaustive
% 27.48/3.93  --prep_sem_filter_out                   false
% 27.48/3.93  --pred_elim                             true
% 27.48/3.93  --res_sim_input                         true
% 27.48/3.93  --eq_ax_congr_red                       true
% 27.48/3.93  --pure_diseq_elim                       true
% 27.48/3.93  --brand_transform                       false
% 27.48/3.93  --non_eq_to_eq                          false
% 27.48/3.93  --prep_def_merge                        true
% 27.48/3.93  --prep_def_merge_prop_impl              false
% 27.48/3.93  --prep_def_merge_mbd                    true
% 27.48/3.93  --prep_def_merge_tr_red                 false
% 27.48/3.93  --prep_def_merge_tr_cl                  false
% 27.48/3.93  --smt_preprocessing                     true
% 27.48/3.93  --smt_ac_axioms                         fast
% 27.48/3.93  --preprocessed_out                      false
% 27.48/3.93  --preprocessed_stats                    false
% 27.48/3.93  
% 27.48/3.93  ------ Abstraction refinement Options
% 27.48/3.93  
% 27.48/3.93  --abstr_ref                             []
% 27.48/3.93  --abstr_ref_prep                        false
% 27.48/3.93  --abstr_ref_until_sat                   false
% 27.48/3.93  --abstr_ref_sig_restrict                funpre
% 27.48/3.93  --abstr_ref_af_restrict_to_split_sk     false
% 27.48/3.93  --abstr_ref_under                       []
% 27.48/3.93  
% 27.48/3.93  ------ SAT Options
% 27.48/3.93  
% 27.48/3.93  --sat_mode                              false
% 27.48/3.93  --sat_fm_restart_options                ""
% 27.48/3.93  --sat_gr_def                            false
% 27.48/3.93  --sat_epr_types                         true
% 27.48/3.93  --sat_non_cyclic_types                  false
% 27.48/3.93  --sat_finite_models                     false
% 27.48/3.93  --sat_fm_lemmas                         false
% 27.48/3.93  --sat_fm_prep                           false
% 27.48/3.93  --sat_fm_uc_incr                        true
% 27.48/3.93  --sat_out_model                         small
% 27.48/3.93  --sat_out_clauses                       false
% 27.48/3.93  
% 27.48/3.93  ------ QBF Options
% 27.48/3.93  
% 27.48/3.93  --qbf_mode                              false
% 27.48/3.93  --qbf_elim_univ                         false
% 27.48/3.93  --qbf_dom_inst                          none
% 27.48/3.93  --qbf_dom_pre_inst                      false
% 27.48/3.93  --qbf_sk_in                             false
% 27.48/3.93  --qbf_pred_elim                         true
% 27.48/3.93  --qbf_split                             512
% 27.48/3.93  
% 27.48/3.93  ------ BMC1 Options
% 27.48/3.93  
% 27.48/3.93  --bmc1_incremental                      false
% 27.48/3.93  --bmc1_axioms                           reachable_all
% 27.48/3.93  --bmc1_min_bound                        0
% 27.48/3.93  --bmc1_max_bound                        -1
% 27.48/3.93  --bmc1_max_bound_default                -1
% 27.48/3.93  --bmc1_symbol_reachability              true
% 27.48/3.93  --bmc1_property_lemmas                  false
% 27.48/3.93  --bmc1_k_induction                      false
% 27.48/3.93  --bmc1_non_equiv_states                 false
% 27.48/3.93  --bmc1_deadlock                         false
% 27.48/3.93  --bmc1_ucm                              false
% 27.48/3.93  --bmc1_add_unsat_core                   none
% 27.48/3.93  --bmc1_unsat_core_children              false
% 27.48/3.93  --bmc1_unsat_core_extrapolate_axioms    false
% 27.48/3.93  --bmc1_out_stat                         full
% 27.48/3.93  --bmc1_ground_init                      false
% 27.48/3.93  --bmc1_pre_inst_next_state              false
% 27.48/3.93  --bmc1_pre_inst_state                   false
% 27.48/3.93  --bmc1_pre_inst_reach_state             false
% 27.48/3.93  --bmc1_out_unsat_core                   false
% 27.48/3.93  --bmc1_aig_witness_out                  false
% 27.48/3.93  --bmc1_verbose                          false
% 27.48/3.93  --bmc1_dump_clauses_tptp                false
% 27.48/3.93  --bmc1_dump_unsat_core_tptp             false
% 27.48/3.93  --bmc1_dump_file                        -
% 27.48/3.93  --bmc1_ucm_expand_uc_limit              128
% 27.48/3.93  --bmc1_ucm_n_expand_iterations          6
% 27.48/3.93  --bmc1_ucm_extend_mode                  1
% 27.48/3.93  --bmc1_ucm_init_mode                    2
% 27.48/3.93  --bmc1_ucm_cone_mode                    none
% 27.48/3.93  --bmc1_ucm_reduced_relation_type        0
% 27.48/3.93  --bmc1_ucm_relax_model                  4
% 27.48/3.93  --bmc1_ucm_full_tr_after_sat            true
% 27.48/3.93  --bmc1_ucm_expand_neg_assumptions       false
% 27.48/3.93  --bmc1_ucm_layered_model                none
% 27.48/3.93  --bmc1_ucm_max_lemma_size               10
% 27.48/3.93  
% 27.48/3.93  ------ AIG Options
% 27.48/3.93  
% 27.48/3.93  --aig_mode                              false
% 27.48/3.93  
% 27.48/3.93  ------ Instantiation Options
% 27.48/3.93  
% 27.48/3.93  --instantiation_flag                    true
% 27.48/3.93  --inst_sos_flag                         true
% 27.48/3.93  --inst_sos_phase                        true
% 27.48/3.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.48/3.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.48/3.93  --inst_lit_sel_side                     num_symb
% 27.48/3.93  --inst_solver_per_active                1400
% 27.48/3.93  --inst_solver_calls_frac                1.
% 27.48/3.93  --inst_passive_queue_type               priority_queues
% 27.48/3.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.48/3.93  --inst_passive_queues_freq              [25;2]
% 27.48/3.93  --inst_dismatching                      true
% 27.48/3.93  --inst_eager_unprocessed_to_passive     true
% 27.48/3.93  --inst_prop_sim_given                   true
% 27.48/3.93  --inst_prop_sim_new                     false
% 27.48/3.93  --inst_subs_new                         false
% 27.48/3.93  --inst_eq_res_simp                      false
% 27.48/3.93  --inst_subs_given                       false
% 27.48/3.93  --inst_orphan_elimination               true
% 27.48/3.93  --inst_learning_loop_flag               true
% 27.48/3.93  --inst_learning_start                   3000
% 27.48/3.93  --inst_learning_factor                  2
% 27.48/3.93  --inst_start_prop_sim_after_learn       3
% 27.48/3.93  --inst_sel_renew                        solver
% 27.48/3.93  --inst_lit_activity_flag                true
% 27.48/3.93  --inst_restr_to_given                   false
% 27.48/3.93  --inst_activity_threshold               500
% 27.48/3.93  --inst_out_proof                        true
% 27.48/3.93  
% 27.48/3.93  ------ Resolution Options
% 27.48/3.93  
% 27.48/3.93  --resolution_flag                       true
% 27.48/3.93  --res_lit_sel                           adaptive
% 27.48/3.93  --res_lit_sel_side                      none
% 27.48/3.93  --res_ordering                          kbo
% 27.48/3.93  --res_to_prop_solver                    active
% 27.48/3.93  --res_prop_simpl_new                    false
% 27.48/3.93  --res_prop_simpl_given                  true
% 27.48/3.93  --res_passive_queue_type                priority_queues
% 27.48/3.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.48/3.93  --res_passive_queues_freq               [15;5]
% 27.48/3.93  --res_forward_subs                      full
% 27.48/3.93  --res_backward_subs                     full
% 27.48/3.93  --res_forward_subs_resolution           true
% 27.48/3.93  --res_backward_subs_resolution          true
% 27.48/3.93  --res_orphan_elimination                true
% 27.48/3.93  --res_time_limit                        2.
% 27.48/3.93  --res_out_proof                         true
% 27.48/3.93  
% 27.48/3.93  ------ Superposition Options
% 27.48/3.93  
% 27.48/3.93  --superposition_flag                    true
% 27.48/3.93  --sup_passive_queue_type                priority_queues
% 27.48/3.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.48/3.93  --sup_passive_queues_freq               [8;1;4]
% 27.48/3.93  --demod_completeness_check              fast
% 27.48/3.93  --demod_use_ground                      true
% 27.48/3.93  --sup_to_prop_solver                    passive
% 27.48/3.93  --sup_prop_simpl_new                    true
% 27.48/3.93  --sup_prop_simpl_given                  true
% 27.48/3.93  --sup_fun_splitting                     true
% 27.48/3.93  --sup_smt_interval                      50000
% 27.48/3.93  
% 27.48/3.93  ------ Superposition Simplification Setup
% 27.48/3.93  
% 27.48/3.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.48/3.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.48/3.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.48/3.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.48/3.93  --sup_full_triv                         [TrivRules;PropSubs]
% 27.48/3.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.48/3.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.48/3.93  --sup_immed_triv                        [TrivRules]
% 27.48/3.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.48/3.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.48/3.93  --sup_immed_bw_main                     []
% 27.48/3.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.48/3.93  --sup_input_triv                        [Unflattening;TrivRules]
% 27.48/3.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.81/3.93  --sup_input_bw                          []
% 27.81/3.93  
% 27.81/3.93  ------ Combination Options
% 27.81/3.93  
% 27.81/3.93  --comb_res_mult                         3
% 27.81/3.93  --comb_sup_mult                         2
% 27.81/3.93  --comb_inst_mult                        10
% 27.81/3.93  
% 27.81/3.93  ------ Debug Options
% 27.81/3.93  
% 27.81/3.93  --dbg_backtrace                         false
% 27.81/3.93  --dbg_dump_prop_clauses                 false
% 27.81/3.93  --dbg_dump_prop_clauses_file            -
% 27.81/3.93  --dbg_out_stat                          false
% 27.81/3.93  ------ Parsing...
% 27.81/3.93  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 27.81/3.93  
% 27.81/3.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 27.81/3.93  
% 27.81/3.93  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 27.81/3.93  
% 27.81/3.93  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 27.81/3.93  ------ Proving...
% 27.81/3.93  ------ Problem Properties 
% 27.81/3.93  
% 27.81/3.93  
% 27.81/3.93  clauses                                 37
% 27.81/3.93  conjectures                             8
% 27.81/3.93  EPR                                     6
% 27.81/3.93  Horn                                    37
% 27.81/3.93  unary                                   14
% 27.81/3.93  binary                                  13
% 27.81/3.93  lits                                    80
% 27.81/3.93  lits eq                                 28
% 27.81/3.93  fd_pure                                 0
% 27.81/3.93  fd_pseudo                               0
% 27.81/3.93  fd_cond                                 0
% 27.81/3.93  fd_pseudo_cond                          1
% 27.81/3.93  AC symbols                              0
% 27.81/3.93  
% 27.81/3.93  ------ Schedule dynamic 5 is on 
% 27.81/3.93  
% 27.81/3.93  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 27.81/3.93  
% 27.81/3.93  
% 27.81/3.93  ------ 
% 27.81/3.93  Current options:
% 27.81/3.93  ------ 
% 27.81/3.93  
% 27.81/3.93  ------ Input Options
% 27.81/3.93  
% 27.81/3.93  --out_options                           all
% 27.81/3.93  --tptp_safe_out                         true
% 27.81/3.93  --problem_path                          ""
% 27.81/3.93  --include_path                          ""
% 27.81/3.93  --clausifier                            res/vclausify_rel
% 27.81/3.93  --clausifier_options                    ""
% 27.81/3.93  --stdin                                 false
% 27.81/3.93  --stats_out                             all
% 27.81/3.93  
% 27.81/3.93  ------ General Options
% 27.81/3.93  
% 27.81/3.93  --fof                                   false
% 27.81/3.93  --time_out_real                         305.
% 27.81/3.93  --time_out_virtual                      -1.
% 27.81/3.93  --symbol_type_check                     false
% 27.81/3.93  --clausify_out                          false
% 27.81/3.93  --sig_cnt_out                           false
% 27.81/3.93  --trig_cnt_out                          false
% 27.81/3.93  --trig_cnt_out_tolerance                1.
% 27.81/3.93  --trig_cnt_out_sk_spl                   false
% 27.81/3.93  --abstr_cl_out                          false
% 27.81/3.93  
% 27.81/3.93  ------ Global Options
% 27.81/3.93  
% 27.81/3.93  --schedule                              default
% 27.81/3.93  --add_important_lit                     false
% 27.81/3.93  --prop_solver_per_cl                    1000
% 27.81/3.93  --min_unsat_core                        false
% 27.81/3.93  --soft_assumptions                      false
% 27.81/3.93  --soft_lemma_size                       3
% 27.81/3.93  --prop_impl_unit_size                   0
% 27.81/3.93  --prop_impl_unit                        []
% 27.81/3.93  --share_sel_clauses                     true
% 27.81/3.93  --reset_solvers                         false
% 27.81/3.93  --bc_imp_inh                            [conj_cone]
% 27.81/3.93  --conj_cone_tolerance                   3.
% 27.81/3.93  --extra_neg_conj                        none
% 27.81/3.93  --large_theory_mode                     true
% 27.81/3.93  --prolific_symb_bound                   200
% 27.81/3.93  --lt_threshold                          2000
% 27.81/3.93  --clause_weak_htbl                      true
% 27.81/3.93  --gc_record_bc_elim                     false
% 27.81/3.93  
% 27.81/3.93  ------ Preprocessing Options
% 27.81/3.93  
% 27.81/3.93  --preprocessing_flag                    true
% 27.81/3.93  --time_out_prep_mult                    0.1
% 27.81/3.93  --splitting_mode                        input
% 27.81/3.93  --splitting_grd                         true
% 27.81/3.93  --splitting_cvd                         false
% 27.81/3.93  --splitting_cvd_svl                     false
% 27.81/3.93  --splitting_nvd                         32
% 27.81/3.93  --sub_typing                            true
% 27.81/3.93  --prep_gs_sim                           true
% 27.81/3.93  --prep_unflatten                        true
% 27.81/3.93  --prep_res_sim                          true
% 27.81/3.93  --prep_upred                            true
% 27.81/3.93  --prep_sem_filter                       exhaustive
% 27.81/3.93  --prep_sem_filter_out                   false
% 27.81/3.93  --pred_elim                             true
% 27.81/3.93  --res_sim_input                         true
% 27.81/3.93  --eq_ax_congr_red                       true
% 27.81/3.93  --pure_diseq_elim                       true
% 27.81/3.93  --brand_transform                       false
% 27.81/3.93  --non_eq_to_eq                          false
% 27.81/3.93  --prep_def_merge                        true
% 27.81/3.93  --prep_def_merge_prop_impl              false
% 27.81/3.93  --prep_def_merge_mbd                    true
% 27.81/3.93  --prep_def_merge_tr_red                 false
% 27.81/3.93  --prep_def_merge_tr_cl                  false
% 27.81/3.93  --smt_preprocessing                     true
% 27.81/3.93  --smt_ac_axioms                         fast
% 27.81/3.93  --preprocessed_out                      false
% 27.81/3.93  --preprocessed_stats                    false
% 27.81/3.93  
% 27.81/3.93  ------ Abstraction refinement Options
% 27.81/3.93  
% 27.81/3.93  --abstr_ref                             []
% 27.81/3.93  --abstr_ref_prep                        false
% 27.81/3.93  --abstr_ref_until_sat                   false
% 27.81/3.93  --abstr_ref_sig_restrict                funpre
% 27.81/3.93  --abstr_ref_af_restrict_to_split_sk     false
% 27.81/3.93  --abstr_ref_under                       []
% 27.81/3.93  
% 27.81/3.93  ------ SAT Options
% 27.81/3.93  
% 27.81/3.93  --sat_mode                              false
% 27.81/3.93  --sat_fm_restart_options                ""
% 27.81/3.93  --sat_gr_def                            false
% 27.81/3.93  --sat_epr_types                         true
% 27.81/3.93  --sat_non_cyclic_types                  false
% 27.81/3.93  --sat_finite_models                     false
% 27.81/3.93  --sat_fm_lemmas                         false
% 27.81/3.93  --sat_fm_prep                           false
% 27.81/3.93  --sat_fm_uc_incr                        true
% 27.81/3.93  --sat_out_model                         small
% 27.81/3.93  --sat_out_clauses                       false
% 27.81/3.93  
% 27.81/3.93  ------ QBF Options
% 27.81/3.93  
% 27.81/3.93  --qbf_mode                              false
% 27.81/3.93  --qbf_elim_univ                         false
% 27.81/3.93  --qbf_dom_inst                          none
% 27.81/3.93  --qbf_dom_pre_inst                      false
% 27.81/3.93  --qbf_sk_in                             false
% 27.81/3.93  --qbf_pred_elim                         true
% 27.81/3.93  --qbf_split                             512
% 27.81/3.93  
% 27.81/3.93  ------ BMC1 Options
% 27.81/3.93  
% 27.81/3.93  --bmc1_incremental                      false
% 27.81/3.93  --bmc1_axioms                           reachable_all
% 27.81/3.93  --bmc1_min_bound                        0
% 27.81/3.93  --bmc1_max_bound                        -1
% 27.81/3.93  --bmc1_max_bound_default                -1
% 27.81/3.93  --bmc1_symbol_reachability              true
% 27.81/3.93  --bmc1_property_lemmas                  false
% 27.81/3.93  --bmc1_k_induction                      false
% 27.81/3.93  --bmc1_non_equiv_states                 false
% 27.81/3.93  --bmc1_deadlock                         false
% 27.81/3.93  --bmc1_ucm                              false
% 27.81/3.93  --bmc1_add_unsat_core                   none
% 27.81/3.93  --bmc1_unsat_core_children              false
% 27.81/3.93  --bmc1_unsat_core_extrapolate_axioms    false
% 27.81/3.93  --bmc1_out_stat                         full
% 27.81/3.93  --bmc1_ground_init                      false
% 27.81/3.93  --bmc1_pre_inst_next_state              false
% 27.81/3.93  --bmc1_pre_inst_state                   false
% 27.81/3.93  --bmc1_pre_inst_reach_state             false
% 27.81/3.93  --bmc1_out_unsat_core                   false
% 27.81/3.93  --bmc1_aig_witness_out                  false
% 27.81/3.93  --bmc1_verbose                          false
% 27.81/3.93  --bmc1_dump_clauses_tptp                false
% 27.81/3.93  --bmc1_dump_unsat_core_tptp             false
% 27.81/3.93  --bmc1_dump_file                        -
% 27.81/3.93  --bmc1_ucm_expand_uc_limit              128
% 27.81/3.93  --bmc1_ucm_n_expand_iterations          6
% 27.81/3.93  --bmc1_ucm_extend_mode                  1
% 27.81/3.93  --bmc1_ucm_init_mode                    2
% 27.81/3.93  --bmc1_ucm_cone_mode                    none
% 27.81/3.93  --bmc1_ucm_reduced_relation_type        0
% 27.81/3.93  --bmc1_ucm_relax_model                  4
% 27.81/3.93  --bmc1_ucm_full_tr_after_sat            true
% 27.81/3.93  --bmc1_ucm_expand_neg_assumptions       false
% 27.81/3.93  --bmc1_ucm_layered_model                none
% 27.81/3.93  --bmc1_ucm_max_lemma_size               10
% 27.81/3.93  
% 27.81/3.93  ------ AIG Options
% 27.81/3.93  
% 27.81/3.93  --aig_mode                              false
% 27.81/3.93  
% 27.81/3.93  ------ Instantiation Options
% 27.81/3.93  
% 27.81/3.93  --instantiation_flag                    true
% 27.81/3.93  --inst_sos_flag                         true
% 27.81/3.93  --inst_sos_phase                        true
% 27.81/3.93  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 27.81/3.93  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 27.81/3.93  --inst_lit_sel_side                     none
% 27.81/3.93  --inst_solver_per_active                1400
% 27.81/3.93  --inst_solver_calls_frac                1.
% 27.81/3.93  --inst_passive_queue_type               priority_queues
% 27.81/3.93  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 27.81/3.93  --inst_passive_queues_freq              [25;2]
% 27.81/3.93  --inst_dismatching                      true
% 27.81/3.93  --inst_eager_unprocessed_to_passive     true
% 27.81/3.93  --inst_prop_sim_given                   true
% 27.81/3.93  --inst_prop_sim_new                     false
% 27.81/3.93  --inst_subs_new                         false
% 27.81/3.93  --inst_eq_res_simp                      false
% 27.81/3.93  --inst_subs_given                       false
% 27.81/3.93  --inst_orphan_elimination               true
% 27.81/3.93  --inst_learning_loop_flag               true
% 27.81/3.93  --inst_learning_start                   3000
% 27.81/3.93  --inst_learning_factor                  2
% 27.81/3.93  --inst_start_prop_sim_after_learn       3
% 27.81/3.93  --inst_sel_renew                        solver
% 27.81/3.93  --inst_lit_activity_flag                true
% 27.81/3.93  --inst_restr_to_given                   false
% 27.81/3.93  --inst_activity_threshold               500
% 27.81/3.93  --inst_out_proof                        true
% 27.81/3.93  
% 27.81/3.93  ------ Resolution Options
% 27.81/3.93  
% 27.81/3.93  --resolution_flag                       false
% 27.81/3.93  --res_lit_sel                           adaptive
% 27.81/3.93  --res_lit_sel_side                      none
% 27.81/3.93  --res_ordering                          kbo
% 27.81/3.93  --res_to_prop_solver                    active
% 27.81/3.93  --res_prop_simpl_new                    false
% 27.81/3.93  --res_prop_simpl_given                  true
% 27.81/3.93  --res_passive_queue_type                priority_queues
% 27.81/3.93  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 27.81/3.93  --res_passive_queues_freq               [15;5]
% 27.81/3.93  --res_forward_subs                      full
% 27.81/3.93  --res_backward_subs                     full
% 27.81/3.93  --res_forward_subs_resolution           true
% 27.81/3.93  --res_backward_subs_resolution          true
% 27.81/3.93  --res_orphan_elimination                true
% 27.81/3.93  --res_time_limit                        2.
% 27.81/3.93  --res_out_proof                         true
% 27.81/3.93  
% 27.81/3.93  ------ Superposition Options
% 27.81/3.93  
% 27.81/3.93  --superposition_flag                    true
% 27.81/3.93  --sup_passive_queue_type                priority_queues
% 27.81/3.93  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 27.81/3.93  --sup_passive_queues_freq               [8;1;4]
% 27.81/3.93  --demod_completeness_check              fast
% 27.81/3.93  --demod_use_ground                      true
% 27.81/3.93  --sup_to_prop_solver                    passive
% 27.81/3.93  --sup_prop_simpl_new                    true
% 27.81/3.93  --sup_prop_simpl_given                  true
% 27.81/3.93  --sup_fun_splitting                     true
% 27.81/3.93  --sup_smt_interval                      50000
% 27.81/3.93  
% 27.81/3.93  ------ Superposition Simplification Setup
% 27.81/3.93  
% 27.81/3.93  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 27.81/3.93  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 27.81/3.93  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 27.81/3.93  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 27.81/3.93  --sup_full_triv                         [TrivRules;PropSubs]
% 27.81/3.93  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 27.81/3.93  --sup_full_bw                           [BwDemod;BwSubsumption]
% 27.81/3.93  --sup_immed_triv                        [TrivRules]
% 27.81/3.93  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 27.81/3.93  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.81/3.93  --sup_immed_bw_main                     []
% 27.81/3.93  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 27.81/3.93  --sup_input_triv                        [Unflattening;TrivRules]
% 27.81/3.93  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 27.81/3.93  --sup_input_bw                          []
% 27.81/3.93  
% 27.81/3.93  ------ Combination Options
% 27.81/3.93  
% 27.81/3.93  --comb_res_mult                         3
% 27.81/3.93  --comb_sup_mult                         2
% 27.81/3.93  --comb_inst_mult                        10
% 27.81/3.93  
% 27.81/3.93  ------ Debug Options
% 27.81/3.93  
% 27.81/3.93  --dbg_backtrace                         false
% 27.81/3.93  --dbg_dump_prop_clauses                 false
% 27.81/3.93  --dbg_dump_prop_clauses_file            -
% 27.81/3.93  --dbg_out_stat                          false
% 27.81/3.93  
% 27.81/3.93  
% 27.81/3.93  
% 27.81/3.93  
% 27.81/3.93  ------ Proving...
% 27.81/3.93  
% 27.81/3.93  
% 27.81/3.93  % SZS status Theorem for theBenchmark.p
% 27.81/3.93  
% 27.81/3.93  % SZS output start CNFRefutation for theBenchmark.p
% 27.81/3.93  
% 27.81/3.93  fof(f22,conjecture,(
% 27.81/3.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f23,negated_conjecture,(
% 27.81/3.93    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 27.81/3.93    inference(negated_conjecture,[],[f22])).
% 27.81/3.93  
% 27.81/3.93  fof(f52,plain,(
% 27.81/3.93    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 27.81/3.93    inference(ennf_transformation,[],[f23])).
% 27.81/3.93  
% 27.81/3.93  fof(f53,plain,(
% 27.81/3.93    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 27.81/3.93    inference(flattening,[],[f52])).
% 27.81/3.93  
% 27.81/3.93  fof(f59,plain,(
% 27.81/3.93    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 27.81/3.93    introduced(choice_axiom,[])).
% 27.81/3.93  
% 27.81/3.93  fof(f58,plain,(
% 27.81/3.93    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 27.81/3.93    introduced(choice_axiom,[])).
% 27.81/3.93  
% 27.81/3.93  fof(f60,plain,(
% 27.81/3.93    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 27.81/3.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f53,f59,f58])).
% 27.81/3.93  
% 27.81/3.93  fof(f98,plain,(
% 27.81/3.93    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 27.81/3.93    inference(cnf_transformation,[],[f60])).
% 27.81/3.93  
% 27.81/3.93  fof(f95,plain,(
% 27.81/3.93    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 27.81/3.93    inference(cnf_transformation,[],[f60])).
% 27.81/3.93  
% 27.81/3.93  fof(f19,axiom,(
% 27.81/3.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f48,plain,(
% 27.81/3.93    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 27.81/3.93    inference(ennf_transformation,[],[f19])).
% 27.81/3.93  
% 27.81/3.93  fof(f49,plain,(
% 27.81/3.93    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 27.81/3.93    inference(flattening,[],[f48])).
% 27.81/3.93  
% 27.81/3.93  fof(f89,plain,(
% 27.81/3.93    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f49])).
% 27.81/3.93  
% 27.81/3.93  fof(f93,plain,(
% 27.81/3.93    v1_funct_1(sK2)),
% 27.81/3.93    inference(cnf_transformation,[],[f60])).
% 27.81/3.93  
% 27.81/3.93  fof(f96,plain,(
% 27.81/3.93    v1_funct_1(sK3)),
% 27.81/3.93    inference(cnf_transformation,[],[f60])).
% 27.81/3.93  
% 27.81/3.93  fof(f17,axiom,(
% 27.81/3.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f46,plain,(
% 27.81/3.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 27.81/3.93    inference(ennf_transformation,[],[f17])).
% 27.81/3.93  
% 27.81/3.93  fof(f47,plain,(
% 27.81/3.93    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 27.81/3.93    inference(flattening,[],[f46])).
% 27.81/3.93  
% 27.81/3.93  fof(f87,plain,(
% 27.81/3.93    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f47])).
% 27.81/3.93  
% 27.81/3.93  fof(f14,axiom,(
% 27.81/3.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f42,plain,(
% 27.81/3.93    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.81/3.93    inference(ennf_transformation,[],[f14])).
% 27.81/3.93  
% 27.81/3.93  fof(f82,plain,(
% 27.81/3.93    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.81/3.93    inference(cnf_transformation,[],[f42])).
% 27.81/3.93  
% 27.81/3.93  fof(f10,axiom,(
% 27.81/3.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f34,plain,(
% 27.81/3.93    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.81/3.93    inference(ennf_transformation,[],[f10])).
% 27.81/3.93  
% 27.81/3.93  fof(f35,plain,(
% 27.81/3.93    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.81/3.93    inference(flattening,[],[f34])).
% 27.81/3.93  
% 27.81/3.93  fof(f75,plain,(
% 27.81/3.93    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f35])).
% 27.81/3.93  
% 27.81/3.93  fof(f5,axiom,(
% 27.81/3.93    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f29,plain,(
% 27.81/3.93    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 27.81/3.93    inference(ennf_transformation,[],[f5])).
% 27.81/3.93  
% 27.81/3.93  fof(f69,plain,(
% 27.81/3.93    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f29])).
% 27.81/3.93  
% 27.81/3.93  fof(f9,axiom,(
% 27.81/3.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f32,plain,(
% 27.81/3.93    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.81/3.93    inference(ennf_transformation,[],[f9])).
% 27.81/3.93  
% 27.81/3.93  fof(f33,plain,(
% 27.81/3.93    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.81/3.93    inference(flattening,[],[f32])).
% 27.81/3.93  
% 27.81/3.93  fof(f74,plain,(
% 27.81/3.93    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f33])).
% 27.81/3.93  
% 27.81/3.93  fof(f101,plain,(
% 27.81/3.93    v2_funct_1(sK2)),
% 27.81/3.93    inference(cnf_transformation,[],[f60])).
% 27.81/3.93  
% 27.81/3.93  fof(f21,axiom,(
% 27.81/3.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f50,plain,(
% 27.81/3.93    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 27.81/3.93    inference(ennf_transformation,[],[f21])).
% 27.81/3.93  
% 27.81/3.93  fof(f51,plain,(
% 27.81/3.93    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 27.81/3.93    inference(flattening,[],[f50])).
% 27.81/3.93  
% 27.81/3.93  fof(f92,plain,(
% 27.81/3.93    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f51])).
% 27.81/3.93  
% 27.81/3.93  fof(f94,plain,(
% 27.81/3.93    v1_funct_2(sK2,sK0,sK1)),
% 27.81/3.93    inference(cnf_transformation,[],[f60])).
% 27.81/3.93  
% 27.81/3.93  fof(f99,plain,(
% 27.81/3.93    k2_relset_1(sK0,sK1,sK2) = sK1),
% 27.81/3.93    inference(cnf_transformation,[],[f60])).
% 27.81/3.93  
% 27.81/3.93  fof(f103,plain,(
% 27.81/3.93    k1_xboole_0 != sK1),
% 27.81/3.93    inference(cnf_transformation,[],[f60])).
% 27.81/3.93  
% 27.81/3.93  fof(f16,axiom,(
% 27.81/3.93    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f44,plain,(
% 27.81/3.93    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 27.81/3.93    inference(ennf_transformation,[],[f16])).
% 27.81/3.93  
% 27.81/3.93  fof(f45,plain,(
% 27.81/3.93    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.81/3.93    inference(flattening,[],[f44])).
% 27.81/3.93  
% 27.81/3.93  fof(f57,plain,(
% 27.81/3.93    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.81/3.93    inference(nnf_transformation,[],[f45])).
% 27.81/3.93  
% 27.81/3.93  fof(f84,plain,(
% 27.81/3.93    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.81/3.93    inference(cnf_transformation,[],[f57])).
% 27.81/3.93  
% 27.81/3.93  fof(f100,plain,(
% 27.81/3.93    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 27.81/3.93    inference(cnf_transformation,[],[f60])).
% 27.81/3.93  
% 27.81/3.93  fof(f18,axiom,(
% 27.81/3.93    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f24,plain,(
% 27.81/3.93    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 27.81/3.93    inference(pure_predicate_removal,[],[f18])).
% 27.81/3.93  
% 27.81/3.93  fof(f88,plain,(
% 27.81/3.93    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 27.81/3.93    inference(cnf_transformation,[],[f24])).
% 27.81/3.93  
% 27.81/3.93  fof(f7,axiom,(
% 27.81/3.93    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f30,plain,(
% 27.81/3.93    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 27.81/3.93    inference(ennf_transformation,[],[f7])).
% 27.81/3.93  
% 27.81/3.93  fof(f72,plain,(
% 27.81/3.93    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f30])).
% 27.81/3.93  
% 27.81/3.93  fof(f20,axiom,(
% 27.81/3.93    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f90,plain,(
% 27.81/3.93    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f20])).
% 27.81/3.93  
% 27.81/3.93  fof(f107,plain,(
% 27.81/3.93    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(definition_unfolding,[],[f72,f90])).
% 27.81/3.93  
% 27.81/3.93  fof(f12,axiom,(
% 27.81/3.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f38,plain,(
% 27.81/3.93    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.81/3.93    inference(ennf_transformation,[],[f12])).
% 27.81/3.93  
% 27.81/3.93  fof(f39,plain,(
% 27.81/3.93    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.81/3.93    inference(flattening,[],[f38])).
% 27.81/3.93  
% 27.81/3.93  fof(f79,plain,(
% 27.81/3.93    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f39])).
% 27.81/3.93  
% 27.81/3.93  fof(f91,plain,(
% 27.81/3.93    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f51])).
% 27.81/3.93  
% 27.81/3.93  fof(f6,axiom,(
% 27.81/3.93    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f71,plain,(
% 27.81/3.93    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 27.81/3.93    inference(cnf_transformation,[],[f6])).
% 27.81/3.93  
% 27.81/3.93  fof(f105,plain,(
% 27.81/3.93    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 27.81/3.93    inference(definition_unfolding,[],[f71,f90])).
% 27.81/3.93  
% 27.81/3.93  fof(f15,axiom,(
% 27.81/3.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f25,plain,(
% 27.81/3.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 27.81/3.93    inference(pure_predicate_removal,[],[f15])).
% 27.81/3.93  
% 27.81/3.93  fof(f43,plain,(
% 27.81/3.93    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 27.81/3.93    inference(ennf_transformation,[],[f25])).
% 27.81/3.93  
% 27.81/3.93  fof(f83,plain,(
% 27.81/3.93    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 27.81/3.93    inference(cnf_transformation,[],[f43])).
% 27.81/3.93  
% 27.81/3.93  fof(f2,axiom,(
% 27.81/3.93    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f26,plain,(
% 27.81/3.93    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 27.81/3.93    inference(ennf_transformation,[],[f2])).
% 27.81/3.93  
% 27.81/3.93  fof(f56,plain,(
% 27.81/3.93    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 27.81/3.93    inference(nnf_transformation,[],[f26])).
% 27.81/3.93  
% 27.81/3.93  fof(f64,plain,(
% 27.81/3.93    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f56])).
% 27.81/3.93  
% 27.81/3.93  fof(f1,axiom,(
% 27.81/3.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f54,plain,(
% 27.81/3.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.81/3.93    inference(nnf_transformation,[],[f1])).
% 27.81/3.93  
% 27.81/3.93  fof(f55,plain,(
% 27.81/3.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 27.81/3.93    inference(flattening,[],[f54])).
% 27.81/3.93  
% 27.81/3.93  fof(f63,plain,(
% 27.81/3.93    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f55])).
% 27.81/3.93  
% 27.81/3.93  fof(f86,plain,(
% 27.81/3.93    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f47])).
% 27.81/3.93  
% 27.81/3.93  fof(f11,axiom,(
% 27.81/3.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f36,plain,(
% 27.81/3.93    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.81/3.93    inference(ennf_transformation,[],[f11])).
% 27.81/3.93  
% 27.81/3.93  fof(f37,plain,(
% 27.81/3.93    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.81/3.93    inference(flattening,[],[f36])).
% 27.81/3.93  
% 27.81/3.93  fof(f77,plain,(
% 27.81/3.93    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f37])).
% 27.81/3.93  
% 27.81/3.93  fof(f13,axiom,(
% 27.81/3.93    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0))))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f40,plain,(
% 27.81/3.93    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 27.81/3.93    inference(ennf_transformation,[],[f13])).
% 27.81/3.93  
% 27.81/3.93  fof(f41,plain,(
% 27.81/3.93    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 27.81/3.93    inference(flattening,[],[f40])).
% 27.81/3.93  
% 27.81/3.93  fof(f81,plain,(
% 27.81/3.93    ( ! [X0] : (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f41])).
% 27.81/3.93  
% 27.81/3.93  fof(f3,axiom,(
% 27.81/3.93    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f27,plain,(
% 27.81/3.93    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 27.81/3.93    inference(ennf_transformation,[],[f3])).
% 27.81/3.93  
% 27.81/3.93  fof(f66,plain,(
% 27.81/3.93    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f27])).
% 27.81/3.93  
% 27.81/3.93  fof(f8,axiom,(
% 27.81/3.93    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f31,plain,(
% 27.81/3.93    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 27.81/3.93    inference(ennf_transformation,[],[f8])).
% 27.81/3.93  
% 27.81/3.93  fof(f73,plain,(
% 27.81/3.93    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f31])).
% 27.81/3.93  
% 27.81/3.93  fof(f108,plain,(
% 27.81/3.93    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(definition_unfolding,[],[f73,f90])).
% 27.81/3.93  
% 27.81/3.93  fof(f4,axiom,(
% 27.81/3.93    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 27.81/3.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 27.81/3.93  
% 27.81/3.93  fof(f28,plain,(
% 27.81/3.93    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 27.81/3.93    inference(ennf_transformation,[],[f4])).
% 27.81/3.93  
% 27.81/3.93  fof(f68,plain,(
% 27.81/3.93    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 27.81/3.93    inference(cnf_transformation,[],[f28])).
% 27.81/3.93  
% 27.81/3.93  fof(f70,plain,(
% 27.81/3.93    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 27.81/3.93    inference(cnf_transformation,[],[f6])).
% 27.81/3.93  
% 27.81/3.93  fof(f106,plain,(
% 27.81/3.93    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 27.81/3.93    inference(definition_unfolding,[],[f70,f90])).
% 27.81/3.93  
% 27.81/3.93  fof(f104,plain,(
% 27.81/3.93    k2_funct_1(sK2) != sK3),
% 27.81/3.93    inference(cnf_transformation,[],[f60])).
% 27.81/3.93  
% 27.81/3.93  cnf(c_37,negated_conjecture,
% 27.81/3.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 27.81/3.93      inference(cnf_transformation,[],[f98]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1301,plain,
% 27.81/3.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_40,negated_conjecture,
% 27.81/3.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 27.81/3.93      inference(cnf_transformation,[],[f95]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1299,plain,
% 27.81/3.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_28,plain,
% 27.81/3.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.81/3.93      | ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v1_funct_1(X3)
% 27.81/3.93      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 27.81/3.93      inference(cnf_transformation,[],[f89]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1302,plain,
% 27.81/3.93      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 27.81/3.93      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 27.81/3.93      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.81/3.93      | v1_funct_1(X5) != iProver_top
% 27.81/3.93      | v1_funct_1(X4) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_3746,plain,
% 27.81/3.93      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 27.81/3.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.81/3.93      | v1_funct_1(X2) != iProver_top
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1299,c_1302]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_42,negated_conjecture,
% 27.81/3.93      ( v1_funct_1(sK2) ),
% 27.81/3.93      inference(cnf_transformation,[],[f93]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_43,plain,
% 27.81/3.93      ( v1_funct_1(sK2) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_3997,plain,
% 27.81/3.93      ( v1_funct_1(X2) != iProver_top
% 27.81/3.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.81/3.93      | k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_3746,c_43]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_3998,plain,
% 27.81/3.93      ( k1_partfun1(X0,X1,sK0,sK1,X2,sK2) = k5_relat_1(X2,sK2)
% 27.81/3.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.81/3.93      | v1_funct_1(X2) != iProver_top ),
% 27.81/3.93      inference(renaming,[status(thm)],[c_3997]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4005,plain,
% 27.81/3.93      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2)
% 27.81/3.93      | v1_funct_1(sK3) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1301,c_3998]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_39,negated_conjecture,
% 27.81/3.93      ( v1_funct_1(sK3) ),
% 27.81/3.93      inference(cnf_transformation,[],[f96]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_46,plain,
% 27.81/3.93      ( v1_funct_1(sK3) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4016,plain,
% 27.81/3.93      ( k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) = k5_relat_1(sK3,sK2) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_4005,c_46]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_25,plain,
% 27.81/3.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.81/3.93      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 27.81/3.93      | ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v1_funct_1(X3) ),
% 27.81/3.93      inference(cnf_transformation,[],[f87]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1305,plain,
% 27.81/3.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.81/3.93      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 27.81/3.93      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 27.81/3.93      | v1_funct_1(X0) != iProver_top
% 27.81/3.93      | v1_funct_1(X3) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4018,plain,
% 27.81/3.93      ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 27.81/3.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.81/3.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.81/3.93      | v1_funct_1(sK3) != iProver_top
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_4016,c_1305]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_45,plain,
% 27.81/3.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_48,plain,
% 27.81/3.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_5966,plain,
% 27.81/3.93      ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_4018,c_43,c_45,c_46,c_48]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_21,plain,
% 27.81/3.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | v1_relat_1(X0) ),
% 27.81/3.93      inference(cnf_transformation,[],[f82]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1306,plain,
% 27.81/3.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.81/3.93      | v1_relat_1(X0) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_5972,plain,
% 27.81/3.93      ( v1_relat_1(k5_relat_1(sK3,sK2)) = iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_5966,c_1306]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2403,plain,
% 27.81/3.93      ( v1_relat_1(sK2) = iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1299,c_1306]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1298,plain,
% 27.81/3.93      ( v1_funct_1(sK2) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_15,plain,
% 27.81/3.93      ( ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v1_relat_1(X0)
% 27.81/3.93      | v1_relat_1(k2_funct_1(X0)) ),
% 27.81/3.93      inference(cnf_transformation,[],[f75]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1308,plain,
% 27.81/3.93      ( v1_funct_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_8,plain,
% 27.81/3.93      ( ~ v1_relat_1(X0)
% 27.81/3.93      | ~ v1_relat_1(X1)
% 27.81/3.93      | ~ v1_relat_1(X2)
% 27.81/3.93      | k5_relat_1(k5_relat_1(X1,X0),X2) = k5_relat_1(X1,k5_relat_1(X0,X2)) ),
% 27.81/3.93      inference(cnf_transformation,[],[f69]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1312,plain,
% 27.81/3.93      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 27.81/3.93      | v1_relat_1(X1) != iProver_top
% 27.81/3.93      | v1_relat_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(X2) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2895,plain,
% 27.81/3.93      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 27.81/3.93      | v1_funct_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(X1) != iProver_top
% 27.81/3.93      | v1_relat_1(X2) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1308,c_1312]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_11254,plain,
% 27.81/3.93      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 27.81/3.93      | v1_relat_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(X1) != iProver_top
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1298,c_2895]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_13,plain,
% 27.81/3.93      ( ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v2_funct_1(X0)
% 27.81/3.93      | ~ v1_relat_1(X0)
% 27.81/3.93      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 27.81/3.93      inference(cnf_transformation,[],[f74]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_34,negated_conjecture,
% 27.81/3.93      ( v2_funct_1(sK2) ),
% 27.81/3.93      inference(cnf_transformation,[],[f101]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_576,plain,
% 27.81/3.93      ( ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v1_relat_1(X0)
% 27.81/3.93      | k2_funct_1(X0) = k4_relat_1(X0)
% 27.81/3.93      | sK2 != X0 ),
% 27.81/3.93      inference(resolution_lifted,[status(thm)],[c_13,c_34]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_577,plain,
% 27.81/3.93      ( ~ v1_funct_1(sK2)
% 27.81/3.93      | ~ v1_relat_1(sK2)
% 27.81/3.93      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 27.81/3.93      inference(unflattening,[status(thm)],[c_576]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_579,plain,
% 27.81/3.93      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_577,c_42]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1291,plain,
% 27.81/3.93      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_579]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1387,plain,
% 27.81/3.93      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.81/3.93      | v1_relat_1(sK2) ),
% 27.81/3.93      inference(instantiation,[status(thm)],[c_21]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1468,plain,
% 27.81/3.93      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.81/3.93      | v1_relat_1(sK2) ),
% 27.81/3.93      inference(instantiation,[status(thm)],[c_1387]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1756,plain,
% 27.81/3.93      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_1291,c_42,c_40,c_577,c_1468]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_11260,plain,
% 27.81/3.93      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
% 27.81/3.93      | v1_relat_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(X1) != iProver_top
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_11254,c_1756]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1469,plain,
% 27.81/3.93      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.81/3.93      | v1_relat_1(sK2) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_1468]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31293,plain,
% 27.81/3.93      ( v1_relat_1(X1) != iProver_top
% 27.81/3.93      | v1_relat_1(X0) != iProver_top
% 27.81/3.93      | k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_11260,c_45,c_1469]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31294,plain,
% 27.81/3.93      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),X0),X1)
% 27.81/3.93      | v1_relat_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(X1) != iProver_top ),
% 27.81/3.93      inference(renaming,[status(thm)],[c_31293]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31301,plain,
% 27.81/3.93      ( k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X0) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0))
% 27.81/3.93      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2403,c_31294]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_29,plain,
% 27.81/3.93      ( ~ v1_funct_2(X0,X1,X2)
% 27.81/3.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v2_funct_1(X0)
% 27.81/3.93      | k2_relset_1(X1,X2,X0) != X2
% 27.81/3.93      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 27.81/3.93      | k1_xboole_0 = X2 ),
% 27.81/3.93      inference(cnf_transformation,[],[f92]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_41,negated_conjecture,
% 27.81/3.93      ( v1_funct_2(sK2,sK0,sK1) ),
% 27.81/3.93      inference(cnf_transformation,[],[f94]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_502,plain,
% 27.81/3.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v2_funct_1(X0)
% 27.81/3.93      | k2_relset_1(X1,X2,X0) != X2
% 27.81/3.93      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 27.81/3.93      | sK0 != X1
% 27.81/3.93      | sK1 != X2
% 27.81/3.93      | sK2 != X0
% 27.81/3.93      | k1_xboole_0 = X2 ),
% 27.81/3.93      inference(resolution_lifted,[status(thm)],[c_29,c_41]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_503,plain,
% 27.81/3.93      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.81/3.93      | ~ v1_funct_1(sK2)
% 27.81/3.93      | ~ v2_funct_1(sK2)
% 27.81/3.93      | k2_relset_1(sK0,sK1,sK2) != sK1
% 27.81/3.93      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 27.81/3.93      | k1_xboole_0 = sK1 ),
% 27.81/3.93      inference(unflattening,[status(thm)],[c_502]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_36,negated_conjecture,
% 27.81/3.93      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 27.81/3.93      inference(cnf_transformation,[],[f99]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_32,negated_conjecture,
% 27.81/3.93      ( k1_xboole_0 != sK1 ),
% 27.81/3.93      inference(cnf_transformation,[],[f103]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_505,plain,
% 27.81/3.93      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_503,c_42,c_40,c_36,c_34,c_32]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1758,plain,
% 27.81/3.93      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
% 27.81/3.93      inference(demodulation,[status(thm)],[c_1756,c_505]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31308,plain,
% 27.81/3.93      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 27.81/3.93      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_31301,c_1758]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31345,plain,
% 27.81/3.93      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,k5_relat_1(sK3,sK2))) = k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_5972,c_31308]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2402,plain,
% 27.81/3.93      ( v1_relat_1(sK3) = iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1301,c_1306]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2896,plain,
% 27.81/3.93      ( k5_relat_1(sK2,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK2,X0),X1)
% 27.81/3.93      | v1_relat_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(X1) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2403,c_1312]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_3480,plain,
% 27.81/3.93      ( k5_relat_1(k5_relat_1(sK2,sK3),X0) = k5_relat_1(sK2,k5_relat_1(sK3,X0))
% 27.81/3.93      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2402,c_2896]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_3745,plain,
% 27.81/3.93      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 27.81/3.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.81/3.93      | v1_funct_1(X2) != iProver_top
% 27.81/3.93      | v1_funct_1(sK3) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1301,c_1302]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_3894,plain,
% 27.81/3.93      ( v1_funct_1(X2) != iProver_top
% 27.81/3.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.81/3.93      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_3745,c_46]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_3895,plain,
% 27.81/3.93      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 27.81/3.93      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 27.81/3.93      | v1_funct_1(X2) != iProver_top ),
% 27.81/3.93      inference(renaming,[status(thm)],[c_3894]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_3903,plain,
% 27.81/3.93      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1299,c_3895]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_24,plain,
% 27.81/3.93      ( ~ r2_relset_1(X0,X1,X2,X3)
% 27.81/3.93      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.81/3.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 27.81/3.93      | X3 = X2 ),
% 27.81/3.93      inference(cnf_transformation,[],[f84]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_35,negated_conjecture,
% 27.81/3.93      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 27.81/3.93      inference(cnf_transformation,[],[f100]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_443,plain,
% 27.81/3.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | X3 = X0
% 27.81/3.93      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 27.81/3.93      | k6_partfun1(sK0) != X3
% 27.81/3.93      | sK0 != X2
% 27.81/3.93      | sK0 != X1 ),
% 27.81/3.93      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_444,plain,
% 27.81/3.93      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 27.81/3.93      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 27.81/3.93      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 27.81/3.93      inference(unflattening,[status(thm)],[c_443]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_27,plain,
% 27.81/3.93      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 27.81/3.93      inference(cnf_transformation,[],[f88]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_61,plain,
% 27.81/3.93      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 27.81/3.93      inference(instantiation,[status(thm)],[c_27]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_446,plain,
% 27.81/3.93      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 27.81/3.93      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_444,c_61]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1296,plain,
% 27.81/3.93      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 27.81/3.93      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_446]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1374,plain,
% 27.81/3.93      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 27.81/3.93      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 27.81/3.93      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.81/3.93      | ~ v1_funct_1(sK3)
% 27.81/3.93      | ~ v1_funct_1(sK2) ),
% 27.81/3.93      inference(instantiation,[status(thm)],[c_25]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1908,plain,
% 27.81/3.93      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_1296,c_42,c_40,c_39,c_37,c_61,c_444,c_1374]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_3904,plain,
% 27.81/3.93      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_3903,c_1908]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4123,plain,
% 27.81/3.93      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_3904,c_43]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4132,plain,
% 27.81/3.93      ( k5_relat_1(sK2,k5_relat_1(sK3,X0)) = k5_relat_1(k6_partfun1(sK0),X0)
% 27.81/3.93      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_3480,c_4123]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4138,plain,
% 27.81/3.93      ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = k5_relat_1(k6_partfun1(sK0),sK2) ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2403,c_4132]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_11,plain,
% 27.81/3.93      ( ~ v1_relat_1(X0)
% 27.81/3.93      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 27.81/3.93      inference(cnf_transformation,[],[f107]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1311,plain,
% 27.81/3.93      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 27.81/3.93      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2467,plain,
% 27.81/3.93      ( k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2) = sK2 ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2403,c_1311]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_17,plain,
% 27.81/3.93      ( ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v2_funct_1(X0)
% 27.81/3.93      | ~ v1_relat_1(X0)
% 27.81/3.93      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 27.81/3.93      inference(cnf_transformation,[],[f79]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_562,plain,
% 27.81/3.93      ( ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v1_relat_1(X0)
% 27.81/3.93      | k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 27.81/3.93      | sK2 != X0 ),
% 27.81/3.93      inference(resolution_lifted,[status(thm)],[c_17,c_34]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_563,plain,
% 27.81/3.93      ( ~ v1_funct_1(sK2)
% 27.81/3.93      | ~ v1_relat_1(sK2)
% 27.81/3.93      | k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 27.81/3.93      inference(unflattening,[status(thm)],[c_562]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_565,plain,
% 27.81/3.93      ( ~ v1_relat_1(sK2)
% 27.81/3.93      | k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_563,c_42]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1292,plain,
% 27.81/3.93      ( k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_30,plain,
% 27.81/3.93      ( ~ v1_funct_2(X0,X1,X2)
% 27.81/3.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v2_funct_1(X0)
% 27.81/3.93      | k2_relset_1(X1,X2,X0) != X2
% 27.81/3.93      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 27.81/3.93      | k1_xboole_0 = X2 ),
% 27.81/3.93      inference(cnf_transformation,[],[f91]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_494,plain,
% 27.81/3.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v2_funct_1(X0)
% 27.81/3.93      | k2_relset_1(X1,X2,X0) != X2
% 27.81/3.93      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 27.81/3.93      | sK0 != X1
% 27.81/3.93      | sK1 != X2
% 27.81/3.93      | sK2 != X0
% 27.81/3.93      | k1_xboole_0 = X2 ),
% 27.81/3.93      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_495,plain,
% 27.81/3.93      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 27.81/3.93      | ~ v1_funct_1(sK2)
% 27.81/3.93      | ~ v2_funct_1(sK2)
% 27.81/3.93      | k2_relset_1(sK0,sK1,sK2) != sK1
% 27.81/3.93      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 27.81/3.93      | k1_xboole_0 = sK1 ),
% 27.81/3.93      inference(unflattening,[status(thm)],[c_494]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_497,plain,
% 27.81/3.93      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_495,c_42,c_40,c_36,c_34,c_32]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1318,plain,
% 27.81/3.93      ( k2_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_1292,c_497]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_9,plain,
% 27.81/3.93      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 27.81/3.93      inference(cnf_transformation,[],[f105]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1319,plain,
% 27.81/3.93      ( k1_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(demodulation,[status(thm)],[c_1318,c_9]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1331,plain,
% 27.81/3.93      ( ~ v1_relat_1(sK2) | k1_relat_1(sK2) = sK0 ),
% 27.81/3.93      inference(predicate_to_equality_rev,[status(thm)],[c_1319]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2035,plain,
% 27.81/3.93      ( k1_relat_1(sK2) = sK0 ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_1319,c_40,c_1331,c_1468]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2474,plain,
% 27.81/3.93      ( k5_relat_1(k6_partfun1(sK0),sK2) = sK2 ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_2467,c_2035]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4141,plain,
% 27.81/3.93      ( k5_relat_1(sK2,k5_relat_1(sK3,sK2)) = sK2 ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_4138,c_2474]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_22,plain,
% 27.81/3.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | v4_relat_1(X0,X1) ),
% 27.81/3.93      inference(cnf_transformation,[],[f83]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4,plain,
% 27.81/3.93      ( ~ v4_relat_1(X0,X1)
% 27.81/3.93      | r1_tarski(k1_relat_1(X0),X1)
% 27.81/3.93      | ~ v1_relat_1(X0) ),
% 27.81/3.93      inference(cnf_transformation,[],[f64]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_420,plain,
% 27.81/3.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | r1_tarski(k1_relat_1(X0),X1)
% 27.81/3.93      | ~ v1_relat_1(X0) ),
% 27.81/3.93      inference(resolution,[status(thm)],[c_22,c_4]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_424,plain,
% 27.81/3.93      ( r1_tarski(k1_relat_1(X0),X1)
% 27.81/3.93      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_420,c_21]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_425,plain,
% 27.81/3.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | r1_tarski(k1_relat_1(X0),X1) ),
% 27.81/3.93      inference(renaming,[status(thm)],[c_424]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1297,plain,
% 27.81/3.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.81/3.93      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_425]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_5973,plain,
% 27.81/3.93      ( r1_tarski(k1_relat_1(k5_relat_1(sK3,sK2)),sK1) = iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_5966,c_1297]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_0,plain,
% 27.81/3.93      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 27.81/3.93      inference(cnf_transformation,[],[f63]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1317,plain,
% 27.81/3.93      ( X0 = X1
% 27.81/3.93      | r1_tarski(X0,X1) != iProver_top
% 27.81/3.93      | r1_tarski(X1,X0) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_7889,plain,
% 27.81/3.93      ( k1_relat_1(k5_relat_1(sK3,sK2)) = sK1
% 27.81/3.93      | r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_5973,c_1317]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_26,plain,
% 27.81/3.93      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 27.81/3.93      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 27.81/3.93      | ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v1_funct_1(X3)
% 27.81/3.93      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) ),
% 27.81/3.93      inference(cnf_transformation,[],[f86]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1304,plain,
% 27.81/3.93      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 27.81/3.93      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 27.81/3.93      | v1_funct_1(X0) != iProver_top
% 27.81/3.93      | v1_funct_1(X3) != iProver_top
% 27.81/3.93      | v1_funct_1(k1_partfun1(X4,X5,X1,X2,X3,X0)) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4019,plain,
% 27.81/3.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.81/3.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.81/3.93      | v1_funct_1(k5_relat_1(sK3,sK2)) = iProver_top
% 27.81/3.93      | v1_funct_1(sK3) != iProver_top
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_4016,c_1304]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_16,plain,
% 27.81/3.93      ( r1_tarski(k2_relat_1(X0),k1_relat_1(X1))
% 27.81/3.93      | ~ v1_funct_1(X1)
% 27.81/3.93      | ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v1_relat_1(X0)
% 27.81/3.93      | ~ v1_relat_1(X1)
% 27.81/3.93      | k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0) ),
% 27.81/3.93      inference(cnf_transformation,[],[f77]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1307,plain,
% 27.81/3.93      ( k1_relat_1(k5_relat_1(X0,X1)) != k1_relat_1(X0)
% 27.81/3.93      | r1_tarski(k2_relat_1(X0),k1_relat_1(X1)) = iProver_top
% 27.81/3.93      | v1_funct_1(X0) != iProver_top
% 27.81/3.93      | v1_funct_1(X1) != iProver_top
% 27.81/3.93      | v1_relat_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(X1) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_7201,plain,
% 27.81/3.93      ( r1_tarski(k2_relat_1(sK2),k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top
% 27.81/3.93      | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top
% 27.81/3.93      | v1_relat_1(k5_relat_1(sK3,sK2)) != iProver_top
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_4141,c_1307]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_19,plain,
% 27.81/3.93      ( ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v2_funct_1(X0)
% 27.81/3.93      | ~ v1_relat_1(X0)
% 27.81/3.93      | k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0) ),
% 27.81/3.93      inference(cnf_transformation,[],[f81]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_534,plain,
% 27.81/3.93      ( ~ v1_funct_1(X0)
% 27.81/3.93      | ~ v1_relat_1(X0)
% 27.81/3.93      | k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) = k2_relat_1(X0)
% 27.81/3.93      | sK2 != X0 ),
% 27.81/3.93      inference(resolution_lifted,[status(thm)],[c_19,c_34]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_535,plain,
% 27.81/3.93      ( ~ v1_funct_1(sK2)
% 27.81/3.93      | ~ v1_relat_1(sK2)
% 27.81/3.93      | k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2) ),
% 27.81/3.93      inference(unflattening,[status(thm)],[c_534]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_537,plain,
% 27.81/3.93      ( ~ v1_relat_1(sK2)
% 27.81/3.93      | k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_535,c_42]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1294,plain,
% 27.81/3.93      ( k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) = k2_relat_1(sK2)
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_537]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1322,plain,
% 27.81/3.93      ( k2_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_1294,c_505]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1323,plain,
% 27.81/3.93      ( k2_relat_1(sK2) = sK1 | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(demodulation,[status(thm)],[c_1322,c_9]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1338,plain,
% 27.81/3.93      ( ~ v1_relat_1(sK2) | k2_relat_1(sK2) = sK1 ),
% 27.81/3.93      inference(predicate_to_equality_rev,[status(thm)],[c_1323]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2163,plain,
% 27.81/3.93      ( k2_relat_1(sK2) = sK1 ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_1323,c_40,c_1338,c_1468]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_7202,plain,
% 27.81/3.93      ( r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) = iProver_top
% 27.81/3.93      | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top
% 27.81/3.93      | v1_relat_1(k5_relat_1(sK3,sK2)) != iProver_top
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_7201,c_2163]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_11289,plain,
% 27.81/3.93      ( k1_relat_1(k5_relat_1(sK3,sK2)) = sK1 ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_7889,c_43,c_45,c_46,c_48,c_1469,c_4019,c_5972,c_7202]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_6130,plain,
% 27.81/3.93      ( k5_relat_1(k6_partfun1(k1_relat_1(k5_relat_1(sK3,sK2))),k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,sK2) ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_5972,c_1311]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_11292,plain,
% 27.81/3.93      ( k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) = k5_relat_1(sK3,sK2) ),
% 27.81/3.93      inference(demodulation,[status(thm)],[c_11289,c_6130]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31346,plain,
% 27.81/3.93      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 27.81/3.93      inference(light_normalisation,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_31345,c_1758,c_4141,c_11292]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_5961,plain,
% 27.81/3.93      ( v1_funct_1(k5_relat_1(sK3,sK2)) = iProver_top ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_4019,c_43,c_45,c_46,c_48]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31806,plain,
% 27.81/3.93      ( v1_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 27.81/3.93      inference(demodulation,[status(thm)],[c_31346,c_5961]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1303,plain,
% 27.81/3.93      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_3901,plain,
% 27.81/3.93      ( k1_partfun1(X0,X0,sK1,sK0,k6_partfun1(X0),sK3) = k5_relat_1(k6_partfun1(X0),sK3)
% 27.81/3.93      | v1_funct_1(k6_partfun1(X0)) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1303,c_3895]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_91543,plain,
% 27.81/3.93      ( k1_partfun1(sK1,sK1,sK1,sK0,k6_partfun1(sK1),sK3) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_31806,c_3901]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2897,plain,
% 27.81/3.93      ( k5_relat_1(sK3,k5_relat_1(X0,X1)) = k5_relat_1(k5_relat_1(sK3,X0),X1)
% 27.81/3.93      | v1_relat_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(X1) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2402,c_1312]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_5123,plain,
% 27.81/3.93      ( k5_relat_1(k5_relat_1(sK3,sK2),X0) = k5_relat_1(sK3,k5_relat_1(sK2,X0))
% 27.81/3.93      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2403,c_2897]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_5145,plain,
% 27.81/3.93      ( k5_relat_1(sK3,k5_relat_1(sK2,sK3)) = k5_relat_1(k5_relat_1(sK3,sK2),sK3) ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2402,c_5123]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_5147,plain,
% 27.81/3.93      ( k5_relat_1(k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_5145,c_4123]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31797,plain,
% 27.81/3.93      ( k5_relat_1(k6_partfun1(sK1),sK3) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
% 27.81/3.93      inference(demodulation,[status(thm)],[c_31346,c_5147]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31340,plain,
% 27.81/3.93      ( k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2402,c_31308]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_5,plain,
% 27.81/3.93      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 27.81/3.93      inference(cnf_transformation,[],[f66]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1315,plain,
% 27.81/3.93      ( v1_relat_1(X0) != iProver_top
% 27.81/3.93      | v1_relat_1(k4_relat_1(X0)) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_12,plain,
% 27.81/3.93      ( ~ v1_relat_1(X0)
% 27.81/3.93      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 27.81/3.93      inference(cnf_transformation,[],[f108]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1310,plain,
% 27.81/3.93      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 27.81/3.93      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2355,plain,
% 27.81/3.93      ( k5_relat_1(k4_relat_1(X0),k6_partfun1(k2_relat_1(k4_relat_1(X0)))) = k4_relat_1(X0)
% 27.81/3.93      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1315,c_1310]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4258,plain,
% 27.81/3.93      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2)))) = k4_relat_1(sK2) ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2403,c_2355]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_6,plain,
% 27.81/3.93      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 27.81/3.93      inference(cnf_transformation,[],[f68]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1314,plain,
% 27.81/3.93      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 27.81/3.93      | v1_relat_1(X0) != iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2469,plain,
% 27.81/3.93      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2403,c_1314]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2472,plain,
% 27.81/3.93      ( k2_relat_1(k4_relat_1(sK2)) = sK0 ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_2469,c_2035]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4263,plain,
% 27.81/3.93      ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k4_relat_1(sK2) ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_4258,c_2472]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31348,plain,
% 27.81/3.93      ( k5_relat_1(k6_partfun1(sK1),sK3) = k4_relat_1(sK2) ),
% 27.81/3.93      inference(light_normalisation,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_31340,c_4123,c_4263]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31814,plain,
% 27.81/3.93      ( k5_relat_1(sK3,k6_partfun1(sK0)) = k4_relat_1(sK2) ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_31797,c_31348]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_3900,plain,
% 27.81/3.93      ( k1_partfun1(X0,X1,sK1,sK0,k1_partfun1(X0,X2,X3,X1,X4,X5),sK3) = k5_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5),sK3)
% 27.81/3.93      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 27.81/3.93      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 27.81/3.93      | v1_funct_1(X5) != iProver_top
% 27.81/3.93      | v1_funct_1(X4) != iProver_top
% 27.81/3.93      | v1_funct_1(k1_partfun1(X0,X2,X3,X1,X4,X5)) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1305,c_3895]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_6186,plain,
% 27.81/3.93      ( k1_partfun1(sK1,sK1,sK1,sK0,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),sK3) = k5_relat_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2),sK3)
% 27.81/3.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.81/3.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.81/3.93      | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top
% 27.81/3.93      | v1_funct_1(sK3) != iProver_top
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_4016,c_3900]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_6189,plain,
% 27.81/3.93      ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k6_partfun1(sK0))
% 27.81/3.93      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.81/3.93      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 27.81/3.93      | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top
% 27.81/3.93      | v1_funct_1(sK3) != iProver_top
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_6186,c_4016,c_5147]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_5971,plain,
% 27.81/3.93      ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(k5_relat_1(sK3,sK2),sK3)
% 27.81/3.93      | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_5966,c_3895]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_5975,plain,
% 27.81/3.93      ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k6_partfun1(sK0))
% 27.81/3.93      | v1_funct_1(k5_relat_1(sK3,sK2)) != iProver_top ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_5971,c_5147]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_6370,plain,
% 27.81/3.93      ( k1_partfun1(sK1,sK1,sK1,sK0,k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_6189,c_43,c_45,c_46,c_48,c_4019,c_5975]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31803,plain,
% 27.81/3.93      ( k1_partfun1(sK1,sK1,sK1,sK0,k6_partfun1(sK1),sK3) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
% 27.81/3.93      inference(demodulation,[status(thm)],[c_31346,c_6370]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31815,plain,
% 27.81/3.93      ( k1_partfun1(sK1,sK1,sK1,sK0,k6_partfun1(sK1),sK3) = k4_relat_1(sK2) ),
% 27.81/3.93      inference(demodulation,[status(thm)],[c_31814,c_31803]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4126,plain,
% 27.81/3.93      ( k1_relat_1(k6_partfun1(sK0)) != k1_relat_1(sK2)
% 27.81/3.93      | r1_tarski(k2_relat_1(sK2),k1_relat_1(sK3)) = iProver_top
% 27.81/3.93      | v1_funct_1(sK3) != iProver_top
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top
% 27.81/3.93      | v1_relat_1(sK3) != iProver_top
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_4123,c_1307]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4127,plain,
% 27.81/3.93      ( k1_relat_1(k6_partfun1(sK0)) != sK0
% 27.81/3.93      | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
% 27.81/3.93      | v1_funct_1(sK3) != iProver_top
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top
% 27.81/3.93      | v1_relat_1(sK3) != iProver_top
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(light_normalisation,[status(thm)],[c_4126,c_2035,c_2163]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_10,plain,
% 27.81/3.93      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 27.81/3.93      inference(cnf_transformation,[],[f106]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4128,plain,
% 27.81/3.93      ( sK0 != sK0
% 27.81/3.93      | r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
% 27.81/3.93      | v1_funct_1(sK3) != iProver_top
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top
% 27.81/3.93      | v1_relat_1(sK3) != iProver_top
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(demodulation,[status(thm)],[c_4127,c_10]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_4129,plain,
% 27.81/3.93      ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top
% 27.81/3.93      | v1_funct_1(sK3) != iProver_top
% 27.81/3.93      | v1_funct_1(sK2) != iProver_top
% 27.81/3.93      | v1_relat_1(sK3) != iProver_top
% 27.81/3.93      | v1_relat_1(sK2) != iProver_top ),
% 27.81/3.93      inference(equality_resolution_simp,[status(thm)],[c_4128]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1561,plain,
% 27.81/3.93      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 27.81/3.93      | v1_relat_1(sK3) ),
% 27.81/3.93      inference(instantiation,[status(thm)],[c_21]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1562,plain,
% 27.81/3.93      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 27.81/3.93      | v1_relat_1(sK3) = iProver_top ),
% 27.81/3.93      inference(predicate_to_equality,[status(thm)],[c_1561]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_22125,plain,
% 27.81/3.93      ( r1_tarski(sK1,k1_relat_1(sK3)) = iProver_top ),
% 27.81/3.93      inference(global_propositional_subsumption,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_4129,c_43,c_45,c_46,c_48,c_1469,c_1562]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2038,plain,
% 27.81/3.93      ( r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_1301,c_1297]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2696,plain,
% 27.81/3.93      ( k1_relat_1(sK3) = sK1
% 27.81/3.93      | r1_tarski(sK1,k1_relat_1(sK3)) != iProver_top ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2038,c_1317]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_22130,plain,
% 27.81/3.93      ( k1_relat_1(sK3) = sK1 ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_22125,c_2696]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_2410,plain,
% 27.81/3.93      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 27.81/3.93      inference(superposition,[status(thm)],[c_2402,c_1311]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_90650,plain,
% 27.81/3.93      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 27.81/3.93      inference(demodulation,[status(thm)],[c_22130,c_2410]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_91544,plain,
% 27.81/3.93      ( k4_relat_1(sK2) = sK3 ),
% 27.81/3.93      inference(light_normalisation,
% 27.81/3.93                [status(thm)],
% 27.81/3.93                [c_91543,c_31815,c_90650]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_31,negated_conjecture,
% 27.81/3.93      ( k2_funct_1(sK2) != sK3 ),
% 27.81/3.93      inference(cnf_transformation,[],[f104]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(c_1760,plain,
% 27.81/3.93      ( k4_relat_1(sK2) != sK3 ),
% 27.81/3.93      inference(demodulation,[status(thm)],[c_1756,c_31]) ).
% 27.81/3.93  
% 27.81/3.93  cnf(contradiction,plain,
% 27.81/3.93      ( $false ),
% 27.81/3.93      inference(minisat,[status(thm)],[c_91544,c_1760]) ).
% 27.81/3.93  
% 27.81/3.93  
% 27.81/3.93  % SZS output end CNFRefutation for theBenchmark.p
% 27.81/3.93  
% 27.81/3.93  ------                               Statistics
% 27.81/3.93  
% 27.81/3.93  ------ General
% 27.81/3.93  
% 27.81/3.93  abstr_ref_over_cycles:                  0
% 27.81/3.93  abstr_ref_under_cycles:                 0
% 27.81/3.93  gc_basic_clause_elim:                   0
% 27.81/3.93  forced_gc_time:                         0
% 27.81/3.93  parsing_time:                           0.007
% 27.81/3.93  unif_index_cands_time:                  0.
% 27.81/3.93  unif_index_add_time:                    0.
% 27.81/3.93  orderings_time:                         0.
% 27.81/3.93  out_proof_time:                         0.027
% 27.81/3.93  total_time:                             3.302
% 27.81/3.93  num_of_symbols:                         54
% 27.81/3.93  num_of_terms:                           104136
% 27.81/3.93  
% 27.81/3.93  ------ Preprocessing
% 27.81/3.93  
% 27.81/3.93  num_of_splits:                          0
% 27.81/3.93  num_of_split_atoms:                     0
% 27.81/3.93  num_of_reused_defs:                     0
% 27.81/3.93  num_eq_ax_congr_red:                    3
% 27.81/3.93  num_of_sem_filtered_clauses:            1
% 27.81/3.93  num_of_subtypes:                        0
% 27.81/3.93  monotx_restored_types:                  0
% 27.81/3.93  sat_num_of_epr_types:                   0
% 27.81/3.93  sat_num_of_non_cyclic_types:            0
% 27.81/3.93  sat_guarded_non_collapsed_types:        0
% 27.81/3.93  num_pure_diseq_elim:                    0
% 27.81/3.93  simp_replaced_by:                       0
% 27.81/3.93  res_preprocessed:                       186
% 27.81/3.93  prep_upred:                             0
% 27.81/3.93  prep_unflattend:                        25
% 27.81/3.93  smt_new_axioms:                         0
% 27.81/3.93  pred_elim_cands:                        4
% 27.81/3.93  pred_elim:                              4
% 27.81/3.93  pred_elim_cl:                           5
% 27.81/3.93  pred_elim_cycles:                       6
% 27.81/3.93  merged_defs:                            0
% 27.81/3.93  merged_defs_ncl:                        0
% 27.81/3.93  bin_hyper_res:                          0
% 27.81/3.93  prep_cycles:                            4
% 27.81/3.93  pred_elim_time:                         0.004
% 27.81/3.93  splitting_time:                         0.
% 27.81/3.93  sem_filter_time:                        0.
% 27.81/3.93  monotx_time:                            0.
% 27.81/3.93  subtype_inf_time:                       0.
% 27.81/3.93  
% 27.81/3.93  ------ Problem properties
% 27.81/3.93  
% 27.81/3.93  clauses:                                37
% 27.81/3.93  conjectures:                            8
% 27.81/3.93  epr:                                    6
% 27.81/3.93  horn:                                   37
% 27.81/3.93  ground:                                 18
% 27.81/3.93  unary:                                  14
% 27.81/3.93  binary:                                 13
% 27.81/3.93  lits:                                   80
% 27.81/3.93  lits_eq:                                28
% 27.81/3.93  fd_pure:                                0
% 27.81/3.93  fd_pseudo:                              0
% 27.81/3.93  fd_cond:                                0
% 27.81/3.93  fd_pseudo_cond:                         1
% 27.81/3.93  ac_symbols:                             0
% 27.81/3.93  
% 27.81/3.93  ------ Propositional Solver
% 27.81/3.93  
% 27.81/3.93  prop_solver_calls:                      47
% 27.81/3.93  prop_fast_solver_calls:                 3623
% 27.81/3.93  smt_solver_calls:                       0
% 27.81/3.93  smt_fast_solver_calls:                  0
% 27.81/3.93  prop_num_of_clauses:                    44209
% 27.81/3.93  prop_preprocess_simplified:             76828
% 27.81/3.93  prop_fo_subsumed:                       519
% 27.81/3.93  prop_solver_time:                       0.
% 27.81/3.93  smt_solver_time:                        0.
% 27.81/3.93  smt_fast_solver_time:                   0.
% 27.81/3.93  prop_fast_solver_time:                  0.
% 27.81/3.93  prop_unsat_core_time:                   0.007
% 27.81/3.93  
% 27.81/3.93  ------ QBF
% 27.81/3.93  
% 27.81/3.93  qbf_q_res:                              0
% 27.81/3.93  qbf_num_tautologies:                    0
% 27.81/3.93  qbf_prep_cycles:                        0
% 27.81/3.93  
% 27.81/3.93  ------ BMC1
% 27.81/3.93  
% 27.81/3.93  bmc1_current_bound:                     -1
% 27.81/3.93  bmc1_last_solved_bound:                 -1
% 27.81/3.93  bmc1_unsat_core_size:                   -1
% 27.81/3.93  bmc1_unsat_core_parents_size:           -1
% 27.81/3.93  bmc1_merge_next_fun:                    0
% 27.81/3.93  bmc1_unsat_core_clauses_time:           0.
% 27.81/3.93  
% 27.81/3.93  ------ Instantiation
% 27.81/3.93  
% 27.81/3.93  inst_num_of_clauses:                    6023
% 27.81/3.93  inst_num_in_passive:                    3476
% 27.81/3.93  inst_num_in_active:                     4633
% 27.81/3.93  inst_num_in_unprocessed:                644
% 27.81/3.93  inst_num_of_loops:                      5129
% 27.81/3.93  inst_num_of_learning_restarts:          1
% 27.81/3.93  inst_num_moves_active_passive:          489
% 27.81/3.93  inst_lit_activity:                      0
% 27.81/3.93  inst_lit_activity_moves:                4
% 27.81/3.93  inst_num_tautologies:                   0
% 27.81/3.93  inst_num_prop_implied:                  0
% 27.81/3.93  inst_num_existing_simplified:           0
% 27.81/3.93  inst_num_eq_res_simplified:             0
% 27.81/3.93  inst_num_child_elim:                    0
% 27.81/3.93  inst_num_of_dismatching_blockings:      6646
% 27.81/3.93  inst_num_of_non_proper_insts:           13179
% 27.81/3.93  inst_num_of_duplicates:                 0
% 27.81/3.93  inst_inst_num_from_inst_to_res:         0
% 27.81/3.93  inst_dismatching_checking_time:         0.
% 27.81/3.93  
% 27.81/3.93  ------ Resolution
% 27.81/3.93  
% 27.81/3.93  res_num_of_clauses:                     53
% 27.81/3.93  res_num_in_passive:                     53
% 27.81/3.93  res_num_in_active:                      0
% 27.81/3.93  res_num_of_loops:                       190
% 27.81/3.93  res_forward_subset_subsumed:            1037
% 27.81/3.93  res_backward_subset_subsumed:           6
% 27.81/3.93  res_forward_subsumed:                   0
% 27.81/3.93  res_backward_subsumed:                  0
% 27.81/3.93  res_forward_subsumption_resolution:     0
% 27.81/3.93  res_backward_subsumption_resolution:    0
% 27.81/3.93  res_clause_to_clause_subsumption:       12179
% 27.81/3.93  res_orphan_elimination:                 0
% 27.81/3.93  res_tautology_del:                      919
% 27.81/3.93  res_num_eq_res_simplified:              0
% 27.81/3.93  res_num_sel_changes:                    0
% 27.81/3.93  res_moves_from_active_to_pass:          0
% 27.81/3.93  
% 27.81/3.93  ------ Superposition
% 27.81/3.93  
% 27.81/3.93  sup_time_total:                         0.
% 27.81/3.93  sup_time_generating:                    0.
% 27.81/3.93  sup_time_sim_full:                      0.
% 27.81/3.93  sup_time_sim_immed:                     0.
% 27.81/3.93  
% 27.81/3.93  sup_num_of_clauses:                     4823
% 27.81/3.93  sup_num_in_active:                      899
% 27.81/3.93  sup_num_in_passive:                     3924
% 27.81/3.93  sup_num_of_loops:                       1025
% 27.81/3.93  sup_fw_superposition:                   3396
% 27.81/3.93  sup_bw_superposition:                   2086
% 27.81/3.93  sup_immediate_simplified:               1726
% 27.81/3.93  sup_given_eliminated:                   3
% 27.81/3.93  comparisons_done:                       0
% 27.81/3.93  comparisons_avoided:                    0
% 27.81/3.93  
% 27.81/3.93  ------ Simplifications
% 27.81/3.93  
% 27.81/3.93  
% 27.81/3.93  sim_fw_subset_subsumed:                 35
% 27.81/3.93  sim_bw_subset_subsumed:                 72
% 27.81/3.93  sim_fw_subsumed:                        113
% 27.81/3.93  sim_bw_subsumed:                        11
% 27.81/3.93  sim_fw_subsumption_res:                 0
% 27.81/3.93  sim_bw_subsumption_res:                 0
% 27.81/3.93  sim_tautology_del:                      10
% 27.81/3.93  sim_eq_tautology_del:                   213
% 27.81/3.93  sim_eq_res_simp:                        21
% 27.81/3.93  sim_fw_demodulated:                     428
% 27.81/3.93  sim_bw_demodulated:                     132
% 27.81/3.93  sim_light_normalised:                   1441
% 27.81/3.93  sim_joinable_taut:                      0
% 27.81/3.93  sim_joinable_simp:                      0
% 27.81/3.93  sim_ac_normalised:                      0
% 27.81/3.93  sim_smt_subsumption:                    0
% 27.81/3.93  
%------------------------------------------------------------------------------
