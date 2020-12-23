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
% DateTime   : Thu Dec  3 12:01:41 EST 2020

% Result     : Theorem 7.05s
% Output     : CNFRefutation 7.05s
% Verified   : 
% Statistics : Number of formulae       :  154 (1029 expanded)
%              Number of clauses        :   94 ( 303 expanded)
%              Number of leaves         :   15 ( 255 expanded)
%              Depth                    :   20
%              Number of atoms          :  501 (7190 expanded)
%              Number of equality atoms :  229 (2464 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f49,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f50,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f49])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( k2_relset_1(X0,X1,X3) != X1
        & k1_xboole_0 != X2
        & v2_funct_1(sK4)
        & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k2_relset_1(sK0,sK1,sK3) != sK1
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( k2_relset_1(sK0,sK1,sK3) != sK1
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f50,f56,f55])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f92,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
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

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f44])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f91,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f57])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f90,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f83,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f93,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f96,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1727,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1729,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1735,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3107,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1729,c_1735])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_34])).

cnf(c_667,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_30,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_669,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_33,c_30])).

cnf(c_3112,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3107,c_669])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1730,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4261,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3112,c_1730])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_42,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_44,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1996,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1997,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1996])).

cnf(c_7746,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4261,c_42,c_44,c_1997])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1733,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_7762,plain,
    ( k4_relset_1(X0,X1,sK1,k2_relat_1(sK4),X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7746,c_1733])).

cnf(c_29958,plain,
    ( k4_relset_1(sK0,sK1,sK1,k2_relat_1(sK4),sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1727,c_7762])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1737,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_30248,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK4)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_29958,c_1737])).

cnf(c_41,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_31178,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_30248,c_41,c_42,c_44,c_1997,c_4261])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1734,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_31203,plain,
    ( k2_relset_1(sK0,k2_relat_1(sK4),k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_31178,c_1734])).

cnf(c_5362,plain,
    ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1733])).

cnf(c_5595,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1727,c_5362])).

cnf(c_6519,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5595,c_1737])).

cnf(c_8361,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6519,c_41,c_44])).

cnf(c_8373,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_8361,c_1734])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1731,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6663,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_1731])).

cnf(c_6810,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6663,c_42])).

cnf(c_6811,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6810])).

cnf(c_6825,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_6811])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2160,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2565,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2160])).

cnf(c_3033,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X0,X1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2565])).

cnf(c_3966,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_3033])).

cnf(c_6892,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6825,c_38,c_36,c_35,c_33,c_3966])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_6897,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_6892,c_32])).

cnf(c_8395,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_8373,c_6897])).

cnf(c_31254,plain,
    ( k2_relset_1(sK0,k2_relat_1(sK4),k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_31203,c_8395])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1738,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1743,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4038,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1738,c_1743])).

cnf(c_31204,plain,
    ( r1_tarski(k2_relset_1(sK0,k2_relat_1(sK4),k5_relat_1(sK3,sK4)),k2_relat_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_31178,c_4038])).

cnf(c_31255,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_31254,c_31204])).

cnf(c_9,plain,
    ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_486,plain,
    ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_31])).

cnf(c_487,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_491,plain,
    ( ~ v1_funct_1(X0)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_487,c_35])).

cnf(c_492,plain,
    ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(renaming,[status(thm)],[c_491])).

cnf(c_1724,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_492])).

cnf(c_488,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_487])).

cnf(c_2639,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1724,c_42,c_44,c_488,c_1997])).

cnf(c_2640,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2639])).

cnf(c_3252,plain,
    ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
    | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3112,c_2640])).

cnf(c_8439,plain,
    ( k2_relat_1(sK4) != sK2
    | r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_8395,c_3252])).

cnf(c_3058,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1729,c_1734])).

cnf(c_4037,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3058,c_1738])).

cnf(c_7151,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4037,c_44])).

cnf(c_7156,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_7151,c_1743])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1746,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_7319,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7156,c_1746])).

cnf(c_3059,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1727,c_1734])).

cnf(c_4035,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3059,c_1738])).

cnf(c_6592,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4035,c_41])).

cnf(c_6597,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_6592,c_1743])).

cnf(c_6807,plain,
    ( k2_relat_1(sK3) = sK1
    | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6597,c_1746])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_3458,plain,
    ( k2_relat_1(sK3) != sK1 ),
    inference(demodulation,[status(thm)],[c_3059,c_29])).

cnf(c_1999,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2000,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1999])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_31255,c_8439,c_7319,c_6807,c_3458,c_2000,c_41,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 12:09:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.05/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.05/1.49  
% 7.05/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.05/1.49  
% 7.05/1.49  ------  iProver source info
% 7.05/1.49  
% 7.05/1.49  git: date: 2020-06-30 10:37:57 +0100
% 7.05/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.05/1.49  git: non_committed_changes: false
% 7.05/1.49  git: last_make_outside_of_git: false
% 7.05/1.49  
% 7.05/1.49  ------ 
% 7.05/1.49  
% 7.05/1.49  ------ Input Options
% 7.05/1.49  
% 7.05/1.49  --out_options                           all
% 7.05/1.49  --tptp_safe_out                         true
% 7.05/1.49  --problem_path                          ""
% 7.05/1.49  --include_path                          ""
% 7.05/1.49  --clausifier                            res/vclausify_rel
% 7.05/1.49  --clausifier_options                    --mode clausify
% 7.05/1.49  --stdin                                 false
% 7.05/1.49  --stats_out                             all
% 7.05/1.49  
% 7.05/1.49  ------ General Options
% 7.05/1.49  
% 7.05/1.49  --fof                                   false
% 7.05/1.49  --time_out_real                         305.
% 7.05/1.49  --time_out_virtual                      -1.
% 7.05/1.49  --symbol_type_check                     false
% 7.05/1.49  --clausify_out                          false
% 7.05/1.49  --sig_cnt_out                           false
% 7.05/1.49  --trig_cnt_out                          false
% 7.05/1.49  --trig_cnt_out_tolerance                1.
% 7.05/1.49  --trig_cnt_out_sk_spl                   false
% 7.05/1.49  --abstr_cl_out                          false
% 7.05/1.49  
% 7.05/1.49  ------ Global Options
% 7.05/1.49  
% 7.05/1.49  --schedule                              default
% 7.05/1.49  --add_important_lit                     false
% 7.05/1.49  --prop_solver_per_cl                    1000
% 7.05/1.49  --min_unsat_core                        false
% 7.05/1.49  --soft_assumptions                      false
% 7.05/1.49  --soft_lemma_size                       3
% 7.05/1.49  --prop_impl_unit_size                   0
% 7.05/1.49  --prop_impl_unit                        []
% 7.05/1.49  --share_sel_clauses                     true
% 7.05/1.49  --reset_solvers                         false
% 7.05/1.49  --bc_imp_inh                            [conj_cone]
% 7.05/1.49  --conj_cone_tolerance                   3.
% 7.05/1.49  --extra_neg_conj                        none
% 7.05/1.49  --large_theory_mode                     true
% 7.05/1.49  --prolific_symb_bound                   200
% 7.05/1.49  --lt_threshold                          2000
% 7.05/1.49  --clause_weak_htbl                      true
% 7.05/1.49  --gc_record_bc_elim                     false
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing Options
% 7.05/1.49  
% 7.05/1.49  --preprocessing_flag                    true
% 7.05/1.49  --time_out_prep_mult                    0.1
% 7.05/1.49  --splitting_mode                        input
% 7.05/1.49  --splitting_grd                         true
% 7.05/1.49  --splitting_cvd                         false
% 7.05/1.49  --splitting_cvd_svl                     false
% 7.05/1.49  --splitting_nvd                         32
% 7.05/1.49  --sub_typing                            true
% 7.05/1.49  --prep_gs_sim                           true
% 7.05/1.49  --prep_unflatten                        true
% 7.05/1.49  --prep_res_sim                          true
% 7.05/1.49  --prep_upred                            true
% 7.05/1.49  --prep_sem_filter                       exhaustive
% 7.05/1.49  --prep_sem_filter_out                   false
% 7.05/1.49  --pred_elim                             true
% 7.05/1.49  --res_sim_input                         true
% 7.05/1.49  --eq_ax_congr_red                       true
% 7.05/1.49  --pure_diseq_elim                       true
% 7.05/1.49  --brand_transform                       false
% 7.05/1.49  --non_eq_to_eq                          false
% 7.05/1.49  --prep_def_merge                        true
% 7.05/1.49  --prep_def_merge_prop_impl              false
% 7.05/1.49  --prep_def_merge_mbd                    true
% 7.05/1.49  --prep_def_merge_tr_red                 false
% 7.05/1.49  --prep_def_merge_tr_cl                  false
% 7.05/1.49  --smt_preprocessing                     true
% 7.05/1.49  --smt_ac_axioms                         fast
% 7.05/1.49  --preprocessed_out                      false
% 7.05/1.49  --preprocessed_stats                    false
% 7.05/1.49  
% 7.05/1.49  ------ Abstraction refinement Options
% 7.05/1.49  
% 7.05/1.49  --abstr_ref                             []
% 7.05/1.49  --abstr_ref_prep                        false
% 7.05/1.49  --abstr_ref_until_sat                   false
% 7.05/1.49  --abstr_ref_sig_restrict                funpre
% 7.05/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.05/1.49  --abstr_ref_under                       []
% 7.05/1.49  
% 7.05/1.49  ------ SAT Options
% 7.05/1.49  
% 7.05/1.49  --sat_mode                              false
% 7.05/1.49  --sat_fm_restart_options                ""
% 7.05/1.49  --sat_gr_def                            false
% 7.05/1.49  --sat_epr_types                         true
% 7.05/1.49  --sat_non_cyclic_types                  false
% 7.05/1.49  --sat_finite_models                     false
% 7.05/1.49  --sat_fm_lemmas                         false
% 7.05/1.49  --sat_fm_prep                           false
% 7.05/1.49  --sat_fm_uc_incr                        true
% 7.05/1.49  --sat_out_model                         small
% 7.05/1.49  --sat_out_clauses                       false
% 7.05/1.49  
% 7.05/1.49  ------ QBF Options
% 7.05/1.49  
% 7.05/1.49  --qbf_mode                              false
% 7.05/1.49  --qbf_elim_univ                         false
% 7.05/1.49  --qbf_dom_inst                          none
% 7.05/1.49  --qbf_dom_pre_inst                      false
% 7.05/1.49  --qbf_sk_in                             false
% 7.05/1.49  --qbf_pred_elim                         true
% 7.05/1.49  --qbf_split                             512
% 7.05/1.49  
% 7.05/1.49  ------ BMC1 Options
% 7.05/1.49  
% 7.05/1.49  --bmc1_incremental                      false
% 7.05/1.49  --bmc1_axioms                           reachable_all
% 7.05/1.49  --bmc1_min_bound                        0
% 7.05/1.49  --bmc1_max_bound                        -1
% 7.05/1.49  --bmc1_max_bound_default                -1
% 7.05/1.49  --bmc1_symbol_reachability              true
% 7.05/1.49  --bmc1_property_lemmas                  false
% 7.05/1.49  --bmc1_k_induction                      false
% 7.05/1.49  --bmc1_non_equiv_states                 false
% 7.05/1.49  --bmc1_deadlock                         false
% 7.05/1.49  --bmc1_ucm                              false
% 7.05/1.49  --bmc1_add_unsat_core                   none
% 7.05/1.49  --bmc1_unsat_core_children              false
% 7.05/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.05/1.49  --bmc1_out_stat                         full
% 7.05/1.49  --bmc1_ground_init                      false
% 7.05/1.49  --bmc1_pre_inst_next_state              false
% 7.05/1.49  --bmc1_pre_inst_state                   false
% 7.05/1.49  --bmc1_pre_inst_reach_state             false
% 7.05/1.49  --bmc1_out_unsat_core                   false
% 7.05/1.49  --bmc1_aig_witness_out                  false
% 7.05/1.49  --bmc1_verbose                          false
% 7.05/1.49  --bmc1_dump_clauses_tptp                false
% 7.05/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.05/1.49  --bmc1_dump_file                        -
% 7.05/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.05/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.05/1.49  --bmc1_ucm_extend_mode                  1
% 7.05/1.49  --bmc1_ucm_init_mode                    2
% 7.05/1.49  --bmc1_ucm_cone_mode                    none
% 7.05/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.05/1.49  --bmc1_ucm_relax_model                  4
% 7.05/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.05/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.05/1.49  --bmc1_ucm_layered_model                none
% 7.05/1.49  --bmc1_ucm_max_lemma_size               10
% 7.05/1.49  
% 7.05/1.49  ------ AIG Options
% 7.05/1.49  
% 7.05/1.49  --aig_mode                              false
% 7.05/1.49  
% 7.05/1.49  ------ Instantiation Options
% 7.05/1.49  
% 7.05/1.49  --instantiation_flag                    true
% 7.05/1.49  --inst_sos_flag                         false
% 7.05/1.49  --inst_sos_phase                        true
% 7.05/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel_side                     num_symb
% 7.05/1.49  --inst_solver_per_active                1400
% 7.05/1.49  --inst_solver_calls_frac                1.
% 7.05/1.49  --inst_passive_queue_type               priority_queues
% 7.05/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.05/1.49  --inst_passive_queues_freq              [25;2]
% 7.05/1.49  --inst_dismatching                      true
% 7.05/1.49  --inst_eager_unprocessed_to_passive     true
% 7.05/1.49  --inst_prop_sim_given                   true
% 7.05/1.49  --inst_prop_sim_new                     false
% 7.05/1.49  --inst_subs_new                         false
% 7.05/1.49  --inst_eq_res_simp                      false
% 7.05/1.49  --inst_subs_given                       false
% 7.05/1.49  --inst_orphan_elimination               true
% 7.05/1.49  --inst_learning_loop_flag               true
% 7.05/1.49  --inst_learning_start                   3000
% 7.05/1.49  --inst_learning_factor                  2
% 7.05/1.49  --inst_start_prop_sim_after_learn       3
% 7.05/1.49  --inst_sel_renew                        solver
% 7.05/1.49  --inst_lit_activity_flag                true
% 7.05/1.49  --inst_restr_to_given                   false
% 7.05/1.49  --inst_activity_threshold               500
% 7.05/1.49  --inst_out_proof                        true
% 7.05/1.49  
% 7.05/1.49  ------ Resolution Options
% 7.05/1.49  
% 7.05/1.49  --resolution_flag                       true
% 7.05/1.49  --res_lit_sel                           adaptive
% 7.05/1.49  --res_lit_sel_side                      none
% 7.05/1.49  --res_ordering                          kbo
% 7.05/1.49  --res_to_prop_solver                    active
% 7.05/1.49  --res_prop_simpl_new                    false
% 7.05/1.49  --res_prop_simpl_given                  true
% 7.05/1.49  --res_passive_queue_type                priority_queues
% 7.05/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.05/1.49  --res_passive_queues_freq               [15;5]
% 7.05/1.49  --res_forward_subs                      full
% 7.05/1.49  --res_backward_subs                     full
% 7.05/1.49  --res_forward_subs_resolution           true
% 7.05/1.49  --res_backward_subs_resolution          true
% 7.05/1.49  --res_orphan_elimination                true
% 7.05/1.49  --res_time_limit                        2.
% 7.05/1.49  --res_out_proof                         true
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Options
% 7.05/1.49  
% 7.05/1.49  --superposition_flag                    true
% 7.05/1.49  --sup_passive_queue_type                priority_queues
% 7.05/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.05/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.05/1.49  --demod_completeness_check              fast
% 7.05/1.49  --demod_use_ground                      true
% 7.05/1.49  --sup_to_prop_solver                    passive
% 7.05/1.49  --sup_prop_simpl_new                    true
% 7.05/1.49  --sup_prop_simpl_given                  true
% 7.05/1.49  --sup_fun_splitting                     false
% 7.05/1.49  --sup_smt_interval                      50000
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Simplification Setup
% 7.05/1.49  
% 7.05/1.49  --sup_indices_passive                   []
% 7.05/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.05/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_full_bw                           [BwDemod]
% 7.05/1.49  --sup_immed_triv                        [TrivRules]
% 7.05/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_immed_bw_main                     []
% 7.05/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.05/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  
% 7.05/1.49  ------ Combination Options
% 7.05/1.49  
% 7.05/1.49  --comb_res_mult                         3
% 7.05/1.49  --comb_sup_mult                         2
% 7.05/1.49  --comb_inst_mult                        10
% 7.05/1.49  
% 7.05/1.49  ------ Debug Options
% 7.05/1.49  
% 7.05/1.49  --dbg_backtrace                         false
% 7.05/1.49  --dbg_dump_prop_clauses                 false
% 7.05/1.49  --dbg_dump_prop_clauses_file            -
% 7.05/1.49  --dbg_out_stat                          false
% 7.05/1.49  ------ Parsing...
% 7.05/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.05/1.49  ------ Proving...
% 7.05/1.49  ------ Problem Properties 
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  clauses                                 35
% 7.05/1.49  conjectures                             7
% 7.05/1.49  EPR                                     5
% 7.05/1.49  Horn                                    30
% 7.05/1.49  unary                                   9
% 7.05/1.49  binary                                  11
% 7.05/1.49  lits                                    89
% 7.05/1.49  lits eq                                 33
% 7.05/1.49  fd_pure                                 0
% 7.05/1.49  fd_pseudo                               0
% 7.05/1.49  fd_cond                                 1
% 7.05/1.49  fd_pseudo_cond                          1
% 7.05/1.49  AC symbols                              0
% 7.05/1.49  
% 7.05/1.49  ------ Schedule dynamic 5 is on 
% 7.05/1.49  
% 7.05/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  ------ 
% 7.05/1.49  Current options:
% 7.05/1.49  ------ 
% 7.05/1.49  
% 7.05/1.49  ------ Input Options
% 7.05/1.49  
% 7.05/1.49  --out_options                           all
% 7.05/1.49  --tptp_safe_out                         true
% 7.05/1.49  --problem_path                          ""
% 7.05/1.49  --include_path                          ""
% 7.05/1.49  --clausifier                            res/vclausify_rel
% 7.05/1.49  --clausifier_options                    --mode clausify
% 7.05/1.49  --stdin                                 false
% 7.05/1.49  --stats_out                             all
% 7.05/1.49  
% 7.05/1.49  ------ General Options
% 7.05/1.49  
% 7.05/1.49  --fof                                   false
% 7.05/1.49  --time_out_real                         305.
% 7.05/1.49  --time_out_virtual                      -1.
% 7.05/1.49  --symbol_type_check                     false
% 7.05/1.49  --clausify_out                          false
% 7.05/1.49  --sig_cnt_out                           false
% 7.05/1.49  --trig_cnt_out                          false
% 7.05/1.49  --trig_cnt_out_tolerance                1.
% 7.05/1.49  --trig_cnt_out_sk_spl                   false
% 7.05/1.49  --abstr_cl_out                          false
% 7.05/1.49  
% 7.05/1.49  ------ Global Options
% 7.05/1.49  
% 7.05/1.49  --schedule                              default
% 7.05/1.49  --add_important_lit                     false
% 7.05/1.49  --prop_solver_per_cl                    1000
% 7.05/1.49  --min_unsat_core                        false
% 7.05/1.49  --soft_assumptions                      false
% 7.05/1.49  --soft_lemma_size                       3
% 7.05/1.49  --prop_impl_unit_size                   0
% 7.05/1.49  --prop_impl_unit                        []
% 7.05/1.49  --share_sel_clauses                     true
% 7.05/1.49  --reset_solvers                         false
% 7.05/1.49  --bc_imp_inh                            [conj_cone]
% 7.05/1.49  --conj_cone_tolerance                   3.
% 7.05/1.49  --extra_neg_conj                        none
% 7.05/1.49  --large_theory_mode                     true
% 7.05/1.49  --prolific_symb_bound                   200
% 7.05/1.49  --lt_threshold                          2000
% 7.05/1.49  --clause_weak_htbl                      true
% 7.05/1.49  --gc_record_bc_elim                     false
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing Options
% 7.05/1.49  
% 7.05/1.49  --preprocessing_flag                    true
% 7.05/1.49  --time_out_prep_mult                    0.1
% 7.05/1.49  --splitting_mode                        input
% 7.05/1.49  --splitting_grd                         true
% 7.05/1.49  --splitting_cvd                         false
% 7.05/1.49  --splitting_cvd_svl                     false
% 7.05/1.49  --splitting_nvd                         32
% 7.05/1.49  --sub_typing                            true
% 7.05/1.49  --prep_gs_sim                           true
% 7.05/1.49  --prep_unflatten                        true
% 7.05/1.49  --prep_res_sim                          true
% 7.05/1.49  --prep_upred                            true
% 7.05/1.49  --prep_sem_filter                       exhaustive
% 7.05/1.49  --prep_sem_filter_out                   false
% 7.05/1.49  --pred_elim                             true
% 7.05/1.49  --res_sim_input                         true
% 7.05/1.49  --eq_ax_congr_red                       true
% 7.05/1.49  --pure_diseq_elim                       true
% 7.05/1.49  --brand_transform                       false
% 7.05/1.49  --non_eq_to_eq                          false
% 7.05/1.49  --prep_def_merge                        true
% 7.05/1.49  --prep_def_merge_prop_impl              false
% 7.05/1.49  --prep_def_merge_mbd                    true
% 7.05/1.49  --prep_def_merge_tr_red                 false
% 7.05/1.49  --prep_def_merge_tr_cl                  false
% 7.05/1.49  --smt_preprocessing                     true
% 7.05/1.49  --smt_ac_axioms                         fast
% 7.05/1.49  --preprocessed_out                      false
% 7.05/1.49  --preprocessed_stats                    false
% 7.05/1.49  
% 7.05/1.49  ------ Abstraction refinement Options
% 7.05/1.49  
% 7.05/1.49  --abstr_ref                             []
% 7.05/1.49  --abstr_ref_prep                        false
% 7.05/1.49  --abstr_ref_until_sat                   false
% 7.05/1.49  --abstr_ref_sig_restrict                funpre
% 7.05/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 7.05/1.49  --abstr_ref_under                       []
% 7.05/1.49  
% 7.05/1.49  ------ SAT Options
% 7.05/1.49  
% 7.05/1.49  --sat_mode                              false
% 7.05/1.49  --sat_fm_restart_options                ""
% 7.05/1.49  --sat_gr_def                            false
% 7.05/1.49  --sat_epr_types                         true
% 7.05/1.49  --sat_non_cyclic_types                  false
% 7.05/1.49  --sat_finite_models                     false
% 7.05/1.49  --sat_fm_lemmas                         false
% 7.05/1.49  --sat_fm_prep                           false
% 7.05/1.49  --sat_fm_uc_incr                        true
% 7.05/1.49  --sat_out_model                         small
% 7.05/1.49  --sat_out_clauses                       false
% 7.05/1.49  
% 7.05/1.49  ------ QBF Options
% 7.05/1.49  
% 7.05/1.49  --qbf_mode                              false
% 7.05/1.49  --qbf_elim_univ                         false
% 7.05/1.49  --qbf_dom_inst                          none
% 7.05/1.49  --qbf_dom_pre_inst                      false
% 7.05/1.49  --qbf_sk_in                             false
% 7.05/1.49  --qbf_pred_elim                         true
% 7.05/1.49  --qbf_split                             512
% 7.05/1.49  
% 7.05/1.49  ------ BMC1 Options
% 7.05/1.49  
% 7.05/1.49  --bmc1_incremental                      false
% 7.05/1.49  --bmc1_axioms                           reachable_all
% 7.05/1.49  --bmc1_min_bound                        0
% 7.05/1.49  --bmc1_max_bound                        -1
% 7.05/1.49  --bmc1_max_bound_default                -1
% 7.05/1.49  --bmc1_symbol_reachability              true
% 7.05/1.49  --bmc1_property_lemmas                  false
% 7.05/1.49  --bmc1_k_induction                      false
% 7.05/1.49  --bmc1_non_equiv_states                 false
% 7.05/1.49  --bmc1_deadlock                         false
% 7.05/1.49  --bmc1_ucm                              false
% 7.05/1.49  --bmc1_add_unsat_core                   none
% 7.05/1.49  --bmc1_unsat_core_children              false
% 7.05/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 7.05/1.49  --bmc1_out_stat                         full
% 7.05/1.49  --bmc1_ground_init                      false
% 7.05/1.49  --bmc1_pre_inst_next_state              false
% 7.05/1.49  --bmc1_pre_inst_state                   false
% 7.05/1.49  --bmc1_pre_inst_reach_state             false
% 7.05/1.49  --bmc1_out_unsat_core                   false
% 7.05/1.49  --bmc1_aig_witness_out                  false
% 7.05/1.49  --bmc1_verbose                          false
% 7.05/1.49  --bmc1_dump_clauses_tptp                false
% 7.05/1.49  --bmc1_dump_unsat_core_tptp             false
% 7.05/1.49  --bmc1_dump_file                        -
% 7.05/1.49  --bmc1_ucm_expand_uc_limit              128
% 7.05/1.49  --bmc1_ucm_n_expand_iterations          6
% 7.05/1.49  --bmc1_ucm_extend_mode                  1
% 7.05/1.49  --bmc1_ucm_init_mode                    2
% 7.05/1.49  --bmc1_ucm_cone_mode                    none
% 7.05/1.49  --bmc1_ucm_reduced_relation_type        0
% 7.05/1.49  --bmc1_ucm_relax_model                  4
% 7.05/1.49  --bmc1_ucm_full_tr_after_sat            true
% 7.05/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 7.05/1.49  --bmc1_ucm_layered_model                none
% 7.05/1.49  --bmc1_ucm_max_lemma_size               10
% 7.05/1.49  
% 7.05/1.49  ------ AIG Options
% 7.05/1.49  
% 7.05/1.49  --aig_mode                              false
% 7.05/1.49  
% 7.05/1.49  ------ Instantiation Options
% 7.05/1.49  
% 7.05/1.49  --instantiation_flag                    true
% 7.05/1.49  --inst_sos_flag                         false
% 7.05/1.49  --inst_sos_phase                        true
% 7.05/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.05/1.49  --inst_lit_sel_side                     none
% 7.05/1.49  --inst_solver_per_active                1400
% 7.05/1.49  --inst_solver_calls_frac                1.
% 7.05/1.49  --inst_passive_queue_type               priority_queues
% 7.05/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.05/1.49  --inst_passive_queues_freq              [25;2]
% 7.05/1.49  --inst_dismatching                      true
% 7.05/1.49  --inst_eager_unprocessed_to_passive     true
% 7.05/1.49  --inst_prop_sim_given                   true
% 7.05/1.49  --inst_prop_sim_new                     false
% 7.05/1.49  --inst_subs_new                         false
% 7.05/1.49  --inst_eq_res_simp                      false
% 7.05/1.49  --inst_subs_given                       false
% 7.05/1.49  --inst_orphan_elimination               true
% 7.05/1.49  --inst_learning_loop_flag               true
% 7.05/1.49  --inst_learning_start                   3000
% 7.05/1.49  --inst_learning_factor                  2
% 7.05/1.49  --inst_start_prop_sim_after_learn       3
% 7.05/1.49  --inst_sel_renew                        solver
% 7.05/1.49  --inst_lit_activity_flag                true
% 7.05/1.49  --inst_restr_to_given                   false
% 7.05/1.49  --inst_activity_threshold               500
% 7.05/1.49  --inst_out_proof                        true
% 7.05/1.49  
% 7.05/1.49  ------ Resolution Options
% 7.05/1.49  
% 7.05/1.49  --resolution_flag                       false
% 7.05/1.49  --res_lit_sel                           adaptive
% 7.05/1.49  --res_lit_sel_side                      none
% 7.05/1.49  --res_ordering                          kbo
% 7.05/1.49  --res_to_prop_solver                    active
% 7.05/1.49  --res_prop_simpl_new                    false
% 7.05/1.49  --res_prop_simpl_given                  true
% 7.05/1.49  --res_passive_queue_type                priority_queues
% 7.05/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.05/1.49  --res_passive_queues_freq               [15;5]
% 7.05/1.49  --res_forward_subs                      full
% 7.05/1.49  --res_backward_subs                     full
% 7.05/1.49  --res_forward_subs_resolution           true
% 7.05/1.49  --res_backward_subs_resolution          true
% 7.05/1.49  --res_orphan_elimination                true
% 7.05/1.49  --res_time_limit                        2.
% 7.05/1.49  --res_out_proof                         true
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Options
% 7.05/1.49  
% 7.05/1.49  --superposition_flag                    true
% 7.05/1.49  --sup_passive_queue_type                priority_queues
% 7.05/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.05/1.49  --sup_passive_queues_freq               [8;1;4]
% 7.05/1.49  --demod_completeness_check              fast
% 7.05/1.49  --demod_use_ground                      true
% 7.05/1.49  --sup_to_prop_solver                    passive
% 7.05/1.49  --sup_prop_simpl_new                    true
% 7.05/1.49  --sup_prop_simpl_given                  true
% 7.05/1.49  --sup_fun_splitting                     false
% 7.05/1.49  --sup_smt_interval                      50000
% 7.05/1.49  
% 7.05/1.49  ------ Superposition Simplification Setup
% 7.05/1.49  
% 7.05/1.49  --sup_indices_passive                   []
% 7.05/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 7.05/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 7.05/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_full_bw                           [BwDemod]
% 7.05/1.49  --sup_immed_triv                        [TrivRules]
% 7.05/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.05/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_immed_bw_main                     []
% 7.05/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 7.05/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 7.05/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 7.05/1.49  
% 7.05/1.49  ------ Combination Options
% 7.05/1.49  
% 7.05/1.49  --comb_res_mult                         3
% 7.05/1.49  --comb_sup_mult                         2
% 7.05/1.49  --comb_inst_mult                        10
% 7.05/1.49  
% 7.05/1.49  ------ Debug Options
% 7.05/1.49  
% 7.05/1.49  --dbg_backtrace                         false
% 7.05/1.49  --dbg_dump_prop_clauses                 false
% 7.05/1.49  --dbg_dump_prop_clauses_file            -
% 7.05/1.49  --dbg_out_stat                          false
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  ------ Proving...
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  % SZS status Theorem for theBenchmark.p
% 7.05/1.49  
% 7.05/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 7.05/1.49  
% 7.05/1.49  fof(f20,conjecture,(
% 7.05/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f21,negated_conjecture,(
% 7.05/1.49    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 7.05/1.49    inference(negated_conjecture,[],[f20])).
% 7.05/1.49  
% 7.05/1.49  fof(f49,plain,(
% 7.05/1.49    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.05/1.49    inference(ennf_transformation,[],[f21])).
% 7.05/1.49  
% 7.05/1.49  fof(f50,plain,(
% 7.05/1.49    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.05/1.49    inference(flattening,[],[f49])).
% 7.05/1.49  
% 7.05/1.49  fof(f56,plain,(
% 7.05/1.49    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 7.05/1.49    introduced(choice_axiom,[])).
% 7.05/1.49  
% 7.05/1.49  fof(f55,plain,(
% 7.05/1.49    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.05/1.49    introduced(choice_axiom,[])).
% 7.05/1.49  
% 7.05/1.49  fof(f57,plain,(
% 7.05/1.49    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.05/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f50,f56,f55])).
% 7.05/1.49  
% 7.05/1.49  fof(f89,plain,(
% 7.05/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.05/1.49    inference(cnf_transformation,[],[f57])).
% 7.05/1.49  
% 7.05/1.49  fof(f92,plain,(
% 7.05/1.49    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.05/1.49    inference(cnf_transformation,[],[f57])).
% 7.05/1.49  
% 7.05/1.49  fof(f13,axiom,(
% 7.05/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f38,plain,(
% 7.05/1.49    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.49    inference(ennf_transformation,[],[f13])).
% 7.05/1.49  
% 7.05/1.49  fof(f73,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.49    inference(cnf_transformation,[],[f38])).
% 7.05/1.49  
% 7.05/1.49  fof(f17,axiom,(
% 7.05/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f43,plain,(
% 7.05/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.49    inference(ennf_transformation,[],[f17])).
% 7.05/1.49  
% 7.05/1.49  fof(f44,plain,(
% 7.05/1.49    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.49    inference(flattening,[],[f43])).
% 7.05/1.49  
% 7.05/1.49  fof(f54,plain,(
% 7.05/1.49    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.49    inference(nnf_transformation,[],[f44])).
% 7.05/1.49  
% 7.05/1.49  fof(f77,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.49    inference(cnf_transformation,[],[f54])).
% 7.05/1.49  
% 7.05/1.49  fof(f91,plain,(
% 7.05/1.49    v1_funct_2(sK4,sK1,sK2)),
% 7.05/1.49    inference(cnf_transformation,[],[f57])).
% 7.05/1.49  
% 7.05/1.49  fof(f95,plain,(
% 7.05/1.49    k1_xboole_0 != sK2),
% 7.05/1.49    inference(cnf_transformation,[],[f57])).
% 7.05/1.49  
% 7.05/1.49  fof(f19,axiom,(
% 7.05/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f47,plain,(
% 7.05/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.05/1.49    inference(ennf_transformation,[],[f19])).
% 7.05/1.49  
% 7.05/1.49  fof(f48,plain,(
% 7.05/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.05/1.49    inference(flattening,[],[f47])).
% 7.05/1.49  
% 7.05/1.49  fof(f86,plain,(
% 7.05/1.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f48])).
% 7.05/1.49  
% 7.05/1.49  fof(f90,plain,(
% 7.05/1.49    v1_funct_1(sK4)),
% 7.05/1.49    inference(cnf_transformation,[],[f57])).
% 7.05/1.49  
% 7.05/1.49  fof(f8,axiom,(
% 7.05/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f32,plain,(
% 7.05/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.49    inference(ennf_transformation,[],[f8])).
% 7.05/1.49  
% 7.05/1.49  fof(f68,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.49    inference(cnf_transformation,[],[f32])).
% 7.05/1.49  
% 7.05/1.49  fof(f15,axiom,(
% 7.05/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f40,plain,(
% 7.05/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.05/1.49    inference(ennf_transformation,[],[f15])).
% 7.05/1.49  
% 7.05/1.49  fof(f41,plain,(
% 7.05/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.49    inference(flattening,[],[f40])).
% 7.05/1.49  
% 7.05/1.49  fof(f75,plain,(
% 7.05/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.49    inference(cnf_transformation,[],[f41])).
% 7.05/1.49  
% 7.05/1.49  fof(f11,axiom,(
% 7.05/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f35,plain,(
% 7.05/1.49    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.05/1.49    inference(ennf_transformation,[],[f11])).
% 7.05/1.49  
% 7.05/1.49  fof(f36,plain,(
% 7.05/1.49    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.49    inference(flattening,[],[f35])).
% 7.05/1.49  
% 7.05/1.49  fof(f71,plain,(
% 7.05/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.49    inference(cnf_transformation,[],[f36])).
% 7.05/1.49  
% 7.05/1.49  fof(f14,axiom,(
% 7.05/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f39,plain,(
% 7.05/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.49    inference(ennf_transformation,[],[f14])).
% 7.05/1.49  
% 7.05/1.49  fof(f74,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.49    inference(cnf_transformation,[],[f39])).
% 7.05/1.49  
% 7.05/1.49  fof(f18,axiom,(
% 7.05/1.49    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f45,plain,(
% 7.05/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.05/1.49    inference(ennf_transformation,[],[f18])).
% 7.05/1.49  
% 7.05/1.49  fof(f46,plain,(
% 7.05/1.49    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.05/1.49    inference(flattening,[],[f45])).
% 7.05/1.49  
% 7.05/1.49  fof(f83,plain,(
% 7.05/1.49    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f46])).
% 7.05/1.49  
% 7.05/1.49  fof(f87,plain,(
% 7.05/1.49    v1_funct_1(sK3)),
% 7.05/1.49    inference(cnf_transformation,[],[f57])).
% 7.05/1.49  
% 7.05/1.49  fof(f93,plain,(
% 7.05/1.49    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 7.05/1.49    inference(cnf_transformation,[],[f57])).
% 7.05/1.49  
% 7.05/1.49  fof(f10,axiom,(
% 7.05/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f34,plain,(
% 7.05/1.49    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.05/1.49    inference(ennf_transformation,[],[f10])).
% 7.05/1.49  
% 7.05/1.49  fof(f70,plain,(
% 7.05/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.05/1.49    inference(cnf_transformation,[],[f34])).
% 7.05/1.49  
% 7.05/1.49  fof(f2,axiom,(
% 7.05/1.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f53,plain,(
% 7.05/1.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.05/1.49    inference(nnf_transformation,[],[f2])).
% 7.05/1.49  
% 7.05/1.49  fof(f61,plain,(
% 7.05/1.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 7.05/1.49    inference(cnf_transformation,[],[f53])).
% 7.05/1.49  
% 7.05/1.49  fof(f7,axiom,(
% 7.05/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f30,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.05/1.49    inference(ennf_transformation,[],[f7])).
% 7.05/1.49  
% 7.05/1.49  fof(f31,plain,(
% 7.05/1.49    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.05/1.49    inference(flattening,[],[f30])).
% 7.05/1.49  
% 7.05/1.49  fof(f67,plain,(
% 7.05/1.49    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f31])).
% 7.05/1.49  
% 7.05/1.49  fof(f94,plain,(
% 7.05/1.49    v2_funct_1(sK4)),
% 7.05/1.49    inference(cnf_transformation,[],[f57])).
% 7.05/1.49  
% 7.05/1.49  fof(f1,axiom,(
% 7.05/1.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.05/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.05/1.49  
% 7.05/1.49  fof(f51,plain,(
% 7.05/1.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.05/1.49    inference(nnf_transformation,[],[f1])).
% 7.05/1.49  
% 7.05/1.49  fof(f52,plain,(
% 7.05/1.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.05/1.49    inference(flattening,[],[f51])).
% 7.05/1.49  
% 7.05/1.49  fof(f60,plain,(
% 7.05/1.49    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.05/1.49    inference(cnf_transformation,[],[f52])).
% 7.05/1.49  
% 7.05/1.49  fof(f96,plain,(
% 7.05/1.49    k2_relset_1(sK0,sK1,sK3) != sK1),
% 7.05/1.49    inference(cnf_transformation,[],[f57])).
% 7.05/1.49  
% 7.05/1.49  cnf(c_36,negated_conjecture,
% 7.05/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.05/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1727,plain,
% 7.05/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_33,negated_conjecture,
% 7.05/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.05/1.49      inference(cnf_transformation,[],[f92]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1729,plain,
% 7.05/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_15,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1735,plain,
% 7.05/1.49      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.05/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3107,plain,
% 7.05/1.49      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1729,c_1735]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_24,plain,
% 7.05/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.05/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.05/1.49      | k1_xboole_0 = X2 ),
% 7.05/1.49      inference(cnf_transformation,[],[f77]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_34,negated_conjecture,
% 7.05/1.49      ( v1_funct_2(sK4,sK1,sK2) ),
% 7.05/1.49      inference(cnf_transformation,[],[f91]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_666,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | k1_relset_1(X1,X2,X0) = X1
% 7.05/1.49      | sK4 != X0
% 7.05/1.49      | sK2 != X2
% 7.05/1.49      | sK1 != X1
% 7.05/1.49      | k1_xboole_0 = X2 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_24,c_34]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_667,plain,
% 7.05/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.05/1.49      | k1_relset_1(sK1,sK2,sK4) = sK1
% 7.05/1.49      | k1_xboole_0 = sK2 ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_666]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_30,negated_conjecture,
% 7.05/1.49      ( k1_xboole_0 != sK2 ),
% 7.05/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_669,plain,
% 7.05/1.49      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_667,c_33,c_30]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3112,plain,
% 7.05/1.49      ( k1_relat_1(sK4) = sK1 ),
% 7.05/1.49      inference(light_normalisation,[status(thm)],[c_3107,c_669]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_26,plain,
% 7.05/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_relat_1(X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1730,plain,
% 7.05/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 7.05/1.49      | v1_funct_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4261,plain,
% 7.05/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) = iProver_top
% 7.05/1.49      | v1_funct_1(sK4) != iProver_top
% 7.05/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_3112,c_1730]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_35,negated_conjecture,
% 7.05/1.49      ( v1_funct_1(sK4) ),
% 7.05/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_42,plain,
% 7.05/1.49      ( v1_funct_1(sK4) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_44,plain,
% 7.05/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_10,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | v1_relat_1(X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1996,plain,
% 7.05/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.05/1.49      | v1_relat_1(sK4) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1997,plain,
% 7.05/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.05/1.49      | v1_relat_1(sK4) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_1996]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_7746,plain,
% 7.05/1.49      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) = iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_4261,c_42,c_44,c_1997]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_17,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.05/1.49      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1733,plain,
% 7.05/1.49      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.05/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.05/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_7762,plain,
% 7.05/1.49      ( k4_relset_1(X0,X1,sK1,k2_relat_1(sK4),X2,sK4) = k5_relat_1(X2,sK4)
% 7.05/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_7746,c_1733]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_29958,plain,
% 7.05/1.49      ( k4_relset_1(sK0,sK1,sK1,k2_relat_1(sK4),sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1727,c_7762]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_13,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.05/1.49      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 7.05/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1737,plain,
% 7.05/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.05/1.49      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.05/1.49      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_30248,plain,
% 7.05/1.49      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK4)))) = iProver_top
% 7.05/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(sK4)))) != iProver_top
% 7.05/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_29958,c_1737]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_41,plain,
% 7.05/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_31178,plain,
% 7.05/1.49      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK4)))) = iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_30248,c_41,c_42,c_44,c_1997,c_4261]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_16,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f74]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1734,plain,
% 7.05/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.05/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_31203,plain,
% 7.05/1.49      ( k2_relset_1(sK0,k2_relat_1(sK4),k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_31178,c_1734]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_5362,plain,
% 7.05/1.49      ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 7.05/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1729,c_1733]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_5595,plain,
% 7.05/1.49      ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1727,c_5362]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6519,plain,
% 7.05/1.49      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 7.05/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.05/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_5595,c_1737]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_8361,plain,
% 7.05/1.49      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_6519,c_41,c_44]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_8373,plain,
% 7.05/1.49      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_8361,c_1734]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_25,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_funct_1(X3)
% 7.05/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1731,plain,
% 7.05/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.05/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.05/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.05/1.49      | v1_funct_1(X5) != iProver_top
% 7.05/1.49      | v1_funct_1(X4) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6663,plain,
% 7.05/1.49      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 7.05/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.05/1.49      | v1_funct_1(X2) != iProver_top
% 7.05/1.49      | v1_funct_1(sK4) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1729,c_1731]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6810,plain,
% 7.05/1.49      ( v1_funct_1(X2) != iProver_top
% 7.05/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.05/1.49      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_6663,c_42]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6811,plain,
% 7.05/1.49      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 7.05/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.05/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_6810]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6825,plain,
% 7.05/1.49      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 7.05/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1727,c_6811]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_38,negated_conjecture,
% 7.05/1.49      ( v1_funct_1(sK3) ),
% 7.05/1.49      inference(cnf_transformation,[],[f87]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2160,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_funct_1(sK4)
% 7.05/1.49      | k1_partfun1(X1,X2,X3,X4,X0,sK4) = k5_relat_1(X0,sK4) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_25]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2565,plain,
% 7.05/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.05/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 7.05/1.49      | ~ v1_funct_1(sK4)
% 7.05/1.49      | ~ v1_funct_1(sK3)
% 7.05/1.49      | k1_partfun1(X2,X3,X0,X1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_2160]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3033,plain,
% 7.05/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.05/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.05/1.49      | ~ v1_funct_1(sK4)
% 7.05/1.49      | ~ v1_funct_1(sK3)
% 7.05/1.49      | k1_partfun1(X0,X1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_2565]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3966,plain,
% 7.05/1.49      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.05/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.05/1.49      | ~ v1_funct_1(sK4)
% 7.05/1.49      | ~ v1_funct_1(sK3)
% 7.05/1.49      | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_3033]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6892,plain,
% 7.05/1.49      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_6825,c_38,c_36,c_35,c_33,c_3966]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_32,negated_conjecture,
% 7.05/1.49      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 7.05/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6897,plain,
% 7.05/1.49      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 7.05/1.49      inference(demodulation,[status(thm)],[c_6892,c_32]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_8395,plain,
% 7.05/1.49      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 7.05/1.49      inference(light_normalisation,[status(thm)],[c_8373,c_6897]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_31254,plain,
% 7.05/1.49      ( k2_relset_1(sK0,k2_relat_1(sK4),k5_relat_1(sK3,sK4)) = sK2 ),
% 7.05/1.49      inference(light_normalisation,[status(thm)],[c_31203,c_8395]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_12,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.05/1.49      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 7.05/1.49      inference(cnf_transformation,[],[f70]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1738,plain,
% 7.05/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.05/1.49      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4,plain,
% 7.05/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 7.05/1.49      inference(cnf_transformation,[],[f61]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1743,plain,
% 7.05/1.49      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 7.05/1.49      | r1_tarski(X0,X1) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4038,plain,
% 7.05/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.05/1.49      | r1_tarski(k2_relset_1(X1,X2,X0),X2) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1738,c_1743]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_31204,plain,
% 7.05/1.49      ( r1_tarski(k2_relset_1(sK0,k2_relat_1(sK4),k5_relat_1(sK3,sK4)),k2_relat_1(sK4)) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_31178,c_4038]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_31255,plain,
% 7.05/1.49      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 7.05/1.49      inference(demodulation,[status(thm)],[c_31254,c_31204]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_9,plain,
% 7.05/1.49      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 7.05/1.49      | ~ v2_funct_1(X0)
% 7.05/1.49      | ~ v1_funct_1(X1)
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_relat_1(X1)
% 7.05/1.49      | ~ v1_relat_1(X0)
% 7.05/1.49      | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) ),
% 7.05/1.49      inference(cnf_transformation,[],[f67]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_31,negated_conjecture,
% 7.05/1.49      ( v2_funct_1(sK4) ),
% 7.05/1.49      inference(cnf_transformation,[],[f94]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_486,plain,
% 7.05/1.49      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 7.05/1.49      | ~ v1_funct_1(X1)
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_relat_1(X1)
% 7.05/1.49      | ~ v1_relat_1(X0)
% 7.05/1.49      | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0)
% 7.05/1.49      | sK4 != X0 ),
% 7.05/1.49      inference(resolution_lifted,[status(thm)],[c_9,c_31]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_487,plain,
% 7.05/1.49      ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_funct_1(sK4)
% 7.05/1.49      | ~ v1_relat_1(X0)
% 7.05/1.49      | ~ v1_relat_1(sK4)
% 7.05/1.49      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 7.05/1.49      inference(unflattening,[status(thm)],[c_486]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_491,plain,
% 7.05/1.49      ( ~ v1_funct_1(X0)
% 7.05/1.49      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 7.05/1.49      | ~ v1_relat_1(X0)
% 7.05/1.49      | ~ v1_relat_1(sK4)
% 7.05/1.49      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_487,c_35]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_492,plain,
% 7.05/1.49      ( r1_tarski(k1_relat_1(sK4),k2_relat_1(X0))
% 7.05/1.49      | ~ v1_funct_1(X0)
% 7.05/1.49      | ~ v1_relat_1(X0)
% 7.05/1.49      | ~ v1_relat_1(sK4)
% 7.05/1.49      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_491]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1724,plain,
% 7.05/1.49      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 7.05/1.49      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 7.05/1.49      | v1_funct_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_492]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_488,plain,
% 7.05/1.49      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 7.05/1.49      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 7.05/1.49      | v1_funct_1(X0) != iProver_top
% 7.05/1.49      | v1_funct_1(sK4) != iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(sK4) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_487]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2639,plain,
% 7.05/1.49      ( v1_relat_1(X0) != iProver_top
% 7.05/1.49      | v1_funct_1(X0) != iProver_top
% 7.05/1.49      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 7.05/1.49      | k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4) ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_1724,c_42,c_44,c_488,c_1997]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2640,plain,
% 7.05/1.49      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 7.05/1.49      | r1_tarski(k1_relat_1(sK4),k2_relat_1(X0)) = iProver_top
% 7.05/1.49      | v1_funct_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.05/1.49      inference(renaming,[status(thm)],[c_2639]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3252,plain,
% 7.05/1.49      ( k2_relat_1(k5_relat_1(X0,sK4)) != k2_relat_1(sK4)
% 7.05/1.49      | r1_tarski(sK1,k2_relat_1(X0)) = iProver_top
% 7.05/1.49      | v1_funct_1(X0) != iProver_top
% 7.05/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.05/1.49      inference(demodulation,[status(thm)],[c_3112,c_2640]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_8439,plain,
% 7.05/1.49      ( k2_relat_1(sK4) != sK2
% 7.05/1.49      | r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top
% 7.05/1.49      | v1_funct_1(sK3) != iProver_top
% 7.05/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_8395,c_3252]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3058,plain,
% 7.05/1.49      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1729,c_1734]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4037,plain,
% 7.05/1.49      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
% 7.05/1.49      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_3058,c_1738]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_7151,plain,
% 7.05/1.49      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_4037,c_44]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_7156,plain,
% 7.05/1.49      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_7151,c_1743]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_0,plain,
% 7.05/1.49      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.05/1.49      inference(cnf_transformation,[],[f60]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1746,plain,
% 7.05/1.49      ( X0 = X1
% 7.05/1.49      | r1_tarski(X0,X1) != iProver_top
% 7.05/1.49      | r1_tarski(X1,X0) != iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_7319,plain,
% 7.05/1.49      ( k2_relat_1(sK4) = sK2
% 7.05/1.49      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_7156,c_1746]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3059,plain,
% 7.05/1.49      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_1727,c_1734]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_4035,plain,
% 7.05/1.49      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
% 7.05/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_3059,c_1738]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6592,plain,
% 7.05/1.49      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
% 7.05/1.49      inference(global_propositional_subsumption,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_4035,c_41]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6597,plain,
% 7.05/1.49      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_6592,c_1743]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_6807,plain,
% 7.05/1.49      ( k2_relat_1(sK3) = sK1
% 7.05/1.49      | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
% 7.05/1.49      inference(superposition,[status(thm)],[c_6597,c_1746]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_29,negated_conjecture,
% 7.05/1.49      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 7.05/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_3458,plain,
% 7.05/1.49      ( k2_relat_1(sK3) != sK1 ),
% 7.05/1.49      inference(demodulation,[status(thm)],[c_3059,c_29]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_1999,plain,
% 7.05/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.05/1.49      | v1_relat_1(sK3) ),
% 7.05/1.49      inference(instantiation,[status(thm)],[c_10]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_2000,plain,
% 7.05/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.05/1.49      | v1_relat_1(sK3) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_1999]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(c_39,plain,
% 7.05/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.05/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.05/1.49  
% 7.05/1.49  cnf(contradiction,plain,
% 7.05/1.49      ( $false ),
% 7.05/1.49      inference(minisat,
% 7.05/1.49                [status(thm)],
% 7.05/1.49                [c_31255,c_8439,c_7319,c_6807,c_3458,c_2000,c_41,c_39]) ).
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.05/1.49  
% 7.05/1.49  ------                               Statistics
% 7.05/1.49  
% 7.05/1.49  ------ General
% 7.05/1.49  
% 7.05/1.49  abstr_ref_over_cycles:                  0
% 7.05/1.49  abstr_ref_under_cycles:                 0
% 7.05/1.49  gc_basic_clause_elim:                   0
% 7.05/1.49  forced_gc_time:                         0
% 7.05/1.49  parsing_time:                           0.009
% 7.05/1.49  unif_index_cands_time:                  0.
% 7.05/1.49  unif_index_add_time:                    0.
% 7.05/1.49  orderings_time:                         0.
% 7.05/1.49  out_proof_time:                         0.016
% 7.05/1.49  total_time:                             0.91
% 7.05/1.49  num_of_symbols:                         57
% 7.05/1.49  num_of_terms:                           40472
% 7.05/1.49  
% 7.05/1.49  ------ Preprocessing
% 7.05/1.49  
% 7.05/1.49  num_of_splits:                          0
% 7.05/1.49  num_of_split_atoms:                     0
% 7.05/1.49  num_of_reused_defs:                     0
% 7.05/1.49  num_eq_ax_congr_red:                    55
% 7.05/1.49  num_of_sem_filtered_clauses:            1
% 7.05/1.49  num_of_subtypes:                        0
% 7.05/1.49  monotx_restored_types:                  0
% 7.05/1.49  sat_num_of_epr_types:                   0
% 7.05/1.49  sat_num_of_non_cyclic_types:            0
% 7.05/1.49  sat_guarded_non_collapsed_types:        0
% 7.05/1.49  num_pure_diseq_elim:                    0
% 7.05/1.49  simp_replaced_by:                       0
% 7.05/1.49  res_preprocessed:                       173
% 7.05/1.49  prep_upred:                             0
% 7.05/1.49  prep_unflattend:                        42
% 7.05/1.49  smt_new_axioms:                         0
% 7.05/1.49  pred_elim_cands:                        4
% 7.05/1.49  pred_elim:                              3
% 7.05/1.49  pred_elim_cl:                           2
% 7.05/1.49  pred_elim_cycles:                       5
% 7.05/1.49  merged_defs:                            8
% 7.05/1.49  merged_defs_ncl:                        0
% 7.05/1.49  bin_hyper_res:                          8
% 7.05/1.49  prep_cycles:                            4
% 7.05/1.49  pred_elim_time:                         0.006
% 7.05/1.49  splitting_time:                         0.
% 7.05/1.49  sem_filter_time:                        0.
% 7.05/1.49  monotx_time:                            0.
% 7.05/1.49  subtype_inf_time:                       0.
% 7.05/1.49  
% 7.05/1.49  ------ Problem properties
% 7.05/1.49  
% 7.05/1.49  clauses:                                35
% 7.05/1.49  conjectures:                            7
% 7.05/1.49  epr:                                    5
% 7.05/1.49  horn:                                   30
% 7.05/1.49  ground:                                 13
% 7.05/1.49  unary:                                  9
% 7.05/1.49  binary:                                 11
% 7.05/1.49  lits:                                   89
% 7.05/1.49  lits_eq:                                33
% 7.05/1.49  fd_pure:                                0
% 7.05/1.49  fd_pseudo:                              0
% 7.05/1.49  fd_cond:                                1
% 7.05/1.49  fd_pseudo_cond:                         1
% 7.05/1.49  ac_symbols:                             0
% 7.05/1.49  
% 7.05/1.49  ------ Propositional Solver
% 7.05/1.49  
% 7.05/1.49  prop_solver_calls:                      30
% 7.05/1.49  prop_fast_solver_calls:                 1782
% 7.05/1.49  smt_solver_calls:                       0
% 7.05/1.49  smt_fast_solver_calls:                  0
% 7.05/1.49  prop_num_of_clauses:                    13015
% 7.05/1.49  prop_preprocess_simplified:             19614
% 7.05/1.49  prop_fo_subsumed:                       76
% 7.05/1.49  prop_solver_time:                       0.
% 7.05/1.49  smt_solver_time:                        0.
% 7.05/1.49  smt_fast_solver_time:                   0.
% 7.05/1.49  prop_fast_solver_time:                  0.
% 7.05/1.49  prop_unsat_core_time:                   0.001
% 7.05/1.49  
% 7.05/1.49  ------ QBF
% 7.05/1.49  
% 7.05/1.49  qbf_q_res:                              0
% 7.05/1.49  qbf_num_tautologies:                    0
% 7.05/1.49  qbf_prep_cycles:                        0
% 7.05/1.49  
% 7.05/1.49  ------ BMC1
% 7.05/1.49  
% 7.05/1.49  bmc1_current_bound:                     -1
% 7.05/1.49  bmc1_last_solved_bound:                 -1
% 7.05/1.49  bmc1_unsat_core_size:                   -1
% 7.05/1.49  bmc1_unsat_core_parents_size:           -1
% 7.05/1.49  bmc1_merge_next_fun:                    0
% 7.05/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.05/1.49  
% 7.05/1.49  ------ Instantiation
% 7.05/1.49  
% 7.05/1.49  inst_num_of_clauses:                    3334
% 7.05/1.49  inst_num_in_passive:                    38
% 7.05/1.49  inst_num_in_active:                     1737
% 7.05/1.49  inst_num_in_unprocessed:                1574
% 7.05/1.49  inst_num_of_loops:                      1780
% 7.05/1.49  inst_num_of_learning_restarts:          0
% 7.05/1.49  inst_num_moves_active_passive:          41
% 7.05/1.49  inst_lit_activity:                      0
% 7.05/1.49  inst_lit_activity_moves:                1
% 7.05/1.49  inst_num_tautologies:                   0
% 7.05/1.49  inst_num_prop_implied:                  0
% 7.05/1.49  inst_num_existing_simplified:           0
% 7.05/1.49  inst_num_eq_res_simplified:             0
% 7.05/1.49  inst_num_child_elim:                    0
% 7.05/1.49  inst_num_of_dismatching_blockings:      2616
% 7.05/1.49  inst_num_of_non_proper_insts:           3942
% 7.05/1.49  inst_num_of_duplicates:                 0
% 7.05/1.49  inst_inst_num_from_inst_to_res:         0
% 7.05/1.49  inst_dismatching_checking_time:         0.
% 7.05/1.49  
% 7.05/1.49  ------ Resolution
% 7.05/1.49  
% 7.05/1.49  res_num_of_clauses:                     0
% 7.05/1.49  res_num_in_passive:                     0
% 7.05/1.49  res_num_in_active:                      0
% 7.05/1.49  res_num_of_loops:                       177
% 7.05/1.49  res_forward_subset_subsumed:            238
% 7.05/1.49  res_backward_subset_subsumed:           30
% 7.05/1.49  res_forward_subsumed:                   0
% 7.05/1.49  res_backward_subsumed:                  0
% 7.05/1.49  res_forward_subsumption_resolution:     2
% 7.05/1.49  res_backward_subsumption_resolution:    0
% 7.05/1.49  res_clause_to_clause_subsumption:       3018
% 7.05/1.49  res_orphan_elimination:                 0
% 7.05/1.49  res_tautology_del:                      202
% 7.05/1.49  res_num_eq_res_simplified:              0
% 7.05/1.49  res_num_sel_changes:                    0
% 7.05/1.49  res_moves_from_active_to_pass:          0
% 7.05/1.49  
% 7.05/1.49  ------ Superposition
% 7.05/1.49  
% 7.05/1.49  sup_time_total:                         0.
% 7.05/1.49  sup_time_generating:                    0.
% 7.05/1.49  sup_time_sim_full:                      0.
% 7.05/1.49  sup_time_sim_immed:                     0.
% 7.05/1.49  
% 7.05/1.49  sup_num_of_clauses:                     1082
% 7.05/1.49  sup_num_in_active:                      351
% 7.05/1.49  sup_num_in_passive:                     731
% 7.05/1.49  sup_num_of_loops:                       355
% 7.05/1.49  sup_fw_superposition:                   902
% 7.05/1.49  sup_bw_superposition:                   684
% 7.05/1.49  sup_immediate_simplified:               409
% 7.05/1.49  sup_given_eliminated:                   0
% 7.05/1.49  comparisons_done:                       0
% 7.05/1.49  comparisons_avoided:                    14
% 7.05/1.49  
% 7.05/1.49  ------ Simplifications
% 7.05/1.49  
% 7.05/1.49  
% 7.05/1.49  sim_fw_subset_subsumed:                 59
% 7.05/1.49  sim_bw_subset_subsumed:                 2
% 7.05/1.49  sim_fw_subsumed:                        33
% 7.05/1.49  sim_bw_subsumed:                        0
% 7.05/1.49  sim_fw_subsumption_res:                 3
% 7.05/1.49  sim_bw_subsumption_res:                 0
% 7.05/1.49  sim_tautology_del:                      7
% 7.05/1.49  sim_eq_tautology_del:                   42
% 7.05/1.49  sim_eq_res_simp:                        0
% 7.05/1.49  sim_fw_demodulated:                     22
% 7.05/1.49  sim_bw_demodulated:                     45
% 7.05/1.49  sim_light_normalised:                   296
% 7.05/1.49  sim_joinable_taut:                      0
% 7.05/1.49  sim_joinable_simp:                      0
% 7.05/1.49  sim_ac_normalised:                      0
% 7.05/1.49  sim_smt_subsumption:                    0
% 7.05/1.49  
%------------------------------------------------------------------------------
