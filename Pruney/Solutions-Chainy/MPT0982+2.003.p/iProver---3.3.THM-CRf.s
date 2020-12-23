%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:37 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 7.71s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 831 expanded)
%              Number of clauses        :  118 ( 266 expanded)
%              Number of leaves         :   20 ( 200 expanded)
%              Depth                    :   22
%              Number of atoms          :  593 (5550 expanded)
%              Number of equality atoms :  266 (1853 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f42,f48,f47])).

fof(f80,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f49])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f77,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f78,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f84,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f49])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f14,axiom,(
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

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f86,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f49])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f43])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f87,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1185,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1193,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1584,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_1193])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1187,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1583,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_1193])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1198,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3270,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1583,c_1198])).

cnf(c_3432,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1584,c_3270])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_424,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_30])).

cnf(c_425,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_424])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_429,plain,
    ( ~ v1_relat_1(sK4)
    | k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_425,c_34])).

cnf(c_1180,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_429])).

cnf(c_1252,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1319,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1252])).

cnf(c_1652,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1180,c_34,c_32,c_425,c_1319])).

cnf(c_11,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1194,plain,
    ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2832,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1652,c_1194])).

cnf(c_41,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1320,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1319])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2854,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2855,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2854])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2865,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_2866,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2865])).

cnf(c_3103,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2832,c_41,c_43,c_1320,c_2855,c_2866])).

cnf(c_4207,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3432,c_3103])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1190,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1191,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3253,plain,
    ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1191])).

cnf(c_5723,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_3253])).

cnf(c_5861,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5723,c_41])).

cnf(c_5862,plain,
    ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5861])).

cnf(c_5869,plain,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_5862])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1188,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3344,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_1188])).

cnf(c_3437,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3344,c_41])).

cnf(c_3438,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_3437])).

cnf(c_3445,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1185,c_3438])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3583,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3445,c_38])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_3585,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3583,c_31])).

cnf(c_5874,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | v1_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5869,c_3583,c_3585])).

cnf(c_5883,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5874,c_38])).

cnf(c_1186,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1195,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3269,plain,
    ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_1198])).

cnf(c_8317,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1186,c_3269])).

cnf(c_8471,plain,
    ( v1_relat_1(X0) != iProver_top
    | k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8317,c_43,c_1320])).

cnf(c_8472,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8471])).

cnf(c_8478,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
    inference(superposition,[status(thm)],[c_1583,c_8472])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1192,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2001,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1187,c_1192])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_525,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_526,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_525])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_528,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_526,c_32,c_29])).

cnf(c_2003,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2001,c_528])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_396,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_30])).

cnf(c_397,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_399,plain,
    ( ~ v1_relat_1(sK4)
    | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_34])).

cnf(c_1182,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_1737,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1182,c_34,c_32,c_397,c_1319])).

cnf(c_2180,plain,
    ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(sK1) ),
    inference(demodulation,[status(thm)],[c_2003,c_1737])).

cnf(c_6,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1197,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5887,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5883,c_1197])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_1468,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1469,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_6300,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5887,c_40,c_43,c_1320,c_1469])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_375,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_376,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_380,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_15])).

cnf(c_381,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_380])).

cnf(c_1183,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_381])).

cnf(c_2456,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1187,c_1183])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1200,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2949,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2456,c_1200])).

cnf(c_6305,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_6300,c_2949])).

cnf(c_8486,plain,
    ( k9_relat_1(k2_funct_1(sK4),sK2) = k2_relat_1(k6_relat_1(sK1)) ),
    inference(light_normalisation,[status(thm)],[c_8478,c_2180,c_6305])).

cnf(c_7,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_8487,plain,
    ( k9_relat_1(k2_funct_1(sK4),sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_8486,c_7])).

cnf(c_18163,plain,
    ( r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4207,c_5883,c_8487])).

cnf(c_743,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1240,plain,
    ( k2_relset_1(sK0,sK1,sK3) != X0
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_2019,plain,
    ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1240])).

cnf(c_1999,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1185,c_1191])).

cnf(c_1281,plain,
    ( ~ r1_tarski(X0,sK1)
    | ~ r1_tarski(sK1,X0)
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1343,plain,
    ( ~ r1_tarski(k2_relat_1(X0),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(X0))
    | sK1 = k2_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_1730,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | ~ r1_tarski(sK1,k2_relat_1(sK3))
    | sK1 = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1343])).

cnf(c_1731,plain,
    ( sK1 = k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1730])).

cnf(c_1431,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | r1_tarski(k2_relat_1(X0),sK1) ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_1641,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k2_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_1431])).

cnf(c_1642,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1641])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_18163,c_2019,c_1999,c_1731,c_1642,c_28,c_40])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:52:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  % Running in FOF mode
% 7.71/1.51  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.71/1.51  
% 7.71/1.51  ------  iProver source info
% 7.71/1.51  
% 7.71/1.51  git: date: 2020-06-30 10:37:57 +0100
% 7.71/1.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.71/1.51  git: non_committed_changes: false
% 7.71/1.51  git: last_make_outside_of_git: false
% 7.71/1.51  
% 7.71/1.51  ------ 
% 7.71/1.51  
% 7.71/1.51  ------ Input Options
% 7.71/1.51  
% 7.71/1.51  --out_options                           all
% 7.71/1.51  --tptp_safe_out                         true
% 7.71/1.51  --problem_path                          ""
% 7.71/1.51  --include_path                          ""
% 7.71/1.51  --clausifier                            res/vclausify_rel
% 7.71/1.51  --clausifier_options                    ""
% 7.71/1.51  --stdin                                 false
% 7.71/1.51  --stats_out                             all
% 7.71/1.51  
% 7.71/1.51  ------ General Options
% 7.71/1.51  
% 7.71/1.51  --fof                                   false
% 7.71/1.51  --time_out_real                         305.
% 7.71/1.51  --time_out_virtual                      -1.
% 7.71/1.51  --symbol_type_check                     false
% 7.71/1.51  --clausify_out                          false
% 7.71/1.51  --sig_cnt_out                           false
% 7.71/1.51  --trig_cnt_out                          false
% 7.71/1.51  --trig_cnt_out_tolerance                1.
% 7.71/1.51  --trig_cnt_out_sk_spl                   false
% 7.71/1.51  --abstr_cl_out                          false
% 7.71/1.51  
% 7.71/1.51  ------ Global Options
% 7.71/1.51  
% 7.71/1.51  --schedule                              default
% 7.71/1.51  --add_important_lit                     false
% 7.71/1.51  --prop_solver_per_cl                    1000
% 7.71/1.51  --min_unsat_core                        false
% 7.71/1.51  --soft_assumptions                      false
% 7.71/1.51  --soft_lemma_size                       3
% 7.71/1.51  --prop_impl_unit_size                   0
% 7.71/1.51  --prop_impl_unit                        []
% 7.71/1.51  --share_sel_clauses                     true
% 7.71/1.51  --reset_solvers                         false
% 7.71/1.51  --bc_imp_inh                            [conj_cone]
% 7.71/1.51  --conj_cone_tolerance                   3.
% 7.71/1.51  --extra_neg_conj                        none
% 7.71/1.51  --large_theory_mode                     true
% 7.71/1.51  --prolific_symb_bound                   200
% 7.71/1.51  --lt_threshold                          2000
% 7.71/1.51  --clause_weak_htbl                      true
% 7.71/1.51  --gc_record_bc_elim                     false
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing Options
% 7.71/1.51  
% 7.71/1.51  --preprocessing_flag                    true
% 7.71/1.51  --time_out_prep_mult                    0.1
% 7.71/1.51  --splitting_mode                        input
% 7.71/1.51  --splitting_grd                         true
% 7.71/1.51  --splitting_cvd                         false
% 7.71/1.51  --splitting_cvd_svl                     false
% 7.71/1.51  --splitting_nvd                         32
% 7.71/1.51  --sub_typing                            true
% 7.71/1.51  --prep_gs_sim                           true
% 7.71/1.51  --prep_unflatten                        true
% 7.71/1.51  --prep_res_sim                          true
% 7.71/1.51  --prep_upred                            true
% 7.71/1.51  --prep_sem_filter                       exhaustive
% 7.71/1.51  --prep_sem_filter_out                   false
% 7.71/1.51  --pred_elim                             true
% 7.71/1.51  --res_sim_input                         true
% 7.71/1.51  --eq_ax_congr_red                       true
% 7.71/1.51  --pure_diseq_elim                       true
% 7.71/1.51  --brand_transform                       false
% 7.71/1.51  --non_eq_to_eq                          false
% 7.71/1.51  --prep_def_merge                        true
% 7.71/1.51  --prep_def_merge_prop_impl              false
% 7.71/1.51  --prep_def_merge_mbd                    true
% 7.71/1.51  --prep_def_merge_tr_red                 false
% 7.71/1.51  --prep_def_merge_tr_cl                  false
% 7.71/1.51  --smt_preprocessing                     true
% 7.71/1.51  --smt_ac_axioms                         fast
% 7.71/1.51  --preprocessed_out                      false
% 7.71/1.51  --preprocessed_stats                    false
% 7.71/1.51  
% 7.71/1.51  ------ Abstraction refinement Options
% 7.71/1.51  
% 7.71/1.51  --abstr_ref                             []
% 7.71/1.51  --abstr_ref_prep                        false
% 7.71/1.51  --abstr_ref_until_sat                   false
% 7.71/1.51  --abstr_ref_sig_restrict                funpre
% 7.71/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.51  --abstr_ref_under                       []
% 7.71/1.51  
% 7.71/1.51  ------ SAT Options
% 7.71/1.51  
% 7.71/1.51  --sat_mode                              false
% 7.71/1.51  --sat_fm_restart_options                ""
% 7.71/1.51  --sat_gr_def                            false
% 7.71/1.51  --sat_epr_types                         true
% 7.71/1.51  --sat_non_cyclic_types                  false
% 7.71/1.51  --sat_finite_models                     false
% 7.71/1.51  --sat_fm_lemmas                         false
% 7.71/1.51  --sat_fm_prep                           false
% 7.71/1.51  --sat_fm_uc_incr                        true
% 7.71/1.51  --sat_out_model                         small
% 7.71/1.51  --sat_out_clauses                       false
% 7.71/1.51  
% 7.71/1.51  ------ QBF Options
% 7.71/1.51  
% 7.71/1.51  --qbf_mode                              false
% 7.71/1.51  --qbf_elim_univ                         false
% 7.71/1.51  --qbf_dom_inst                          none
% 7.71/1.51  --qbf_dom_pre_inst                      false
% 7.71/1.51  --qbf_sk_in                             false
% 7.71/1.51  --qbf_pred_elim                         true
% 7.71/1.51  --qbf_split                             512
% 7.71/1.51  
% 7.71/1.51  ------ BMC1 Options
% 7.71/1.51  
% 7.71/1.51  --bmc1_incremental                      false
% 7.71/1.51  --bmc1_axioms                           reachable_all
% 7.71/1.51  --bmc1_min_bound                        0
% 7.71/1.51  --bmc1_max_bound                        -1
% 7.71/1.51  --bmc1_max_bound_default                -1
% 7.71/1.51  --bmc1_symbol_reachability              true
% 7.71/1.51  --bmc1_property_lemmas                  false
% 7.71/1.51  --bmc1_k_induction                      false
% 7.71/1.51  --bmc1_non_equiv_states                 false
% 7.71/1.51  --bmc1_deadlock                         false
% 7.71/1.51  --bmc1_ucm                              false
% 7.71/1.51  --bmc1_add_unsat_core                   none
% 7.71/1.51  --bmc1_unsat_core_children              false
% 7.71/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.51  --bmc1_out_stat                         full
% 7.71/1.51  --bmc1_ground_init                      false
% 7.71/1.51  --bmc1_pre_inst_next_state              false
% 7.71/1.51  --bmc1_pre_inst_state                   false
% 7.71/1.51  --bmc1_pre_inst_reach_state             false
% 7.71/1.51  --bmc1_out_unsat_core                   false
% 7.71/1.51  --bmc1_aig_witness_out                  false
% 7.71/1.51  --bmc1_verbose                          false
% 7.71/1.51  --bmc1_dump_clauses_tptp                false
% 7.71/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.51  --bmc1_dump_file                        -
% 7.71/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.51  --bmc1_ucm_extend_mode                  1
% 7.71/1.51  --bmc1_ucm_init_mode                    2
% 7.71/1.51  --bmc1_ucm_cone_mode                    none
% 7.71/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.51  --bmc1_ucm_relax_model                  4
% 7.71/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.51  --bmc1_ucm_layered_model                none
% 7.71/1.51  --bmc1_ucm_max_lemma_size               10
% 7.71/1.51  
% 7.71/1.51  ------ AIG Options
% 7.71/1.51  
% 7.71/1.51  --aig_mode                              false
% 7.71/1.51  
% 7.71/1.51  ------ Instantiation Options
% 7.71/1.51  
% 7.71/1.51  --instantiation_flag                    true
% 7.71/1.51  --inst_sos_flag                         true
% 7.71/1.51  --inst_sos_phase                        true
% 7.71/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel_side                     num_symb
% 7.71/1.51  --inst_solver_per_active                1400
% 7.71/1.51  --inst_solver_calls_frac                1.
% 7.71/1.51  --inst_passive_queue_type               priority_queues
% 7.71/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.51  --inst_passive_queues_freq              [25;2]
% 7.71/1.51  --inst_dismatching                      true
% 7.71/1.51  --inst_eager_unprocessed_to_passive     true
% 7.71/1.51  --inst_prop_sim_given                   true
% 7.71/1.51  --inst_prop_sim_new                     false
% 7.71/1.51  --inst_subs_new                         false
% 7.71/1.51  --inst_eq_res_simp                      false
% 7.71/1.51  --inst_subs_given                       false
% 7.71/1.51  --inst_orphan_elimination               true
% 7.71/1.51  --inst_learning_loop_flag               true
% 7.71/1.51  --inst_learning_start                   3000
% 7.71/1.51  --inst_learning_factor                  2
% 7.71/1.51  --inst_start_prop_sim_after_learn       3
% 7.71/1.51  --inst_sel_renew                        solver
% 7.71/1.51  --inst_lit_activity_flag                true
% 7.71/1.51  --inst_restr_to_given                   false
% 7.71/1.51  --inst_activity_threshold               500
% 7.71/1.51  --inst_out_proof                        true
% 7.71/1.51  
% 7.71/1.51  ------ Resolution Options
% 7.71/1.51  
% 7.71/1.51  --resolution_flag                       true
% 7.71/1.51  --res_lit_sel                           adaptive
% 7.71/1.51  --res_lit_sel_side                      none
% 7.71/1.51  --res_ordering                          kbo
% 7.71/1.51  --res_to_prop_solver                    active
% 7.71/1.51  --res_prop_simpl_new                    false
% 7.71/1.51  --res_prop_simpl_given                  true
% 7.71/1.51  --res_passive_queue_type                priority_queues
% 7.71/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.51  --res_passive_queues_freq               [15;5]
% 7.71/1.51  --res_forward_subs                      full
% 7.71/1.51  --res_backward_subs                     full
% 7.71/1.51  --res_forward_subs_resolution           true
% 7.71/1.51  --res_backward_subs_resolution          true
% 7.71/1.51  --res_orphan_elimination                true
% 7.71/1.51  --res_time_limit                        2.
% 7.71/1.51  --res_out_proof                         true
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Options
% 7.71/1.51  
% 7.71/1.51  --superposition_flag                    true
% 7.71/1.51  --sup_passive_queue_type                priority_queues
% 7.71/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.71/1.51  --demod_completeness_check              fast
% 7.71/1.51  --demod_use_ground                      true
% 7.71/1.51  --sup_to_prop_solver                    passive
% 7.71/1.51  --sup_prop_simpl_new                    true
% 7.71/1.51  --sup_prop_simpl_given                  true
% 7.71/1.51  --sup_fun_splitting                     true
% 7.71/1.51  --sup_smt_interval                      50000
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Simplification Setup
% 7.71/1.51  
% 7.71/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.71/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.71/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.71/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.71/1.51  --sup_immed_triv                        [TrivRules]
% 7.71/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_bw_main                     []
% 7.71/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.71/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_input_bw                          []
% 7.71/1.51  
% 7.71/1.51  ------ Combination Options
% 7.71/1.51  
% 7.71/1.51  --comb_res_mult                         3
% 7.71/1.51  --comb_sup_mult                         2
% 7.71/1.51  --comb_inst_mult                        10
% 7.71/1.51  
% 7.71/1.51  ------ Debug Options
% 7.71/1.51  
% 7.71/1.51  --dbg_backtrace                         false
% 7.71/1.51  --dbg_dump_prop_clauses                 false
% 7.71/1.51  --dbg_dump_prop_clauses_file            -
% 7.71/1.51  --dbg_out_stat                          false
% 7.71/1.51  ------ Parsing...
% 7.71/1.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.71/1.51  ------ Proving...
% 7.71/1.51  ------ Problem Properties 
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  clauses                                 32
% 7.71/1.51  conjectures                             7
% 7.71/1.51  EPR                                     5
% 7.71/1.51  Horn                                    29
% 7.71/1.51  unary                                   11
% 7.71/1.51  binary                                  8
% 7.71/1.51  lits                                    74
% 7.71/1.51  lits eq                                 26
% 7.71/1.51  fd_pure                                 0
% 7.71/1.51  fd_pseudo                               0
% 7.71/1.51  fd_cond                                 0
% 7.71/1.51  fd_pseudo_cond                          1
% 7.71/1.51  AC symbols                              0
% 7.71/1.51  
% 7.71/1.51  ------ Schedule dynamic 5 is on 
% 7.71/1.51  
% 7.71/1.51  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  ------ 
% 7.71/1.51  Current options:
% 7.71/1.51  ------ 
% 7.71/1.51  
% 7.71/1.51  ------ Input Options
% 7.71/1.51  
% 7.71/1.51  --out_options                           all
% 7.71/1.51  --tptp_safe_out                         true
% 7.71/1.51  --problem_path                          ""
% 7.71/1.51  --include_path                          ""
% 7.71/1.51  --clausifier                            res/vclausify_rel
% 7.71/1.51  --clausifier_options                    ""
% 7.71/1.51  --stdin                                 false
% 7.71/1.51  --stats_out                             all
% 7.71/1.51  
% 7.71/1.51  ------ General Options
% 7.71/1.51  
% 7.71/1.51  --fof                                   false
% 7.71/1.51  --time_out_real                         305.
% 7.71/1.51  --time_out_virtual                      -1.
% 7.71/1.51  --symbol_type_check                     false
% 7.71/1.51  --clausify_out                          false
% 7.71/1.51  --sig_cnt_out                           false
% 7.71/1.51  --trig_cnt_out                          false
% 7.71/1.51  --trig_cnt_out_tolerance                1.
% 7.71/1.51  --trig_cnt_out_sk_spl                   false
% 7.71/1.51  --abstr_cl_out                          false
% 7.71/1.51  
% 7.71/1.51  ------ Global Options
% 7.71/1.51  
% 7.71/1.51  --schedule                              default
% 7.71/1.51  --add_important_lit                     false
% 7.71/1.51  --prop_solver_per_cl                    1000
% 7.71/1.51  --min_unsat_core                        false
% 7.71/1.51  --soft_assumptions                      false
% 7.71/1.51  --soft_lemma_size                       3
% 7.71/1.51  --prop_impl_unit_size                   0
% 7.71/1.51  --prop_impl_unit                        []
% 7.71/1.51  --share_sel_clauses                     true
% 7.71/1.51  --reset_solvers                         false
% 7.71/1.51  --bc_imp_inh                            [conj_cone]
% 7.71/1.51  --conj_cone_tolerance                   3.
% 7.71/1.51  --extra_neg_conj                        none
% 7.71/1.51  --large_theory_mode                     true
% 7.71/1.51  --prolific_symb_bound                   200
% 7.71/1.51  --lt_threshold                          2000
% 7.71/1.51  --clause_weak_htbl                      true
% 7.71/1.51  --gc_record_bc_elim                     false
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing Options
% 7.71/1.51  
% 7.71/1.51  --preprocessing_flag                    true
% 7.71/1.51  --time_out_prep_mult                    0.1
% 7.71/1.51  --splitting_mode                        input
% 7.71/1.51  --splitting_grd                         true
% 7.71/1.51  --splitting_cvd                         false
% 7.71/1.51  --splitting_cvd_svl                     false
% 7.71/1.51  --splitting_nvd                         32
% 7.71/1.51  --sub_typing                            true
% 7.71/1.51  --prep_gs_sim                           true
% 7.71/1.51  --prep_unflatten                        true
% 7.71/1.51  --prep_res_sim                          true
% 7.71/1.51  --prep_upred                            true
% 7.71/1.51  --prep_sem_filter                       exhaustive
% 7.71/1.51  --prep_sem_filter_out                   false
% 7.71/1.51  --pred_elim                             true
% 7.71/1.51  --res_sim_input                         true
% 7.71/1.51  --eq_ax_congr_red                       true
% 7.71/1.51  --pure_diseq_elim                       true
% 7.71/1.51  --brand_transform                       false
% 7.71/1.51  --non_eq_to_eq                          false
% 7.71/1.51  --prep_def_merge                        true
% 7.71/1.51  --prep_def_merge_prop_impl              false
% 7.71/1.51  --prep_def_merge_mbd                    true
% 7.71/1.51  --prep_def_merge_tr_red                 false
% 7.71/1.51  --prep_def_merge_tr_cl                  false
% 7.71/1.51  --smt_preprocessing                     true
% 7.71/1.51  --smt_ac_axioms                         fast
% 7.71/1.51  --preprocessed_out                      false
% 7.71/1.51  --preprocessed_stats                    false
% 7.71/1.51  
% 7.71/1.51  ------ Abstraction refinement Options
% 7.71/1.51  
% 7.71/1.51  --abstr_ref                             []
% 7.71/1.51  --abstr_ref_prep                        false
% 7.71/1.51  --abstr_ref_until_sat                   false
% 7.71/1.51  --abstr_ref_sig_restrict                funpre
% 7.71/1.51  --abstr_ref_af_restrict_to_split_sk     false
% 7.71/1.51  --abstr_ref_under                       []
% 7.71/1.51  
% 7.71/1.51  ------ SAT Options
% 7.71/1.51  
% 7.71/1.51  --sat_mode                              false
% 7.71/1.51  --sat_fm_restart_options                ""
% 7.71/1.51  --sat_gr_def                            false
% 7.71/1.51  --sat_epr_types                         true
% 7.71/1.51  --sat_non_cyclic_types                  false
% 7.71/1.51  --sat_finite_models                     false
% 7.71/1.51  --sat_fm_lemmas                         false
% 7.71/1.51  --sat_fm_prep                           false
% 7.71/1.51  --sat_fm_uc_incr                        true
% 7.71/1.51  --sat_out_model                         small
% 7.71/1.51  --sat_out_clauses                       false
% 7.71/1.51  
% 7.71/1.51  ------ QBF Options
% 7.71/1.51  
% 7.71/1.51  --qbf_mode                              false
% 7.71/1.51  --qbf_elim_univ                         false
% 7.71/1.51  --qbf_dom_inst                          none
% 7.71/1.51  --qbf_dom_pre_inst                      false
% 7.71/1.51  --qbf_sk_in                             false
% 7.71/1.51  --qbf_pred_elim                         true
% 7.71/1.51  --qbf_split                             512
% 7.71/1.51  
% 7.71/1.51  ------ BMC1 Options
% 7.71/1.51  
% 7.71/1.51  --bmc1_incremental                      false
% 7.71/1.51  --bmc1_axioms                           reachable_all
% 7.71/1.51  --bmc1_min_bound                        0
% 7.71/1.51  --bmc1_max_bound                        -1
% 7.71/1.51  --bmc1_max_bound_default                -1
% 7.71/1.51  --bmc1_symbol_reachability              true
% 7.71/1.51  --bmc1_property_lemmas                  false
% 7.71/1.51  --bmc1_k_induction                      false
% 7.71/1.51  --bmc1_non_equiv_states                 false
% 7.71/1.51  --bmc1_deadlock                         false
% 7.71/1.51  --bmc1_ucm                              false
% 7.71/1.51  --bmc1_add_unsat_core                   none
% 7.71/1.51  --bmc1_unsat_core_children              false
% 7.71/1.51  --bmc1_unsat_core_extrapolate_axioms    false
% 7.71/1.51  --bmc1_out_stat                         full
% 7.71/1.51  --bmc1_ground_init                      false
% 7.71/1.51  --bmc1_pre_inst_next_state              false
% 7.71/1.51  --bmc1_pre_inst_state                   false
% 7.71/1.51  --bmc1_pre_inst_reach_state             false
% 7.71/1.51  --bmc1_out_unsat_core                   false
% 7.71/1.51  --bmc1_aig_witness_out                  false
% 7.71/1.51  --bmc1_verbose                          false
% 7.71/1.51  --bmc1_dump_clauses_tptp                false
% 7.71/1.51  --bmc1_dump_unsat_core_tptp             false
% 7.71/1.51  --bmc1_dump_file                        -
% 7.71/1.51  --bmc1_ucm_expand_uc_limit              128
% 7.71/1.51  --bmc1_ucm_n_expand_iterations          6
% 7.71/1.51  --bmc1_ucm_extend_mode                  1
% 7.71/1.51  --bmc1_ucm_init_mode                    2
% 7.71/1.51  --bmc1_ucm_cone_mode                    none
% 7.71/1.51  --bmc1_ucm_reduced_relation_type        0
% 7.71/1.51  --bmc1_ucm_relax_model                  4
% 7.71/1.51  --bmc1_ucm_full_tr_after_sat            true
% 7.71/1.51  --bmc1_ucm_expand_neg_assumptions       false
% 7.71/1.51  --bmc1_ucm_layered_model                none
% 7.71/1.51  --bmc1_ucm_max_lemma_size               10
% 7.71/1.51  
% 7.71/1.51  ------ AIG Options
% 7.71/1.51  
% 7.71/1.51  --aig_mode                              false
% 7.71/1.51  
% 7.71/1.51  ------ Instantiation Options
% 7.71/1.51  
% 7.71/1.51  --instantiation_flag                    true
% 7.71/1.51  --inst_sos_flag                         true
% 7.71/1.51  --inst_sos_phase                        true
% 7.71/1.51  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.71/1.51  --inst_lit_sel_side                     none
% 7.71/1.51  --inst_solver_per_active                1400
% 7.71/1.51  --inst_solver_calls_frac                1.
% 7.71/1.51  --inst_passive_queue_type               priority_queues
% 7.71/1.51  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.71/1.51  --inst_passive_queues_freq              [25;2]
% 7.71/1.51  --inst_dismatching                      true
% 7.71/1.51  --inst_eager_unprocessed_to_passive     true
% 7.71/1.51  --inst_prop_sim_given                   true
% 7.71/1.51  --inst_prop_sim_new                     false
% 7.71/1.51  --inst_subs_new                         false
% 7.71/1.51  --inst_eq_res_simp                      false
% 7.71/1.51  --inst_subs_given                       false
% 7.71/1.51  --inst_orphan_elimination               true
% 7.71/1.51  --inst_learning_loop_flag               true
% 7.71/1.51  --inst_learning_start                   3000
% 7.71/1.51  --inst_learning_factor                  2
% 7.71/1.51  --inst_start_prop_sim_after_learn       3
% 7.71/1.51  --inst_sel_renew                        solver
% 7.71/1.51  --inst_lit_activity_flag                true
% 7.71/1.51  --inst_restr_to_given                   false
% 7.71/1.51  --inst_activity_threshold               500
% 7.71/1.51  --inst_out_proof                        true
% 7.71/1.51  
% 7.71/1.51  ------ Resolution Options
% 7.71/1.51  
% 7.71/1.51  --resolution_flag                       false
% 7.71/1.51  --res_lit_sel                           adaptive
% 7.71/1.51  --res_lit_sel_side                      none
% 7.71/1.51  --res_ordering                          kbo
% 7.71/1.51  --res_to_prop_solver                    active
% 7.71/1.51  --res_prop_simpl_new                    false
% 7.71/1.51  --res_prop_simpl_given                  true
% 7.71/1.51  --res_passive_queue_type                priority_queues
% 7.71/1.51  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.71/1.51  --res_passive_queues_freq               [15;5]
% 7.71/1.51  --res_forward_subs                      full
% 7.71/1.51  --res_backward_subs                     full
% 7.71/1.51  --res_forward_subs_resolution           true
% 7.71/1.51  --res_backward_subs_resolution          true
% 7.71/1.51  --res_orphan_elimination                true
% 7.71/1.51  --res_time_limit                        2.
% 7.71/1.51  --res_out_proof                         true
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Options
% 7.71/1.51  
% 7.71/1.51  --superposition_flag                    true
% 7.71/1.51  --sup_passive_queue_type                priority_queues
% 7.71/1.51  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.71/1.51  --sup_passive_queues_freq               [8;1;4]
% 7.71/1.51  --demod_completeness_check              fast
% 7.71/1.51  --demod_use_ground                      true
% 7.71/1.51  --sup_to_prop_solver                    passive
% 7.71/1.51  --sup_prop_simpl_new                    true
% 7.71/1.51  --sup_prop_simpl_given                  true
% 7.71/1.51  --sup_fun_splitting                     true
% 7.71/1.51  --sup_smt_interval                      50000
% 7.71/1.51  
% 7.71/1.51  ------ Superposition Simplification Setup
% 7.71/1.51  
% 7.71/1.51  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.71/1.51  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.71/1.51  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.71/1.51  --sup_full_triv                         [TrivRules;PropSubs]
% 7.71/1.51  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.71/1.51  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.71/1.51  --sup_immed_triv                        [TrivRules]
% 7.71/1.51  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_immed_bw_main                     []
% 7.71/1.51  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.71/1.51  --sup_input_triv                        [Unflattening;TrivRules]
% 7.71/1.51  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.71/1.51  --sup_input_bw                          []
% 7.71/1.51  
% 7.71/1.51  ------ Combination Options
% 7.71/1.51  
% 7.71/1.51  --comb_res_mult                         3
% 7.71/1.51  --comb_sup_mult                         2
% 7.71/1.51  --comb_inst_mult                        10
% 7.71/1.51  
% 7.71/1.51  ------ Debug Options
% 7.71/1.51  
% 7.71/1.51  --dbg_backtrace                         false
% 7.71/1.51  --dbg_dump_prop_clauses                 false
% 7.71/1.51  --dbg_dump_prop_clauses_file            -
% 7.71/1.51  --dbg_out_stat                          false
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  ------ Proving...
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  % SZS status Theorem for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  % SZS output start CNFRefutation for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  fof(f17,conjecture,(
% 7.71/1.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f18,negated_conjecture,(
% 7.71/1.51    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 7.71/1.51    inference(negated_conjecture,[],[f17])).
% 7.71/1.51  
% 7.71/1.51  fof(f41,plain,(
% 7.71/1.51    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.71/1.51    inference(ennf_transformation,[],[f18])).
% 7.71/1.51  
% 7.71/1.51  fof(f42,plain,(
% 7.71/1.51    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.71/1.51    inference(flattening,[],[f41])).
% 7.71/1.51  
% 7.71/1.51  fof(f48,plain,(
% 7.71/1.51    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 7.71/1.51    introduced(choice_axiom,[])).
% 7.71/1.51  
% 7.71/1.51  fof(f47,plain,(
% 7.71/1.51    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 7.71/1.51    introduced(choice_axiom,[])).
% 7.71/1.51  
% 7.71/1.51  fof(f49,plain,(
% 7.71/1.51    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 7.71/1.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f42,f48,f47])).
% 7.71/1.51  
% 7.71/1.51  fof(f80,plain,(
% 7.71/1.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.71/1.51    inference(cnf_transformation,[],[f49])).
% 7.71/1.51  
% 7.71/1.51  fof(f10,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f31,plain,(
% 7.71/1.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.51    inference(ennf_transformation,[],[f10])).
% 7.71/1.51  
% 7.71/1.51  fof(f65,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f31])).
% 7.71/1.51  
% 7.71/1.51  fof(f83,plain,(
% 7.71/1.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 7.71/1.51    inference(cnf_transformation,[],[f49])).
% 7.71/1.51  
% 7.71/1.51  fof(f3,axiom,(
% 7.71/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f21,plain,(
% 7.71/1.51    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.71/1.51    inference(ennf_transformation,[],[f3])).
% 7.71/1.51  
% 7.71/1.51  fof(f55,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f21])).
% 7.71/1.51  
% 7.71/1.51  fof(f8,axiom,(
% 7.71/1.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f27,plain,(
% 7.71/1.51    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.71/1.51    inference(ennf_transformation,[],[f8])).
% 7.71/1.51  
% 7.71/1.51  fof(f28,plain,(
% 7.71/1.51    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.71/1.51    inference(flattening,[],[f27])).
% 7.71/1.51  
% 7.71/1.51  fof(f62,plain,(
% 7.71/1.51    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f28])).
% 7.71/1.51  
% 7.71/1.51  fof(f85,plain,(
% 7.71/1.51    v2_funct_1(sK4)),
% 7.71/1.51    inference(cnf_transformation,[],[f49])).
% 7.71/1.51  
% 7.71/1.51  fof(f81,plain,(
% 7.71/1.51    v1_funct_1(sK4)),
% 7.71/1.51    inference(cnf_transformation,[],[f49])).
% 7.71/1.51  
% 7.71/1.51  fof(f7,axiom,(
% 7.71/1.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f25,plain,(
% 7.71/1.51    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 7.71/1.51    inference(ennf_transformation,[],[f7])).
% 7.71/1.51  
% 7.71/1.51  fof(f26,plain,(
% 7.71/1.51    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 7.71/1.51    inference(flattening,[],[f25])).
% 7.71/1.51  
% 7.71/1.51  fof(f61,plain,(
% 7.71/1.51    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,k10_relat_1(X1,X0)),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f26])).
% 7.71/1.51  
% 7.71/1.51  fof(f6,axiom,(
% 7.71/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f23,plain,(
% 7.71/1.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.71/1.51    inference(ennf_transformation,[],[f6])).
% 7.71/1.51  
% 7.71/1.51  fof(f24,plain,(
% 7.71/1.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.71/1.51    inference(flattening,[],[f23])).
% 7.71/1.51  
% 7.71/1.51  fof(f60,plain,(
% 7.71/1.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f24])).
% 7.71/1.51  
% 7.71/1.51  fof(f59,plain,(
% 7.71/1.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f24])).
% 7.71/1.51  
% 7.71/1.51  fof(f15,axiom,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f37,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.71/1.51    inference(ennf_transformation,[],[f15])).
% 7.71/1.51  
% 7.71/1.51  fof(f38,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.71/1.51    inference(flattening,[],[f37])).
% 7.71/1.51  
% 7.71/1.51  fof(f76,plain,(
% 7.71/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f38])).
% 7.71/1.51  
% 7.71/1.51  fof(f13,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f34,plain,(
% 7.71/1.51    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.51    inference(ennf_transformation,[],[f13])).
% 7.71/1.51  
% 7.71/1.51  fof(f68,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f34])).
% 7.71/1.51  
% 7.71/1.51  fof(f16,axiom,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f39,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.71/1.51    inference(ennf_transformation,[],[f16])).
% 7.71/1.51  
% 7.71/1.51  fof(f40,plain,(
% 7.71/1.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.71/1.51    inference(flattening,[],[f39])).
% 7.71/1.51  
% 7.71/1.51  fof(f77,plain,(
% 7.71/1.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f40])).
% 7.71/1.51  
% 7.71/1.51  fof(f78,plain,(
% 7.71/1.51    v1_funct_1(sK3)),
% 7.71/1.51    inference(cnf_transformation,[],[f49])).
% 7.71/1.51  
% 7.71/1.51  fof(f84,plain,(
% 7.71/1.51    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 7.71/1.51    inference(cnf_transformation,[],[f49])).
% 7.71/1.51  
% 7.71/1.51  fof(f12,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f33,plain,(
% 7.71/1.51    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.51    inference(ennf_transformation,[],[f12])).
% 7.71/1.51  
% 7.71/1.51  fof(f67,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f33])).
% 7.71/1.51  
% 7.71/1.51  fof(f14,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f35,plain,(
% 7.71/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.51    inference(ennf_transformation,[],[f14])).
% 7.71/1.51  
% 7.71/1.51  fof(f36,plain,(
% 7.71/1.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.51    inference(flattening,[],[f35])).
% 7.71/1.51  
% 7.71/1.51  fof(f46,plain,(
% 7.71/1.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.51    inference(nnf_transformation,[],[f36])).
% 7.71/1.51  
% 7.71/1.51  fof(f69,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f46])).
% 7.71/1.51  
% 7.71/1.51  fof(f82,plain,(
% 7.71/1.51    v1_funct_2(sK4,sK1,sK2)),
% 7.71/1.51    inference(cnf_transformation,[],[f49])).
% 7.71/1.51  
% 7.71/1.51  fof(f86,plain,(
% 7.71/1.51    k1_xboole_0 != sK2),
% 7.71/1.51    inference(cnf_transformation,[],[f49])).
% 7.71/1.51  
% 7.71/1.51  fof(f9,axiom,(
% 7.71/1.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f29,plain,(
% 7.71/1.51    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.71/1.51    inference(ennf_transformation,[],[f9])).
% 7.71/1.51  
% 7.71/1.51  fof(f30,plain,(
% 7.71/1.51    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.71/1.51    inference(flattening,[],[f29])).
% 7.71/1.51  
% 7.71/1.51  fof(f63,plain,(
% 7.71/1.51    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f30])).
% 7.71/1.51  
% 7.71/1.51  fof(f4,axiom,(
% 7.71/1.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f22,plain,(
% 7.71/1.51    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.71/1.51    inference(ennf_transformation,[],[f4])).
% 7.71/1.51  
% 7.71/1.51  fof(f56,plain,(
% 7.71/1.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f22])).
% 7.71/1.51  
% 7.71/1.51  fof(f2,axiom,(
% 7.71/1.51    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f20,plain,(
% 7.71/1.51    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.71/1.51    inference(ennf_transformation,[],[f2])).
% 7.71/1.51  
% 7.71/1.51  fof(f45,plain,(
% 7.71/1.51    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 7.71/1.51    inference(nnf_transformation,[],[f20])).
% 7.71/1.51  
% 7.71/1.51  fof(f53,plain,(
% 7.71/1.51    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f45])).
% 7.71/1.51  
% 7.71/1.51  fof(f11,axiom,(
% 7.71/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f19,plain,(
% 7.71/1.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 7.71/1.51    inference(pure_predicate_removal,[],[f11])).
% 7.71/1.51  
% 7.71/1.51  fof(f32,plain,(
% 7.71/1.51    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.71/1.51    inference(ennf_transformation,[],[f19])).
% 7.71/1.51  
% 7.71/1.51  fof(f66,plain,(
% 7.71/1.51    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.71/1.51    inference(cnf_transformation,[],[f32])).
% 7.71/1.51  
% 7.71/1.51  fof(f1,axiom,(
% 7.71/1.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f43,plain,(
% 7.71/1.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.71/1.51    inference(nnf_transformation,[],[f1])).
% 7.71/1.51  
% 7.71/1.51  fof(f44,plain,(
% 7.71/1.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.71/1.51    inference(flattening,[],[f43])).
% 7.71/1.51  
% 7.71/1.51  fof(f52,plain,(
% 7.71/1.51    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 7.71/1.51    inference(cnf_transformation,[],[f44])).
% 7.71/1.51  
% 7.71/1.51  fof(f5,axiom,(
% 7.71/1.51    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.71/1.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 7.71/1.51  
% 7.71/1.51  fof(f58,plain,(
% 7.71/1.51    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.71/1.51    inference(cnf_transformation,[],[f5])).
% 7.71/1.51  
% 7.71/1.51  fof(f87,plain,(
% 7.71/1.51    k2_relset_1(sK0,sK1,sK3) != sK1),
% 7.71/1.51    inference(cnf_transformation,[],[f49])).
% 7.71/1.51  
% 7.71/1.51  cnf(c_35,negated_conjecture,
% 7.71/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.71/1.51      inference(cnf_transformation,[],[f80]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1185,plain,
% 7.71/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_15,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | v1_relat_1(X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f65]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1193,plain,
% 7.71/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.71/1.51      | v1_relat_1(X0) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1584,plain,
% 7.71/1.51      ( v1_relat_1(sK3) = iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1185,c_1193]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_32,negated_conjecture,
% 7.71/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 7.71/1.51      inference(cnf_transformation,[],[f83]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1187,plain,
% 7.71/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1583,plain,
% 7.71/1.51      ( v1_relat_1(sK4) = iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1187,c_1193]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5,plain,
% 7.71/1.51      ( ~ v1_relat_1(X0)
% 7.71/1.51      | ~ v1_relat_1(X1)
% 7.71/1.51      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 7.71/1.51      inference(cnf_transformation,[],[f55]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1198,plain,
% 7.71/1.51      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 7.71/1.51      | v1_relat_1(X0) != iProver_top
% 7.71/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3270,plain,
% 7.71/1.51      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 7.71/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1583,c_1198]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3432,plain,
% 7.71/1.51      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1584,c_3270]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_12,plain,
% 7.71/1.51      ( ~ v2_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_relat_1(X0)
% 7.71/1.51      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 7.71/1.51      inference(cnf_transformation,[],[f62]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_30,negated_conjecture,
% 7.71/1.51      ( v2_funct_1(sK4) ),
% 7.71/1.51      inference(cnf_transformation,[],[f85]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_424,plain,
% 7.71/1.51      ( ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_relat_1(X0)
% 7.71/1.51      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
% 7.71/1.51      | sK4 != X0 ),
% 7.71/1.51      inference(resolution_lifted,[status(thm)],[c_12,c_30]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_425,plain,
% 7.71/1.51      ( ~ v1_funct_1(sK4)
% 7.71/1.51      | ~ v1_relat_1(sK4)
% 7.71/1.51      | k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
% 7.71/1.51      inference(unflattening,[status(thm)],[c_424]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_34,negated_conjecture,
% 7.71/1.51      ( v1_funct_1(sK4) ),
% 7.71/1.51      inference(cnf_transformation,[],[f81]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_429,plain,
% 7.71/1.51      ( ~ v1_relat_1(sK4)
% 7.71/1.51      | k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_425,c_34]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1180,plain,
% 7.71/1.51      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
% 7.71/1.51      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_429]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1252,plain,
% 7.71/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.71/1.51      | v1_relat_1(sK4) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1319,plain,
% 7.71/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.71/1.51      | v1_relat_1(sK4) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_1252]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1652,plain,
% 7.71/1.51      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_1180,c_34,c_32,c_425,c_1319]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_11,plain,
% 7.71/1.51      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1)
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_relat_1(X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f61]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1194,plain,
% 7.71/1.51      ( r1_tarski(k9_relat_1(X0,k10_relat_1(X0,X1)),X1) = iProver_top
% 7.71/1.51      | v1_funct_1(X0) != iProver_top
% 7.71/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2832,plain,
% 7.71/1.51      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top
% 7.71/1.51      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 7.71/1.51      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1652,c_1194]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_41,plain,
% 7.71/1.51      ( v1_funct_1(sK4) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_43,plain,
% 7.71/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1320,plain,
% 7.71/1.51      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 7.71/1.51      | v1_relat_1(sK4) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_1319]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_9,plain,
% 7.71/1.51      ( ~ v1_funct_1(X0)
% 7.71/1.51      | v1_funct_1(k2_funct_1(X0))
% 7.71/1.51      | ~ v1_relat_1(X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f60]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2854,plain,
% 7.71/1.51      ( v1_funct_1(k2_funct_1(sK4))
% 7.71/1.51      | ~ v1_funct_1(sK4)
% 7.71/1.51      | ~ v1_relat_1(sK4) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_9]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2855,plain,
% 7.71/1.51      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 7.71/1.51      | v1_funct_1(sK4) != iProver_top
% 7.71/1.51      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_2854]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_10,plain,
% 7.71/1.51      ( ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_relat_1(X0)
% 7.71/1.51      | v1_relat_1(k2_funct_1(X0)) ),
% 7.71/1.51      inference(cnf_transformation,[],[f59]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2865,plain,
% 7.71/1.51      ( ~ v1_funct_1(sK4)
% 7.71/1.51      | v1_relat_1(k2_funct_1(sK4))
% 7.71/1.51      | ~ v1_relat_1(sK4) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_10]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2866,plain,
% 7.71/1.51      ( v1_funct_1(sK4) != iProver_top
% 7.71/1.51      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 7.71/1.51      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_2865]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3103,plain,
% 7.71/1.51      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)),X0) = iProver_top ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_2832,c_41,c_43,c_1320,c_2855,c_2866]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_4207,plain,
% 7.71/1.51      ( r1_tarski(k9_relat_1(k2_funct_1(sK4),k2_relat_1(k5_relat_1(sK3,sK4))),k2_relat_1(sK3)) = iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_3432,c_3103]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_25,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.71/1.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X3) ),
% 7.71/1.51      inference(cnf_transformation,[],[f76]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1190,plain,
% 7.71/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.71/1.51      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 7.71/1.51      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 7.71/1.51      | v1_funct_1(X0) != iProver_top
% 7.71/1.51      | v1_funct_1(X3) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_18,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f68]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1191,plain,
% 7.71/1.51      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3253,plain,
% 7.71/1.51      ( k2_relset_1(X0,X1,k1_partfun1(X0,X2,X3,X1,X4,X5)) = k2_relat_1(k1_partfun1(X0,X2,X3,X1,X4,X5))
% 7.71/1.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 7.71/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) != iProver_top
% 7.71/1.51      | v1_funct_1(X5) != iProver_top
% 7.71/1.51      | v1_funct_1(X4) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1190,c_1191]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5723,plain,
% 7.71/1.51      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | v1_funct_1(X2) != iProver_top
% 7.71/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1187,c_3253]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5861,plain,
% 7.71/1.51      ( v1_funct_1(X2) != iProver_top
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_5723,c_41]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5862,plain,
% 7.71/1.51      ( k2_relset_1(X0,sK2,k1_partfun1(X0,X1,sK1,sK2,X2,sK4)) = k2_relat_1(k1_partfun1(X0,X1,sK1,sK2,X2,sK4))
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.71/1.51      inference(renaming,[status(thm)],[c_5861]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5869,plain,
% 7.71/1.51      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1185,c_5862]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_27,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X3)
% 7.71/1.51      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f77]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1188,plain,
% 7.71/1.51      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.71/1.51      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.71/1.51      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | v1_funct_1(X5) != iProver_top
% 7.71/1.51      | v1_funct_1(X4) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3344,plain,
% 7.71/1.51      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | v1_funct_1(X2) != iProver_top
% 7.71/1.51      | v1_funct_1(sK4) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1187,c_1188]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3437,plain,
% 7.71/1.51      ( v1_funct_1(X2) != iProver_top
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_3344,c_41]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3438,plain,
% 7.71/1.51      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.71/1.51      | v1_funct_1(X2) != iProver_top ),
% 7.71/1.51      inference(renaming,[status(thm)],[c_3437]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3445,plain,
% 7.71/1.51      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1185,c_3438]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_37,negated_conjecture,
% 7.71/1.51      ( v1_funct_1(sK3) ),
% 7.71/1.51      inference(cnf_transformation,[],[f78]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_38,plain,
% 7.71/1.51      ( v1_funct_1(sK3) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3583,plain,
% 7.71/1.51      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_3445,c_38]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_31,negated_conjecture,
% 7.71/1.51      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 7.71/1.51      inference(cnf_transformation,[],[f84]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3585,plain,
% 7.71/1.51      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_3583,c_31]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5874,plain,
% 7.71/1.51      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
% 7.71/1.51      | v1_funct_1(sK3) != iProver_top ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_5869,c_3583,c_3585]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5883,plain,
% 7.71/1.51      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_5874,c_38]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1186,plain,
% 7.71/1.51      ( v1_funct_1(sK4) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1195,plain,
% 7.71/1.51      ( v1_funct_1(X0) != iProver_top
% 7.71/1.51      | v1_relat_1(X0) != iProver_top
% 7.71/1.51      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_3269,plain,
% 7.71/1.51      ( k9_relat_1(k2_funct_1(X0),k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,k2_funct_1(X0)))
% 7.71/1.51      | v1_funct_1(X0) != iProver_top
% 7.71/1.51      | v1_relat_1(X0) != iProver_top
% 7.71/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1195,c_1198]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8317,plain,
% 7.71/1.51      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
% 7.71/1.51      | v1_relat_1(X0) != iProver_top
% 7.71/1.51      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1186,c_3269]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8471,plain,
% 7.71/1.51      ( v1_relat_1(X0) != iProver_top
% 7.71/1.51      | k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4))) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_8317,c_43,c_1320]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8472,plain,
% 7.71/1.51      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,k2_funct_1(sK4)))
% 7.71/1.51      | v1_relat_1(X0) != iProver_top ),
% 7.71/1.51      inference(renaming,[status(thm)],[c_8471]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8478,plain,
% 7.71/1.51      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = k2_relat_1(k5_relat_1(sK4,k2_funct_1(sK4))) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1583,c_8472]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_17,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f67]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1192,plain,
% 7.71/1.51      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.71/1.51      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2001,plain,
% 7.71/1.51      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1187,c_1192]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_24,plain,
% 7.71/1.51      ( ~ v1_funct_2(X0,X1,X2)
% 7.71/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | k1_relset_1(X1,X2,X0) = X1
% 7.71/1.51      | k1_xboole_0 = X2 ),
% 7.71/1.51      inference(cnf_transformation,[],[f69]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_33,negated_conjecture,
% 7.71/1.51      ( v1_funct_2(sK4,sK1,sK2) ),
% 7.71/1.51      inference(cnf_transformation,[],[f82]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_525,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | k1_relset_1(X1,X2,X0) = X1
% 7.71/1.51      | sK4 != X0
% 7.71/1.51      | sK2 != X2
% 7.71/1.51      | sK1 != X1
% 7.71/1.51      | k1_xboole_0 = X2 ),
% 7.71/1.51      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_526,plain,
% 7.71/1.51      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 7.71/1.51      | k1_relset_1(sK1,sK2,sK4) = sK1
% 7.71/1.51      | k1_xboole_0 = sK2 ),
% 7.71/1.51      inference(unflattening,[status(thm)],[c_525]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_29,negated_conjecture,
% 7.71/1.51      ( k1_xboole_0 != sK2 ),
% 7.71/1.51      inference(cnf_transformation,[],[f86]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_528,plain,
% 7.71/1.51      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_526,c_32,c_29]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2003,plain,
% 7.71/1.51      ( k1_relat_1(sK4) = sK1 ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_2001,c_528]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_14,plain,
% 7.71/1.51      ( ~ v2_funct_1(X0)
% 7.71/1.51      | ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_relat_1(X0)
% 7.71/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 7.71/1.51      inference(cnf_transformation,[],[f63]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_396,plain,
% 7.71/1.51      ( ~ v1_funct_1(X0)
% 7.71/1.51      | ~ v1_relat_1(X0)
% 7.71/1.51      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
% 7.71/1.51      | sK4 != X0 ),
% 7.71/1.51      inference(resolution_lifted,[status(thm)],[c_14,c_30]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_397,plain,
% 7.71/1.51      ( ~ v1_funct_1(sK4)
% 7.71/1.51      | ~ v1_relat_1(sK4)
% 7.71/1.51      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) ),
% 7.71/1.51      inference(unflattening,[status(thm)],[c_396]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_399,plain,
% 7.71/1.51      ( ~ v1_relat_1(sK4)
% 7.71/1.51      | k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_397,c_34]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1182,plain,
% 7.71/1.51      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4))
% 7.71/1.51      | v1_relat_1(sK4) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1737,plain,
% 7.71/1.51      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(k1_relat_1(sK4)) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_1182,c_34,c_32,c_397,c_1319]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2180,plain,
% 7.71/1.51      ( k5_relat_1(sK4,k2_funct_1(sK4)) = k6_relat_1(sK1) ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_2003,c_1737]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_6,plain,
% 7.71/1.51      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
% 7.71/1.51      | ~ v1_relat_1(X1)
% 7.71/1.51      | ~ v1_relat_1(X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f56]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1197,plain,
% 7.71/1.51      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) = iProver_top
% 7.71/1.51      | v1_relat_1(X0) != iProver_top
% 7.71/1.51      | v1_relat_1(X1) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_5887,plain,
% 7.71/1.51      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top
% 7.71/1.51      | v1_relat_1(sK4) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_5883,c_1197]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_40,plain,
% 7.71/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1468,plain,
% 7.71/1.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.71/1.51      | v1_relat_1(sK3) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_15]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1469,plain,
% 7.71/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.71/1.51      | v1_relat_1(sK3) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_1468]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_6300,plain,
% 7.71/1.51      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_5887,c_40,c_43,c_1320,c_1469]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_4,plain,
% 7.71/1.51      ( ~ v5_relat_1(X0,X1)
% 7.71/1.51      | r1_tarski(k2_relat_1(X0),X1)
% 7.71/1.51      | ~ v1_relat_1(X0) ),
% 7.71/1.51      inference(cnf_transformation,[],[f53]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_16,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | v5_relat_1(X0,X2) ),
% 7.71/1.51      inference(cnf_transformation,[],[f66]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_375,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | r1_tarski(k2_relat_1(X3),X4)
% 7.71/1.51      | ~ v1_relat_1(X3)
% 7.71/1.51      | X0 != X3
% 7.71/1.51      | X2 != X4 ),
% 7.71/1.51      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_376,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | r1_tarski(k2_relat_1(X0),X2)
% 7.71/1.51      | ~ v1_relat_1(X0) ),
% 7.71/1.51      inference(unflattening,[status(thm)],[c_375]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_380,plain,
% 7.71/1.51      ( r1_tarski(k2_relat_1(X0),X2)
% 7.71/1.51      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 7.71/1.51      inference(global_propositional_subsumption,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_376,c_15]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_381,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.71/1.51      | r1_tarski(k2_relat_1(X0),X2) ),
% 7.71/1.51      inference(renaming,[status(thm)],[c_380]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1183,plain,
% 7.71/1.51      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.71/1.51      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_381]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2456,plain,
% 7.71/1.51      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1187,c_1183]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_0,plain,
% 7.71/1.51      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 7.71/1.51      inference(cnf_transformation,[],[f52]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1200,plain,
% 7.71/1.51      ( X0 = X1
% 7.71/1.51      | r1_tarski(X0,X1) != iProver_top
% 7.71/1.51      | r1_tarski(X1,X0) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2949,plain,
% 7.71/1.51      ( k2_relat_1(sK4) = sK2
% 7.71/1.51      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_2456,c_1200]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_6305,plain,
% 7.71/1.51      ( k2_relat_1(sK4) = sK2 ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_6300,c_2949]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8486,plain,
% 7.71/1.51      ( k9_relat_1(k2_funct_1(sK4),sK2) = k2_relat_1(k6_relat_1(sK1)) ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_8478,c_2180,c_6305]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_7,plain,
% 7.71/1.51      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 7.71/1.51      inference(cnf_transformation,[],[f58]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_8487,plain,
% 7.71/1.51      ( k9_relat_1(k2_funct_1(sK4),sK2) = sK1 ),
% 7.71/1.51      inference(demodulation,[status(thm)],[c_8486,c_7]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_18163,plain,
% 7.71/1.51      ( r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top ),
% 7.71/1.51      inference(light_normalisation,[status(thm)],[c_4207,c_5883,c_8487]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_743,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1240,plain,
% 7.71/1.51      ( k2_relset_1(sK0,sK1,sK3) != X0
% 7.71/1.51      | k2_relset_1(sK0,sK1,sK3) = sK1
% 7.71/1.51      | sK1 != X0 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_743]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_2019,plain,
% 7.71/1.51      ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 7.71/1.51      | k2_relset_1(sK0,sK1,sK3) = sK1
% 7.71/1.51      | sK1 != k2_relat_1(sK3) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_1240]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1999,plain,
% 7.71/1.51      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 7.71/1.51      inference(superposition,[status(thm)],[c_1185,c_1191]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1281,plain,
% 7.71/1.51      ( ~ r1_tarski(X0,sK1) | ~ r1_tarski(sK1,X0) | sK1 = X0 ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_0]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1343,plain,
% 7.71/1.51      ( ~ r1_tarski(k2_relat_1(X0),sK1)
% 7.71/1.51      | ~ r1_tarski(sK1,k2_relat_1(X0))
% 7.71/1.51      | sK1 = k2_relat_1(X0) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_1281]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1730,plain,
% 7.71/1.51      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 7.71/1.51      | ~ r1_tarski(sK1,k2_relat_1(sK3))
% 7.71/1.51      | sK1 = k2_relat_1(sK3) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_1343]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1731,plain,
% 7.71/1.51      ( sK1 = k2_relat_1(sK3)
% 7.71/1.51      | r1_tarski(k2_relat_1(sK3),sK1) != iProver_top
% 7.71/1.51      | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_1730]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1431,plain,
% 7.71/1.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.71/1.51      | r1_tarski(k2_relat_1(X0),sK1) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_381]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1641,plain,
% 7.71/1.51      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.71/1.51      | r1_tarski(k2_relat_1(sK3),sK1) ),
% 7.71/1.51      inference(instantiation,[status(thm)],[c_1431]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_1642,plain,
% 7.71/1.51      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.71/1.51      | r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 7.71/1.51      inference(predicate_to_equality,[status(thm)],[c_1641]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(c_28,negated_conjecture,
% 7.71/1.51      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 7.71/1.51      inference(cnf_transformation,[],[f87]) ).
% 7.71/1.51  
% 7.71/1.51  cnf(contradiction,plain,
% 7.71/1.51      ( $false ),
% 7.71/1.51      inference(minisat,
% 7.71/1.51                [status(thm)],
% 7.71/1.51                [c_18163,c_2019,c_1999,c_1731,c_1642,c_28,c_40]) ).
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  % SZS output end CNFRefutation for theBenchmark.p
% 7.71/1.51  
% 7.71/1.51  ------                               Statistics
% 7.71/1.51  
% 7.71/1.51  ------ General
% 7.71/1.51  
% 7.71/1.51  abstr_ref_over_cycles:                  0
% 7.71/1.51  abstr_ref_under_cycles:                 0
% 7.71/1.51  gc_basic_clause_elim:                   0
% 7.71/1.51  forced_gc_time:                         0
% 7.71/1.51  parsing_time:                           0.012
% 7.71/1.51  unif_index_cands_time:                  0.
% 7.71/1.51  unif_index_add_time:                    0.
% 7.71/1.51  orderings_time:                         0.
% 7.71/1.51  out_proof_time:                         0.016
% 7.71/1.51  total_time:                             0.623
% 7.71/1.51  num_of_symbols:                         56
% 7.71/1.51  num_of_terms:                           19179
% 7.71/1.51  
% 7.71/1.51  ------ Preprocessing
% 7.71/1.51  
% 7.71/1.51  num_of_splits:                          0
% 7.71/1.51  num_of_split_atoms:                     0
% 7.71/1.51  num_of_reused_defs:                     0
% 7.71/1.51  num_eq_ax_congr_red:                    9
% 7.71/1.51  num_of_sem_filtered_clauses:            1
% 7.71/1.51  num_of_subtypes:                        0
% 7.71/1.51  monotx_restored_types:                  0
% 7.71/1.51  sat_num_of_epr_types:                   0
% 7.71/1.51  sat_num_of_non_cyclic_types:            0
% 7.71/1.51  sat_guarded_non_collapsed_types:        0
% 7.71/1.51  num_pure_diseq_elim:                    0
% 7.71/1.51  simp_replaced_by:                       0
% 7.71/1.51  res_preprocessed:                       170
% 7.71/1.51  prep_upred:                             0
% 7.71/1.51  prep_unflattend:                        39
% 7.71/1.51  smt_new_axioms:                         0
% 7.71/1.51  pred_elim_cands:                        4
% 7.71/1.51  pred_elim:                              3
% 7.71/1.51  pred_elim_cl:                           5
% 7.71/1.51  pred_elim_cycles:                       5
% 7.71/1.51  merged_defs:                            0
% 7.71/1.51  merged_defs_ncl:                        0
% 7.71/1.51  bin_hyper_res:                          0
% 7.71/1.51  prep_cycles:                            4
% 7.71/1.51  pred_elim_time:                         0.005
% 7.71/1.51  splitting_time:                         0.
% 7.71/1.51  sem_filter_time:                        0.
% 7.71/1.51  monotx_time:                            0.
% 7.71/1.51  subtype_inf_time:                       0.
% 7.71/1.51  
% 7.71/1.51  ------ Problem properties
% 7.71/1.51  
% 7.71/1.51  clauses:                                32
% 7.71/1.51  conjectures:                            7
% 7.71/1.51  epr:                                    5
% 7.71/1.51  horn:                                   29
% 7.71/1.51  ground:                                 15
% 7.71/1.51  unary:                                  11
% 7.71/1.51  binary:                                 8
% 7.71/1.51  lits:                                   74
% 7.71/1.51  lits_eq:                                26
% 7.71/1.51  fd_pure:                                0
% 7.71/1.51  fd_pseudo:                              0
% 7.71/1.51  fd_cond:                                0
% 7.71/1.51  fd_pseudo_cond:                         1
% 7.71/1.51  ac_symbols:                             0
% 7.71/1.51  
% 7.71/1.51  ------ Propositional Solver
% 7.71/1.51  
% 7.71/1.51  prop_solver_calls:                      31
% 7.71/1.51  prop_fast_solver_calls:                 1663
% 7.71/1.51  smt_solver_calls:                       0
% 7.71/1.51  smt_fast_solver_calls:                  0
% 7.71/1.51  prop_num_of_clauses:                    9239
% 7.71/1.51  prop_preprocess_simplified:             18100
% 7.71/1.51  prop_fo_subsumed:                       190
% 7.71/1.51  prop_solver_time:                       0.
% 7.71/1.51  smt_solver_time:                        0.
% 7.71/1.51  smt_fast_solver_time:                   0.
% 7.71/1.51  prop_fast_solver_time:                  0.
% 7.71/1.51  prop_unsat_core_time:                   0.001
% 7.71/1.51  
% 7.71/1.51  ------ QBF
% 7.71/1.51  
% 7.71/1.51  qbf_q_res:                              0
% 7.71/1.51  qbf_num_tautologies:                    0
% 7.71/1.51  qbf_prep_cycles:                        0
% 7.71/1.51  
% 7.71/1.51  ------ BMC1
% 7.71/1.51  
% 7.71/1.51  bmc1_current_bound:                     -1
% 7.71/1.51  bmc1_last_solved_bound:                 -1
% 7.71/1.51  bmc1_unsat_core_size:                   -1
% 7.71/1.51  bmc1_unsat_core_parents_size:           -1
% 7.71/1.51  bmc1_merge_next_fun:                    0
% 7.71/1.51  bmc1_unsat_core_clauses_time:           0.
% 7.71/1.51  
% 7.71/1.51  ------ Instantiation
% 7.71/1.51  
% 7.71/1.51  inst_num_of_clauses:                    2734
% 7.71/1.51  inst_num_in_passive:                    1300
% 7.71/1.51  inst_num_in_active:                     1138
% 7.71/1.51  inst_num_in_unprocessed:                296
% 7.71/1.51  inst_num_of_loops:                      1260
% 7.71/1.51  inst_num_of_learning_restarts:          0
% 7.71/1.51  inst_num_moves_active_passive:          118
% 7.71/1.51  inst_lit_activity:                      0
% 7.71/1.51  inst_lit_activity_moves:                0
% 7.71/1.51  inst_num_tautologies:                   0
% 7.71/1.51  inst_num_prop_implied:                  0
% 7.71/1.51  inst_num_existing_simplified:           0
% 7.71/1.51  inst_num_eq_res_simplified:             0
% 7.71/1.51  inst_num_child_elim:                    0
% 7.71/1.51  inst_num_of_dismatching_blockings:      766
% 7.71/1.51  inst_num_of_non_proper_insts:           2838
% 7.71/1.51  inst_num_of_duplicates:                 0
% 7.71/1.51  inst_inst_num_from_inst_to_res:         0
% 7.71/1.51  inst_dismatching_checking_time:         0.
% 7.71/1.51  
% 7.71/1.51  ------ Resolution
% 7.71/1.51  
% 7.71/1.51  res_num_of_clauses:                     0
% 7.71/1.51  res_num_in_passive:                     0
% 7.71/1.51  res_num_in_active:                      0
% 7.71/1.51  res_num_of_loops:                       174
% 7.71/1.51  res_forward_subset_subsumed:            284
% 7.71/1.51  res_backward_subset_subsumed:           0
% 7.71/1.51  res_forward_subsumed:                   0
% 7.71/1.51  res_backward_subsumed:                  0
% 7.71/1.51  res_forward_subsumption_resolution:     0
% 7.71/1.51  res_backward_subsumption_resolution:    0
% 7.71/1.51  res_clause_to_clause_subsumption:       1369
% 7.71/1.51  res_orphan_elimination:                 0
% 7.71/1.51  res_tautology_del:                      190
% 7.71/1.51  res_num_eq_res_simplified:              0
% 7.71/1.51  res_num_sel_changes:                    0
% 7.71/1.51  res_moves_from_active_to_pass:          0
% 7.71/1.51  
% 7.71/1.51  ------ Superposition
% 7.71/1.51  
% 7.71/1.51  sup_time_total:                         0.
% 7.71/1.51  sup_time_generating:                    0.
% 7.71/1.51  sup_time_sim_full:                      0.
% 7.71/1.51  sup_time_sim_immed:                     0.
% 7.71/1.51  
% 7.71/1.51  sup_num_of_clauses:                     580
% 7.71/1.51  sup_num_in_active:                      241
% 7.71/1.51  sup_num_in_passive:                     339
% 7.71/1.51  sup_num_of_loops:                       251
% 7.71/1.51  sup_fw_superposition:                   346
% 7.71/1.51  sup_bw_superposition:                   270
% 7.71/1.51  sup_immediate_simplified:               156
% 7.71/1.51  sup_given_eliminated:                   1
% 7.71/1.51  comparisons_done:                       0
% 7.71/1.51  comparisons_avoided:                    3
% 7.71/1.51  
% 7.71/1.51  ------ Simplifications
% 7.71/1.51  
% 7.71/1.51  
% 7.71/1.51  sim_fw_subset_subsumed:                 6
% 7.71/1.51  sim_bw_subset_subsumed:                 15
% 7.71/1.51  sim_fw_subsumed:                        11
% 7.71/1.51  sim_bw_subsumed:                        0
% 7.71/1.51  sim_fw_subsumption_res:                 0
% 7.71/1.51  sim_bw_subsumption_res:                 0
% 7.71/1.51  sim_tautology_del:                      0
% 7.71/1.51  sim_eq_tautology_del:                   21
% 7.71/1.51  sim_eq_res_simp:                        0
% 7.71/1.51  sim_fw_demodulated:                     26
% 7.71/1.51  sim_bw_demodulated:                     6
% 7.71/1.51  sim_light_normalised:                   154
% 7.71/1.51  sim_joinable_taut:                      0
% 7.71/1.51  sim_joinable_simp:                      0
% 7.71/1.51  sim_ac_normalised:                      0
% 7.71/1.51  sim_smt_subsumption:                    0
% 7.71/1.51  
%------------------------------------------------------------------------------
