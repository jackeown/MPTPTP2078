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
% DateTime   : Thu Dec  3 12:02:18 EST 2020

% Result     : Theorem 3.59s
% Output     : CNFRefutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :  249 (16489 expanded)
%              Number of clauses        :  170 (5308 expanded)
%              Number of leaves         :   24 (4025 expanded)
%              Depth                    :   25
%              Number of atoms          :  770 (126785 expanded)
%              Number of equality atoms :  408 (38744 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   24 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
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
    inference(negated_conjecture,[],[f20])).

fof(f42,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f43,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f42])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( ( ~ v2_funct_1(sK5)
          | ~ v2_funct_1(X3) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 != X2 )
        & k2_relset_1(X0,X1,X3) = X1
        & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,sK5))
        & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK5,X1,X2)
        & v1_funct_1(sK5) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ v2_funct_1(X4)
              | ~ v2_funct_1(X3) )
            & ( k1_xboole_0 = X1
              | k1_xboole_0 != X2 )
            & k2_relset_1(X0,X1,X3) = X1
            & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(sK4) )
          & ( k1_xboole_0 = sK2
            | k1_xboole_0 != sK3 )
          & k2_relset_1(sK1,sK2,sK4) = sK2
          & v2_funct_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
          & v1_funct_2(X4,sK2,sK3)
          & v1_funct_1(X4) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK4,sK1,sK2)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ( ~ v2_funct_1(sK5)
      | ~ v2_funct_1(sK4) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & k2_relset_1(sK1,sK2,sK4) = sK2
    & v2_funct_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f43,f53,f52])).

fof(f95,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f96,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f94,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f90,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f100,plain,
    ( ~ v2_funct_1(sK5)
    | ~ v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f93,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f91,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f54])).

fof(f97,plain,(
    v2_funct_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f54])).

fof(f98,plain,(
    k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f102,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f58,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f85])).

fof(f92,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f50,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f68,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f4,axiom,(
    ! [X0] :
    ? [X1] :
      ( v1_xboole_0(X1)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( v1_xboole_0(sK0(X0))
        & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(sK0(X0))
      & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f46])).

fof(f61,plain,(
    ! [X0] : v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_668,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_41])).

cnf(c_669,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_671,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_40])).

cnf(c_1605,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1613,plain,
    ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3598,plain,
    ( k8_relset_1(sK2,sK3,sK5,sK3) = k1_relset_1(sK2,sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1605,c_1613])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1614,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3115,plain,
    ( k8_relset_1(sK2,sK3,sK5,X0) = k10_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_1605,c_1614])).

cnf(c_3607,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k10_relat_1(sK5,sK3) ),
    inference(demodulation,[status(thm)],[c_3598,c_3115])).

cnf(c_4083,plain,
    ( k10_relat_1(sK5,sK3) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_671,c_3607])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1611,plain,
    ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4279,plain,
    ( k8_relset_1(sK2,sK3,sK5,k7_relset_1(sK2,sK3,sK5,sK2)) = k1_relset_1(sK2,sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1605,c_1611])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1612,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3130,plain,
    ( k7_relset_1(sK2,sK3,sK5,sK2) = k2_relset_1(sK2,sK3,sK5) ),
    inference(superposition,[status(thm)],[c_1605,c_1612])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1615,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2653,plain,
    ( k2_relset_1(sK2,sK3,sK5) = k2_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1605,c_1615])).

cnf(c_3136,plain,
    ( k7_relset_1(sK2,sK3,sK5,sK2) = k2_relat_1(sK5) ),
    inference(light_normalisation,[status(thm)],[c_3130,c_2653])).

cnf(c_4291,plain,
    ( k8_relset_1(sK2,sK3,sK5,k2_relat_1(sK5)) = k10_relat_1(sK5,sK3) ),
    inference(light_normalisation,[status(thm)],[c_4279,c_3136,c_3607])).

cnf(c_5766,plain,
    ( k10_relat_1(sK5,k2_relat_1(sK5)) = k10_relat_1(sK5,sK3) ),
    inference(superposition,[status(thm)],[c_3115,c_4291])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1617,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2463,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_1617])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1622,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2533,plain,
    ( k10_relat_1(sK5,k2_relat_1(sK5)) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2463,c_1622])).

cnf(c_5768,plain,
    ( k10_relat_1(sK5,sK3) = k1_relat_1(sK5) ),
    inference(light_normalisation,[status(thm)],[c_5766,c_2533])).

cnf(c_7879,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4083,c_5768])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1604,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_33,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1608,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3643,plain,
    ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1608,c_1615])).

cnf(c_7582,plain,
    ( k2_relset_1(k1_relat_1(sK5),k2_relat_1(sK5),sK5) = k2_relat_1(sK5)
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1604,c_3643])).

cnf(c_1933,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1954,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))))
    | ~ v1_funct_1(sK5)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_2129,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))))
    | k2_relset_1(k1_relat_1(sK5),k2_relat_1(sK5),sK5) = k2_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_7649,plain,
    ( k2_relset_1(k1_relat_1(sK5),k2_relat_1(sK5),sK5) = k2_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7582,c_42,c_40,c_1933,c_1954,c_2129])).

cnf(c_8045,plain,
    ( k2_relset_1(sK2,k2_relat_1(sK5),sK5) = k2_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7879,c_7649])).

cnf(c_36,negated_conjecture,
    ( ~ v2_funct_1(sK4)
    | ~ v2_funct_1(sK5) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_43,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1603,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1609,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_4355,plain,
    ( k1_partfun1(X0,X1,sK2,sK3,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_1609])).

cnf(c_49,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_4580,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK3,X2,sK5) = k5_relat_1(X2,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4355,c_49])).

cnf(c_4581,plain,
    ( k1_partfun1(X0,X1,sK2,sK3,X2,sK5) = k5_relat_1(X2,sK5)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4580])).

cnf(c_4591,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5)
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_4581])).

cnf(c_45,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2096,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X1,X2,X3,X4,X0,sK5) = k5_relat_1(X0,sK5) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_2401,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(X0,X1,X2,X3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2096])).

cnf(c_2615,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK1,sK2,X0,X1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2401])).

cnf(c_2799,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_funct_1(sK4)
    | ~ v1_funct_1(sK5)
    | k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_2615])).

cnf(c_4662,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4591,c_45,c_43,c_42,c_40,c_2799])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1606,plain,
    ( v2_funct_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4665,plain,
    ( v2_funct_1(k5_relat_1(sK4,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4662,c_1606])).

cnf(c_4666,plain,
    ( v2_funct_1(k5_relat_1(sK4,sK5)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4665])).

cnf(c_2654,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1603,c_1615])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2656,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2654,c_38])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1619,plain,
    ( k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4484,plain,
    ( k1_relat_1(X0) != sK2
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_1619])).

cnf(c_46,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_48,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_1936,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1937,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1936])).

cnf(c_5399,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | k1_relat_1(X0) != sK2
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4484,c_46,c_48,c_1937])).

cnf(c_5400,plain,
    ( k1_relat_1(X0) != sK2
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5399])).

cnf(c_8040,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(k5_relat_1(sK4,sK5)) != iProver_top
    | v2_funct_1(sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7879,c_5400])).

cnf(c_8117,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v2_funct_1(k5_relat_1(sK4,sK5))
    | v2_funct_1(sK5)
    | ~ v1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8040])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1618,plain,
    ( k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4422,plain,
    ( k1_relat_1(X0) != sK2
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_1618])).

cnf(c_5281,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
    | k1_relat_1(X0) != sK2
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4422,c_46,c_48,c_1937])).

cnf(c_5282,plain,
    ( k1_relat_1(X0) != sK2
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5281])).

cnf(c_8041,plain,
    ( sK3 = k1_xboole_0
    | v1_funct_1(sK5) != iProver_top
    | v2_funct_1(k5_relat_1(sK4,sK5)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_7879,c_5282])).

cnf(c_8118,plain,
    ( ~ v1_funct_1(sK5)
    | ~ v2_funct_1(k5_relat_1(sK4,sK5))
    | v2_funct_1(sK4)
    | ~ v1_relat_1(sK5)
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8041])).

cnf(c_8122,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8045,c_42,c_40,c_36,c_1933,c_4666,c_8117,c_8118])).

cnf(c_37,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_8145,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8122,c_37])).

cnf(c_8146,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_8145])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1616,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3614,plain,
    ( v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1605,c_1616])).

cnf(c_8356,plain,
    ( v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8146,c_3614])).

cnf(c_51,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_145,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_149,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_151,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_974,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2416,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_2417,plain,
    ( sK2 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2416])).

cnf(c_2419,plain,
    ( sK2 != k1_xboole_0
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2417])).

cnf(c_973,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1992,plain,
    ( sK2 != X0
    | sK2 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_2564,plain,
    ( sK2 != sK2
    | sK2 = k1_xboole_0
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_1992])).

cnf(c_972,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2565,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_972])).

cnf(c_3054,plain,
    ( sK3 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK3 ),
    inference(instantiation,[status(thm)],[c_973])).

cnf(c_3055,plain,
    ( sK3 != k1_xboole_0
    | k1_xboole_0 = sK3
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3054])).

cnf(c_2765,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3294,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_2765])).

cnf(c_3295,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3294])).

cnf(c_9339,plain,
    ( v1_xboole_0(sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8356,c_42,c_40,c_51,c_37,c_36,c_145,c_149,c_151,c_1933,c_2419,c_2564,c_2565,c_3055,c_3295,c_4666,c_8117,c_8118])).

cnf(c_1628,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1625,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2587,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1628,c_1625])).

cnf(c_9345,plain,
    ( sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9339,c_2587])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_44,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != X1
    | sK2 != k1_xboole_0
    | sK4 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_44])).

cnf(c_576,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_575])).

cnf(c_1597,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_8362,plain,
    ( sK1 = k1_xboole_0
    | sK4 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8146,c_1597])).

cnf(c_8377,plain,
    ( sK1 = k1_xboole_0
    | sK4 = k1_xboole_0
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_8362])).

cnf(c_8365,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8146,c_1603])).

cnf(c_8381,plain,
    ( sK1 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8377,c_8365])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1621,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2696,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | sK2 != k1_xboole_0
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_1621])).

cnf(c_2702,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k1_relat_1(sK4))
    | k1_relat_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_974])).

cnf(c_2704,plain,
    ( v1_xboole_0(k1_relat_1(sK4))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relat_1(sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2702])).

cnf(c_2937,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK4)
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2939,plain,
    ( ~ v1_xboole_0(sK4)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK4 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2937])).

cnf(c_3639,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2))) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2656,c_1608])).

cnf(c_3932,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3639,c_46,c_48,c_1937])).

cnf(c_3942,plain,
    ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3932,c_1616])).

cnf(c_3965,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK4))
    | v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3942])).

cnf(c_11913,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8381,c_48,c_42,c_40,c_37,c_36,c_145,c_149,c_0,c_1933,c_1937,c_2564,c_2565,c_2696,c_2704,c_2939,c_3055,c_3965,c_4666,c_8117,c_8118])).

cnf(c_1607,plain,
    ( v2_funct_1(sK4) != iProver_top
    | v2_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_11948,plain,
    ( v2_funct_1(sK5) != iProver_top
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11913,c_1607])).

cnf(c_13160,plain,
    ( v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9345,c_11948])).

cnf(c_11944,plain,
    ( v2_funct_1(k5_relat_1(k1_xboole_0,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11913,c_4665])).

cnf(c_13157,plain,
    ( v2_funct_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9345,c_11944])).

cnf(c_8361,plain,
    ( k2_relat_1(sK4) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8146,c_2656])).

cnf(c_11939,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11913,c_8361])).

cnf(c_8347,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
    | v2_funct_1(sK4) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8146,c_5282])).

cnf(c_11916,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(k1_xboole_0,X0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11913,c_8347])).

cnf(c_12030,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v2_funct_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v2_funct_1(k1_xboole_0) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11916])).

cnf(c_5,plain,
    ( v1_xboole_0(sK0(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1624,plain,
    ( v1_xboole_0(sK0(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3290,plain,
    ( sK0(X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1624,c_2587])).

cnf(c_6,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1623,plain,
    ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2462,plain,
    ( v1_relat_1(sK0(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_1617])).

cnf(c_3509,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3290,c_2462])).

cnf(c_3517,plain,
    ( v1_relat_1(k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3509])).

cnf(c_2418,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2416])).

cnf(c_2257,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK5)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2259,plain,
    ( ~ v1_xboole_0(sK5)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_2257])).

cnf(c_980,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1944,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK5)
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_980])).

cnf(c_1945,plain,
    ( X0 != sK5
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1944])).

cnf(c_1947,plain,
    ( k1_xboole_0 != sK5
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1945])).

cnf(c_118,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13160,c_13157,c_11939,c_12030,c_8122,c_3517,c_3509,c_3294,c_3055,c_2565,c_2564,c_2418,c_2259,c_1947,c_0,c_149,c_145,c_118,c_37,c_40,c_49])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 14:06:23 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.59/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.59/0.99  
% 3.59/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.59/0.99  
% 3.59/0.99  ------  iProver source info
% 3.59/0.99  
% 3.59/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.59/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.59/0.99  git: non_committed_changes: false
% 3.59/0.99  git: last_make_outside_of_git: false
% 3.59/0.99  
% 3.59/0.99  ------ 
% 3.59/0.99  
% 3.59/0.99  ------ Input Options
% 3.59/0.99  
% 3.59/0.99  --out_options                           all
% 3.59/0.99  --tptp_safe_out                         true
% 3.59/0.99  --problem_path                          ""
% 3.59/0.99  --include_path                          ""
% 3.59/0.99  --clausifier                            res/vclausify_rel
% 3.59/0.99  --clausifier_options                    --mode clausify
% 3.59/0.99  --stdin                                 false
% 3.59/0.99  --stats_out                             all
% 3.59/0.99  
% 3.59/0.99  ------ General Options
% 3.59/0.99  
% 3.59/0.99  --fof                                   false
% 3.59/0.99  --time_out_real                         305.
% 3.59/0.99  --time_out_virtual                      -1.
% 3.59/0.99  --symbol_type_check                     false
% 3.59/0.99  --clausify_out                          false
% 3.59/0.99  --sig_cnt_out                           false
% 3.59/0.99  --trig_cnt_out                          false
% 3.59/0.99  --trig_cnt_out_tolerance                1.
% 3.59/0.99  --trig_cnt_out_sk_spl                   false
% 3.59/0.99  --abstr_cl_out                          false
% 3.59/0.99  
% 3.59/0.99  ------ Global Options
% 3.59/0.99  
% 3.59/0.99  --schedule                              default
% 3.59/0.99  --add_important_lit                     false
% 3.59/0.99  --prop_solver_per_cl                    1000
% 3.59/0.99  --min_unsat_core                        false
% 3.59/0.99  --soft_assumptions                      false
% 3.59/0.99  --soft_lemma_size                       3
% 3.59/0.99  --prop_impl_unit_size                   0
% 3.59/0.99  --prop_impl_unit                        []
% 3.59/0.99  --share_sel_clauses                     true
% 3.59/0.99  --reset_solvers                         false
% 3.59/0.99  --bc_imp_inh                            [conj_cone]
% 3.59/0.99  --conj_cone_tolerance                   3.
% 3.59/0.99  --extra_neg_conj                        none
% 3.59/0.99  --large_theory_mode                     true
% 3.59/0.99  --prolific_symb_bound                   200
% 3.59/0.99  --lt_threshold                          2000
% 3.59/0.99  --clause_weak_htbl                      true
% 3.59/0.99  --gc_record_bc_elim                     false
% 3.59/0.99  
% 3.59/0.99  ------ Preprocessing Options
% 3.59/0.99  
% 3.59/0.99  --preprocessing_flag                    true
% 3.59/0.99  --time_out_prep_mult                    0.1
% 3.59/0.99  --splitting_mode                        input
% 3.59/0.99  --splitting_grd                         true
% 3.59/0.99  --splitting_cvd                         false
% 3.59/0.99  --splitting_cvd_svl                     false
% 3.59/0.99  --splitting_nvd                         32
% 3.59/0.99  --sub_typing                            true
% 3.59/0.99  --prep_gs_sim                           true
% 3.59/0.99  --prep_unflatten                        true
% 3.59/0.99  --prep_res_sim                          true
% 3.59/0.99  --prep_upred                            true
% 3.59/0.99  --prep_sem_filter                       exhaustive
% 3.59/0.99  --prep_sem_filter_out                   false
% 3.59/0.99  --pred_elim                             true
% 3.59/0.99  --res_sim_input                         true
% 3.59/0.99  --eq_ax_congr_red                       true
% 3.59/0.99  --pure_diseq_elim                       true
% 3.59/0.99  --brand_transform                       false
% 3.59/0.99  --non_eq_to_eq                          false
% 3.59/0.99  --prep_def_merge                        true
% 3.59/0.99  --prep_def_merge_prop_impl              false
% 3.59/0.99  --prep_def_merge_mbd                    true
% 3.59/0.99  --prep_def_merge_tr_red                 false
% 3.59/0.99  --prep_def_merge_tr_cl                  false
% 3.59/0.99  --smt_preprocessing                     true
% 3.59/0.99  --smt_ac_axioms                         fast
% 3.59/0.99  --preprocessed_out                      false
% 3.59/0.99  --preprocessed_stats                    false
% 3.59/0.99  
% 3.59/0.99  ------ Abstraction refinement Options
% 3.59/0.99  
% 3.59/0.99  --abstr_ref                             []
% 3.59/0.99  --abstr_ref_prep                        false
% 3.59/0.99  --abstr_ref_until_sat                   false
% 3.59/0.99  --abstr_ref_sig_restrict                funpre
% 3.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.99  --abstr_ref_under                       []
% 3.59/0.99  
% 3.59/0.99  ------ SAT Options
% 3.59/0.99  
% 3.59/0.99  --sat_mode                              false
% 3.59/0.99  --sat_fm_restart_options                ""
% 3.59/0.99  --sat_gr_def                            false
% 3.59/0.99  --sat_epr_types                         true
% 3.59/0.99  --sat_non_cyclic_types                  false
% 3.59/0.99  --sat_finite_models                     false
% 3.59/0.99  --sat_fm_lemmas                         false
% 3.59/0.99  --sat_fm_prep                           false
% 3.59/0.99  --sat_fm_uc_incr                        true
% 3.59/0.99  --sat_out_model                         small
% 3.59/0.99  --sat_out_clauses                       false
% 3.59/0.99  
% 3.59/0.99  ------ QBF Options
% 3.59/0.99  
% 3.59/0.99  --qbf_mode                              false
% 3.59/0.99  --qbf_elim_univ                         false
% 3.59/0.99  --qbf_dom_inst                          none
% 3.59/0.99  --qbf_dom_pre_inst                      false
% 3.59/0.99  --qbf_sk_in                             false
% 3.59/0.99  --qbf_pred_elim                         true
% 3.59/0.99  --qbf_split                             512
% 3.59/0.99  
% 3.59/0.99  ------ BMC1 Options
% 3.59/0.99  
% 3.59/0.99  --bmc1_incremental                      false
% 3.59/0.99  --bmc1_axioms                           reachable_all
% 3.59/0.99  --bmc1_min_bound                        0
% 3.59/0.99  --bmc1_max_bound                        -1
% 3.59/0.99  --bmc1_max_bound_default                -1
% 3.59/0.99  --bmc1_symbol_reachability              true
% 3.59/0.99  --bmc1_property_lemmas                  false
% 3.59/0.99  --bmc1_k_induction                      false
% 3.59/0.99  --bmc1_non_equiv_states                 false
% 3.59/0.99  --bmc1_deadlock                         false
% 3.59/0.99  --bmc1_ucm                              false
% 3.59/0.99  --bmc1_add_unsat_core                   none
% 3.59/0.99  --bmc1_unsat_core_children              false
% 3.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.99  --bmc1_out_stat                         full
% 3.59/0.99  --bmc1_ground_init                      false
% 3.59/0.99  --bmc1_pre_inst_next_state              false
% 3.59/0.99  --bmc1_pre_inst_state                   false
% 3.59/0.99  --bmc1_pre_inst_reach_state             false
% 3.59/0.99  --bmc1_out_unsat_core                   false
% 3.59/0.99  --bmc1_aig_witness_out                  false
% 3.59/0.99  --bmc1_verbose                          false
% 3.59/0.99  --bmc1_dump_clauses_tptp                false
% 3.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.99  --bmc1_dump_file                        -
% 3.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.99  --bmc1_ucm_extend_mode                  1
% 3.59/0.99  --bmc1_ucm_init_mode                    2
% 3.59/0.99  --bmc1_ucm_cone_mode                    none
% 3.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.99  --bmc1_ucm_relax_model                  4
% 3.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.99  --bmc1_ucm_layered_model                none
% 3.59/0.99  --bmc1_ucm_max_lemma_size               10
% 3.59/0.99  
% 3.59/0.99  ------ AIG Options
% 3.59/0.99  
% 3.59/0.99  --aig_mode                              false
% 3.59/0.99  
% 3.59/0.99  ------ Instantiation Options
% 3.59/0.99  
% 3.59/0.99  --instantiation_flag                    true
% 3.59/0.99  --inst_sos_flag                         false
% 3.59/0.99  --inst_sos_phase                        true
% 3.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.99  --inst_lit_sel_side                     num_symb
% 3.59/0.99  --inst_solver_per_active                1400
% 3.59/0.99  --inst_solver_calls_frac                1.
% 3.59/0.99  --inst_passive_queue_type               priority_queues
% 3.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.99  --inst_passive_queues_freq              [25;2]
% 3.59/0.99  --inst_dismatching                      true
% 3.59/0.99  --inst_eager_unprocessed_to_passive     true
% 3.59/0.99  --inst_prop_sim_given                   true
% 3.59/0.99  --inst_prop_sim_new                     false
% 3.59/0.99  --inst_subs_new                         false
% 3.59/0.99  --inst_eq_res_simp                      false
% 3.59/0.99  --inst_subs_given                       false
% 3.59/0.99  --inst_orphan_elimination               true
% 3.59/0.99  --inst_learning_loop_flag               true
% 3.59/0.99  --inst_learning_start                   3000
% 3.59/0.99  --inst_learning_factor                  2
% 3.59/0.99  --inst_start_prop_sim_after_learn       3
% 3.59/0.99  --inst_sel_renew                        solver
% 3.59/0.99  --inst_lit_activity_flag                true
% 3.59/0.99  --inst_restr_to_given                   false
% 3.59/0.99  --inst_activity_threshold               500
% 3.59/0.99  --inst_out_proof                        true
% 3.59/0.99  
% 3.59/0.99  ------ Resolution Options
% 3.59/0.99  
% 3.59/0.99  --resolution_flag                       true
% 3.59/0.99  --res_lit_sel                           adaptive
% 3.59/0.99  --res_lit_sel_side                      none
% 3.59/0.99  --res_ordering                          kbo
% 3.59/0.99  --res_to_prop_solver                    active
% 3.59/0.99  --res_prop_simpl_new                    false
% 3.59/0.99  --res_prop_simpl_given                  true
% 3.59/0.99  --res_passive_queue_type                priority_queues
% 3.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.99  --res_passive_queues_freq               [15;5]
% 3.59/0.99  --res_forward_subs                      full
% 3.59/0.99  --res_backward_subs                     full
% 3.59/0.99  --res_forward_subs_resolution           true
% 3.59/0.99  --res_backward_subs_resolution          true
% 3.59/0.99  --res_orphan_elimination                true
% 3.59/0.99  --res_time_limit                        2.
% 3.59/0.99  --res_out_proof                         true
% 3.59/0.99  
% 3.59/0.99  ------ Superposition Options
% 3.59/0.99  
% 3.59/0.99  --superposition_flag                    true
% 3.59/0.99  --sup_passive_queue_type                priority_queues
% 3.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.99  --demod_completeness_check              fast
% 3.59/0.99  --demod_use_ground                      true
% 3.59/0.99  --sup_to_prop_solver                    passive
% 3.59/0.99  --sup_prop_simpl_new                    true
% 3.59/0.99  --sup_prop_simpl_given                  true
% 3.59/0.99  --sup_fun_splitting                     false
% 3.59/0.99  --sup_smt_interval                      50000
% 3.59/0.99  
% 3.59/0.99  ------ Superposition Simplification Setup
% 3.59/0.99  
% 3.59/0.99  --sup_indices_passive                   []
% 3.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.99  --sup_full_bw                           [BwDemod]
% 3.59/0.99  --sup_immed_triv                        [TrivRules]
% 3.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.99  --sup_immed_bw_main                     []
% 3.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.99  
% 3.59/0.99  ------ Combination Options
% 3.59/0.99  
% 3.59/0.99  --comb_res_mult                         3
% 3.59/0.99  --comb_sup_mult                         2
% 3.59/0.99  --comb_inst_mult                        10
% 3.59/0.99  
% 3.59/0.99  ------ Debug Options
% 3.59/0.99  
% 3.59/0.99  --dbg_backtrace                         false
% 3.59/0.99  --dbg_dump_prop_clauses                 false
% 3.59/0.99  --dbg_dump_prop_clauses_file            -
% 3.59/0.99  --dbg_out_stat                          false
% 3.59/0.99  ------ Parsing...
% 3.59/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.59/0.99  
% 3.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.59/0.99  
% 3.59/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.59/0.99  
% 3.59/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.59/0.99  ------ Proving...
% 3.59/0.99  ------ Problem Properties 
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  clauses                                 40
% 3.59/0.99  conjectures                             8
% 3.59/0.99  EPR                                     8
% 3.59/0.99  Horn                                    34
% 3.59/0.99  unary                                   10
% 3.59/0.99  binary                                  14
% 3.59/0.99  lits                                    102
% 3.59/0.99  lits eq                                 40
% 3.59/0.99  fd_pure                                 0
% 3.59/0.99  fd_pseudo                               0
% 3.59/0.99  fd_cond                                 1
% 3.59/0.99  fd_pseudo_cond                          2
% 3.59/0.99  AC symbols                              0
% 3.59/0.99  
% 3.59/0.99  ------ Schedule dynamic 5 is on 
% 3.59/0.99  
% 3.59/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  ------ 
% 3.59/0.99  Current options:
% 3.59/0.99  ------ 
% 3.59/0.99  
% 3.59/0.99  ------ Input Options
% 3.59/0.99  
% 3.59/0.99  --out_options                           all
% 3.59/0.99  --tptp_safe_out                         true
% 3.59/0.99  --problem_path                          ""
% 3.59/0.99  --include_path                          ""
% 3.59/0.99  --clausifier                            res/vclausify_rel
% 3.59/0.99  --clausifier_options                    --mode clausify
% 3.59/0.99  --stdin                                 false
% 3.59/0.99  --stats_out                             all
% 3.59/0.99  
% 3.59/0.99  ------ General Options
% 3.59/0.99  
% 3.59/0.99  --fof                                   false
% 3.59/0.99  --time_out_real                         305.
% 3.59/0.99  --time_out_virtual                      -1.
% 3.59/0.99  --symbol_type_check                     false
% 3.59/0.99  --clausify_out                          false
% 3.59/0.99  --sig_cnt_out                           false
% 3.59/0.99  --trig_cnt_out                          false
% 3.59/0.99  --trig_cnt_out_tolerance                1.
% 3.59/0.99  --trig_cnt_out_sk_spl                   false
% 3.59/0.99  --abstr_cl_out                          false
% 3.59/0.99  
% 3.59/0.99  ------ Global Options
% 3.59/0.99  
% 3.59/0.99  --schedule                              default
% 3.59/0.99  --add_important_lit                     false
% 3.59/0.99  --prop_solver_per_cl                    1000
% 3.59/0.99  --min_unsat_core                        false
% 3.59/0.99  --soft_assumptions                      false
% 3.59/0.99  --soft_lemma_size                       3
% 3.59/0.99  --prop_impl_unit_size                   0
% 3.59/0.99  --prop_impl_unit                        []
% 3.59/0.99  --share_sel_clauses                     true
% 3.59/0.99  --reset_solvers                         false
% 3.59/0.99  --bc_imp_inh                            [conj_cone]
% 3.59/0.99  --conj_cone_tolerance                   3.
% 3.59/0.99  --extra_neg_conj                        none
% 3.59/0.99  --large_theory_mode                     true
% 3.59/0.99  --prolific_symb_bound                   200
% 3.59/0.99  --lt_threshold                          2000
% 3.59/0.99  --clause_weak_htbl                      true
% 3.59/0.99  --gc_record_bc_elim                     false
% 3.59/0.99  
% 3.59/0.99  ------ Preprocessing Options
% 3.59/0.99  
% 3.59/0.99  --preprocessing_flag                    true
% 3.59/0.99  --time_out_prep_mult                    0.1
% 3.59/0.99  --splitting_mode                        input
% 3.59/0.99  --splitting_grd                         true
% 3.59/0.99  --splitting_cvd                         false
% 3.59/0.99  --splitting_cvd_svl                     false
% 3.59/0.99  --splitting_nvd                         32
% 3.59/0.99  --sub_typing                            true
% 3.59/0.99  --prep_gs_sim                           true
% 3.59/0.99  --prep_unflatten                        true
% 3.59/0.99  --prep_res_sim                          true
% 3.59/0.99  --prep_upred                            true
% 3.59/0.99  --prep_sem_filter                       exhaustive
% 3.59/0.99  --prep_sem_filter_out                   false
% 3.59/0.99  --pred_elim                             true
% 3.59/0.99  --res_sim_input                         true
% 3.59/0.99  --eq_ax_congr_red                       true
% 3.59/0.99  --pure_diseq_elim                       true
% 3.59/0.99  --brand_transform                       false
% 3.59/0.99  --non_eq_to_eq                          false
% 3.59/0.99  --prep_def_merge                        true
% 3.59/0.99  --prep_def_merge_prop_impl              false
% 3.59/0.99  --prep_def_merge_mbd                    true
% 3.59/0.99  --prep_def_merge_tr_red                 false
% 3.59/0.99  --prep_def_merge_tr_cl                  false
% 3.59/0.99  --smt_preprocessing                     true
% 3.59/0.99  --smt_ac_axioms                         fast
% 3.59/0.99  --preprocessed_out                      false
% 3.59/0.99  --preprocessed_stats                    false
% 3.59/0.99  
% 3.59/0.99  ------ Abstraction refinement Options
% 3.59/0.99  
% 3.59/0.99  --abstr_ref                             []
% 3.59/0.99  --abstr_ref_prep                        false
% 3.59/0.99  --abstr_ref_until_sat                   false
% 3.59/0.99  --abstr_ref_sig_restrict                funpre
% 3.59/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.59/0.99  --abstr_ref_under                       []
% 3.59/0.99  
% 3.59/0.99  ------ SAT Options
% 3.59/0.99  
% 3.59/0.99  --sat_mode                              false
% 3.59/0.99  --sat_fm_restart_options                ""
% 3.59/0.99  --sat_gr_def                            false
% 3.59/0.99  --sat_epr_types                         true
% 3.59/0.99  --sat_non_cyclic_types                  false
% 3.59/0.99  --sat_finite_models                     false
% 3.59/0.99  --sat_fm_lemmas                         false
% 3.59/0.99  --sat_fm_prep                           false
% 3.59/0.99  --sat_fm_uc_incr                        true
% 3.59/0.99  --sat_out_model                         small
% 3.59/0.99  --sat_out_clauses                       false
% 3.59/0.99  
% 3.59/0.99  ------ QBF Options
% 3.59/0.99  
% 3.59/0.99  --qbf_mode                              false
% 3.59/0.99  --qbf_elim_univ                         false
% 3.59/0.99  --qbf_dom_inst                          none
% 3.59/0.99  --qbf_dom_pre_inst                      false
% 3.59/0.99  --qbf_sk_in                             false
% 3.59/0.99  --qbf_pred_elim                         true
% 3.59/0.99  --qbf_split                             512
% 3.59/0.99  
% 3.59/0.99  ------ BMC1 Options
% 3.59/0.99  
% 3.59/0.99  --bmc1_incremental                      false
% 3.59/0.99  --bmc1_axioms                           reachable_all
% 3.59/0.99  --bmc1_min_bound                        0
% 3.59/0.99  --bmc1_max_bound                        -1
% 3.59/0.99  --bmc1_max_bound_default                -1
% 3.59/0.99  --bmc1_symbol_reachability              true
% 3.59/0.99  --bmc1_property_lemmas                  false
% 3.59/0.99  --bmc1_k_induction                      false
% 3.59/0.99  --bmc1_non_equiv_states                 false
% 3.59/0.99  --bmc1_deadlock                         false
% 3.59/0.99  --bmc1_ucm                              false
% 3.59/0.99  --bmc1_add_unsat_core                   none
% 3.59/0.99  --bmc1_unsat_core_children              false
% 3.59/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.59/0.99  --bmc1_out_stat                         full
% 3.59/0.99  --bmc1_ground_init                      false
% 3.59/0.99  --bmc1_pre_inst_next_state              false
% 3.59/0.99  --bmc1_pre_inst_state                   false
% 3.59/0.99  --bmc1_pre_inst_reach_state             false
% 3.59/0.99  --bmc1_out_unsat_core                   false
% 3.59/0.99  --bmc1_aig_witness_out                  false
% 3.59/0.99  --bmc1_verbose                          false
% 3.59/0.99  --bmc1_dump_clauses_tptp                false
% 3.59/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.59/0.99  --bmc1_dump_file                        -
% 3.59/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.59/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.59/0.99  --bmc1_ucm_extend_mode                  1
% 3.59/0.99  --bmc1_ucm_init_mode                    2
% 3.59/0.99  --bmc1_ucm_cone_mode                    none
% 3.59/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.59/0.99  --bmc1_ucm_relax_model                  4
% 3.59/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.59/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.59/0.99  --bmc1_ucm_layered_model                none
% 3.59/0.99  --bmc1_ucm_max_lemma_size               10
% 3.59/0.99  
% 3.59/0.99  ------ AIG Options
% 3.59/0.99  
% 3.59/0.99  --aig_mode                              false
% 3.59/0.99  
% 3.59/0.99  ------ Instantiation Options
% 3.59/0.99  
% 3.59/0.99  --instantiation_flag                    true
% 3.59/0.99  --inst_sos_flag                         false
% 3.59/0.99  --inst_sos_phase                        true
% 3.59/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.59/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.59/0.99  --inst_lit_sel_side                     none
% 3.59/0.99  --inst_solver_per_active                1400
% 3.59/0.99  --inst_solver_calls_frac                1.
% 3.59/0.99  --inst_passive_queue_type               priority_queues
% 3.59/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.59/0.99  --inst_passive_queues_freq              [25;2]
% 3.59/0.99  --inst_dismatching                      true
% 3.59/0.99  --inst_eager_unprocessed_to_passive     true
% 3.59/0.99  --inst_prop_sim_given                   true
% 3.59/0.99  --inst_prop_sim_new                     false
% 3.59/0.99  --inst_subs_new                         false
% 3.59/0.99  --inst_eq_res_simp                      false
% 3.59/0.99  --inst_subs_given                       false
% 3.59/0.99  --inst_orphan_elimination               true
% 3.59/0.99  --inst_learning_loop_flag               true
% 3.59/0.99  --inst_learning_start                   3000
% 3.59/0.99  --inst_learning_factor                  2
% 3.59/0.99  --inst_start_prop_sim_after_learn       3
% 3.59/0.99  --inst_sel_renew                        solver
% 3.59/0.99  --inst_lit_activity_flag                true
% 3.59/0.99  --inst_restr_to_given                   false
% 3.59/0.99  --inst_activity_threshold               500
% 3.59/0.99  --inst_out_proof                        true
% 3.59/0.99  
% 3.59/0.99  ------ Resolution Options
% 3.59/0.99  
% 3.59/0.99  --resolution_flag                       false
% 3.59/0.99  --res_lit_sel                           adaptive
% 3.59/0.99  --res_lit_sel_side                      none
% 3.59/0.99  --res_ordering                          kbo
% 3.59/0.99  --res_to_prop_solver                    active
% 3.59/0.99  --res_prop_simpl_new                    false
% 3.59/0.99  --res_prop_simpl_given                  true
% 3.59/0.99  --res_passive_queue_type                priority_queues
% 3.59/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.59/0.99  --res_passive_queues_freq               [15;5]
% 3.59/0.99  --res_forward_subs                      full
% 3.59/0.99  --res_backward_subs                     full
% 3.59/0.99  --res_forward_subs_resolution           true
% 3.59/0.99  --res_backward_subs_resolution          true
% 3.59/0.99  --res_orphan_elimination                true
% 3.59/0.99  --res_time_limit                        2.
% 3.59/0.99  --res_out_proof                         true
% 3.59/0.99  
% 3.59/0.99  ------ Superposition Options
% 3.59/0.99  
% 3.59/0.99  --superposition_flag                    true
% 3.59/0.99  --sup_passive_queue_type                priority_queues
% 3.59/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.59/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.59/0.99  --demod_completeness_check              fast
% 3.59/0.99  --demod_use_ground                      true
% 3.59/0.99  --sup_to_prop_solver                    passive
% 3.59/0.99  --sup_prop_simpl_new                    true
% 3.59/0.99  --sup_prop_simpl_given                  true
% 3.59/0.99  --sup_fun_splitting                     false
% 3.59/0.99  --sup_smt_interval                      50000
% 3.59/0.99  
% 3.59/0.99  ------ Superposition Simplification Setup
% 3.59/0.99  
% 3.59/0.99  --sup_indices_passive                   []
% 3.59/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.59/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.59/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.99  --sup_full_bw                           [BwDemod]
% 3.59/0.99  --sup_immed_triv                        [TrivRules]
% 3.59/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.59/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.99  --sup_immed_bw_main                     []
% 3.59/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.59/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.59/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.59/0.99  
% 3.59/0.99  ------ Combination Options
% 3.59/0.99  
% 3.59/0.99  --comb_res_mult                         3
% 3.59/0.99  --comb_sup_mult                         2
% 3.59/0.99  --comb_inst_mult                        10
% 3.59/0.99  
% 3.59/0.99  ------ Debug Options
% 3.59/0.99  
% 3.59/0.99  --dbg_backtrace                         false
% 3.59/0.99  --dbg_dump_prop_clauses                 false
% 3.59/0.99  --dbg_dump_prop_clauses_file            -
% 3.59/0.99  --dbg_out_stat                          false
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  ------ Proving...
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  % SZS status Theorem for theBenchmark.p
% 3.59/0.99  
% 3.59/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.59/0.99  
% 3.59/0.99  fof(f17,axiom,(
% 3.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f36,plain,(
% 3.59/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(ennf_transformation,[],[f17])).
% 3.59/0.99  
% 3.59/0.99  fof(f37,plain,(
% 3.59/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(flattening,[],[f36])).
% 3.59/0.99  
% 3.59/0.99  fof(f51,plain,(
% 3.59/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(nnf_transformation,[],[f37])).
% 3.59/0.99  
% 3.59/0.99  fof(f81,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f51])).
% 3.59/0.99  
% 3.59/0.99  fof(f20,conjecture,(
% 3.59/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f21,negated_conjecture,(
% 3.59/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.59/0.99    inference(negated_conjecture,[],[f20])).
% 3.59/0.99  
% 3.59/0.99  fof(f42,plain,(
% 3.59/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2)) & (k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.59/0.99    inference(ennf_transformation,[],[f21])).
% 3.59/0.99  
% 3.59/0.99  fof(f43,plain,(
% 3.59/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.59/0.99    inference(flattening,[],[f42])).
% 3.59/0.99  
% 3.59/0.99  fof(f53,plain,(
% 3.59/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((~v2_funct_1(sK5) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK5,X1,X2) & v1_funct_1(sK5))) )),
% 3.59/0.99    introduced(choice_axiom,[])).
% 3.59/0.99  
% 3.59/0.99  fof(f52,plain,(
% 3.59/0.99    ? [X0,X1,X2,X3] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(sK4)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & k2_relset_1(sK1,sK2,sK4) = sK2 & v2_funct_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(X4,sK2,sK3) & v1_funct_1(X4)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4))),
% 3.59/0.99    introduced(choice_axiom,[])).
% 3.59/0.99  
% 3.59/0.99  fof(f54,plain,(
% 3.59/0.99    ((~v2_funct_1(sK5) | ~v2_funct_1(sK4)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & k2_relset_1(sK1,sK2,sK4) = sK2 & v2_funct_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)),
% 3.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4,sK5])],[f43,f53,f52])).
% 3.59/0.99  
% 3.59/0.99  fof(f95,plain,(
% 3.59/0.99    v1_funct_2(sK5,sK2,sK3)),
% 3.59/0.99    inference(cnf_transformation,[],[f54])).
% 3.59/0.99  
% 3.59/0.99  fof(f96,plain,(
% 3.59/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.59/0.99    inference(cnf_transformation,[],[f54])).
% 3.59/0.99  
% 3.59/0.99  fof(f15,axiom,(
% 3.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f34,plain,(
% 3.59/0.99    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(ennf_transformation,[],[f15])).
% 3.59/0.99  
% 3.59/0.99  fof(f78,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f34])).
% 3.59/0.99  
% 3.59/0.99  fof(f14,axiom,(
% 3.59/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f33,plain,(
% 3.59/0.99    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(ennf_transformation,[],[f14])).
% 3.59/0.99  
% 3.59/0.99  fof(f76,plain,(
% 3.59/0.99    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f33])).
% 3.59/0.99  
% 3.59/0.99  fof(f16,axiom,(
% 3.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f35,plain,(
% 3.59/0.99    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k2_relset_1(X1,X0,X2) = k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 3.59/0.99    inference(ennf_transformation,[],[f16])).
% 3.59/0.99  
% 3.59/0.99  fof(f80,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f35])).
% 3.59/0.99  
% 3.59/0.99  fof(f77,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f34])).
% 3.59/0.99  
% 3.59/0.99  fof(f13,axiom,(
% 3.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f32,plain,(
% 3.59/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(ennf_transformation,[],[f13])).
% 3.59/0.99  
% 3.59/0.99  fof(f75,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f32])).
% 3.59/0.99  
% 3.59/0.99  fof(f10,axiom,(
% 3.59/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f29,plain,(
% 3.59/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.59/0.99    inference(ennf_transformation,[],[f10])).
% 3.59/0.99  
% 3.59/0.99  fof(f71,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f29])).
% 3.59/0.99  
% 3.59/0.99  fof(f7,axiom,(
% 3.59/0.99    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f25,plain,(
% 3.59/0.99    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.59/0.99    inference(ennf_transformation,[],[f7])).
% 3.59/0.99  
% 3.59/0.99  fof(f66,plain,(
% 3.59/0.99    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f25])).
% 3.59/0.99  
% 3.59/0.99  fof(f94,plain,(
% 3.59/0.99    v1_funct_1(sK5)),
% 3.59/0.99    inference(cnf_transformation,[],[f54])).
% 3.59/0.99  
% 3.59/0.99  fof(f19,axiom,(
% 3.59/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f40,plain,(
% 3.59/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.59/0.99    inference(ennf_transformation,[],[f19])).
% 3.59/0.99  
% 3.59/0.99  fof(f41,plain,(
% 3.59/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.59/0.99    inference(flattening,[],[f40])).
% 3.59/0.99  
% 3.59/0.99  fof(f90,plain,(
% 3.59/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f41])).
% 3.59/0.99  
% 3.59/0.99  fof(f100,plain,(
% 3.59/0.99    ~v2_funct_1(sK5) | ~v2_funct_1(sK4)),
% 3.59/0.99    inference(cnf_transformation,[],[f54])).
% 3.59/0.99  
% 3.59/0.99  fof(f93,plain,(
% 3.59/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.59/0.99    inference(cnf_transformation,[],[f54])).
% 3.59/0.99  
% 3.59/0.99  fof(f18,axiom,(
% 3.59/0.99    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f38,plain,(
% 3.59/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.59/0.99    inference(ennf_transformation,[],[f18])).
% 3.59/0.99  
% 3.59/0.99  fof(f39,plain,(
% 3.59/0.99    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.59/0.99    inference(flattening,[],[f38])).
% 3.59/0.99  
% 3.59/0.99  fof(f87,plain,(
% 3.59/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f39])).
% 3.59/0.99  
% 3.59/0.99  fof(f91,plain,(
% 3.59/0.99    v1_funct_1(sK4)),
% 3.59/0.99    inference(cnf_transformation,[],[f54])).
% 3.59/0.99  
% 3.59/0.99  fof(f97,plain,(
% 3.59/0.99    v2_funct_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5))),
% 3.59/0.99    inference(cnf_transformation,[],[f54])).
% 3.59/0.99  
% 3.59/0.99  fof(f98,plain,(
% 3.59/0.99    k2_relset_1(sK1,sK2,sK4) = sK2),
% 3.59/0.99    inference(cnf_transformation,[],[f54])).
% 3.59/0.99  
% 3.59/0.99  fof(f9,axiom,(
% 3.59/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f27,plain,(
% 3.59/0.99    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.59/0.99    inference(ennf_transformation,[],[f9])).
% 3.59/0.99  
% 3.59/0.99  fof(f28,plain,(
% 3.59/0.99    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.59/0.99    inference(flattening,[],[f27])).
% 3.59/0.99  
% 3.59/0.99  fof(f70,plain,(
% 3.59/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f28])).
% 3.59/0.99  
% 3.59/0.99  fof(f69,plain,(
% 3.59/0.99    ( ! [X0,X1] : (v2_funct_1(X1) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f28])).
% 3.59/0.99  
% 3.59/0.99  fof(f99,plain,(
% 3.59/0.99    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 3.59/0.99    inference(cnf_transformation,[],[f54])).
% 3.59/0.99  
% 3.59/0.99  fof(f12,axiom,(
% 3.59/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f31,plain,(
% 3.59/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.59/0.99    inference(ennf_transformation,[],[f12])).
% 3.59/0.99  
% 3.59/0.99  fof(f74,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f31])).
% 3.59/0.99  
% 3.59/0.99  fof(f2,axiom,(
% 3.59/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f44,plain,(
% 3.59/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.99    inference(nnf_transformation,[],[f2])).
% 3.59/0.99  
% 3.59/0.99  fof(f45,plain,(
% 3.59/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.99    inference(flattening,[],[f44])).
% 3.59/0.99  
% 3.59/0.99  fof(f56,plain,(
% 3.59/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.59/0.99    inference(cnf_transformation,[],[f45])).
% 3.59/0.99  
% 3.59/0.99  fof(f102,plain,(
% 3.59/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/0.99    inference(equality_resolution,[],[f56])).
% 3.59/0.99  
% 3.59/0.99  fof(f58,plain,(
% 3.59/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f45])).
% 3.59/0.99  
% 3.59/0.99  fof(f1,axiom,(
% 3.59/0.99    v1_xboole_0(k1_xboole_0)),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f55,plain,(
% 3.59/0.99    v1_xboole_0(k1_xboole_0)),
% 3.59/0.99    inference(cnf_transformation,[],[f1])).
% 3.59/0.99  
% 3.59/0.99  fof(f3,axiom,(
% 3.59/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f22,plain,(
% 3.59/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.59/0.99    inference(ennf_transformation,[],[f3])).
% 3.59/0.99  
% 3.59/0.99  fof(f59,plain,(
% 3.59/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f22])).
% 3.59/0.99  
% 3.59/0.99  fof(f85,plain,(
% 3.59/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f51])).
% 3.59/0.99  
% 3.59/0.99  fof(f105,plain,(
% 3.59/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.59/0.99    inference(equality_resolution,[],[f85])).
% 3.59/0.99  
% 3.59/0.99  fof(f92,plain,(
% 3.59/0.99    v1_funct_2(sK4,sK1,sK2)),
% 3.59/0.99    inference(cnf_transformation,[],[f54])).
% 3.59/0.99  
% 3.59/0.99  fof(f8,axiom,(
% 3.59/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f26,plain,(
% 3.59/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.59/0.99    inference(ennf_transformation,[],[f8])).
% 3.59/0.99  
% 3.59/0.99  fof(f50,plain,(
% 3.59/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.59/0.99    inference(nnf_transformation,[],[f26])).
% 3.59/0.99  
% 3.59/0.99  fof(f68,plain,(
% 3.59/0.99    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.59/0.99    inference(cnf_transformation,[],[f50])).
% 3.59/0.99  
% 3.59/0.99  fof(f4,axiom,(
% 3.59/0.99    ! [X0] : ? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.59/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.59/0.99  
% 3.59/0.99  fof(f46,plain,(
% 3.59/0.99    ! [X0] : (? [X1] : (v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0))))),
% 3.59/0.99    introduced(choice_axiom,[])).
% 3.59/0.99  
% 3.59/0.99  fof(f47,plain,(
% 3.59/0.99    ! [X0] : (v1_xboole_0(sK0(X0)) & m1_subset_1(sK0(X0),k1_zfmisc_1(X0)))),
% 3.59/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f4,f46])).
% 3.59/0.99  
% 3.59/0.99  fof(f61,plain,(
% 3.59/0.99    ( ! [X0] : (v1_xboole_0(sK0(X0))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f47])).
% 3.59/0.99  
% 3.59/0.99  fof(f60,plain,(
% 3.59/0.99    ( ! [X0] : (m1_subset_1(sK0(X0),k1_zfmisc_1(X0))) )),
% 3.59/0.99    inference(cnf_transformation,[],[f47])).
% 3.59/0.99  
% 3.59/0.99  cnf(c_31,plain,
% 3.59/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.59/0.99      | k1_xboole_0 = X2 ),
% 3.59/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_41,negated_conjecture,
% 3.59/0.99      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.59/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_668,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.59/0.99      | sK3 != X2
% 3.59/0.99      | sK2 != X1
% 3.59/0.99      | sK5 != X0
% 3.59/0.99      | k1_xboole_0 = X2 ),
% 3.59/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_41]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_669,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.59/0.99      | k1_relset_1(sK2,sK3,sK5) = sK2
% 3.59/0.99      | k1_xboole_0 = sK3 ),
% 3.59/0.99      inference(unflattening,[status(thm)],[c_668]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_40,negated_conjecture,
% 3.59/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.59/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_671,plain,
% 3.59/0.99      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_669,c_40]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1605,plain,
% 3.59/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_22,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k8_relset_1(X1,X2,X0,X2) = k1_relset_1(X1,X2,X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1613,plain,
% 3.59/0.99      ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
% 3.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3598,plain,
% 3.59/0.99      ( k8_relset_1(sK2,sK3,sK5,sK3) = k1_relset_1(sK2,sK3,sK5) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1605,c_1613]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_21,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 3.59/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1614,plain,
% 3.59/0.99      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 3.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3115,plain,
% 3.59/0.99      ( k8_relset_1(sK2,sK3,sK5,X0) = k10_relat_1(sK5,X0) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1605,c_1614]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3607,plain,
% 3.59/0.99      ( k1_relset_1(sK2,sK3,sK5) = k10_relat_1(sK5,sK3) ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_3598,c_3115]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4083,plain,
% 3.59/0.99      ( k10_relat_1(sK5,sK3) = sK2 | sK3 = k1_xboole_0 ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_671,c_3607]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_24,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k8_relset_1(X1,X2,X0,k7_relset_1(X1,X2,X0,X1)) = k1_relset_1(X1,X2,X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1611,plain,
% 3.59/0.99      ( k8_relset_1(X0,X1,X2,k7_relset_1(X0,X1,X2,X0)) = k1_relset_1(X0,X1,X2)
% 3.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4279,plain,
% 3.59/0.99      ( k8_relset_1(sK2,sK3,sK5,k7_relset_1(sK2,sK3,sK5,sK2)) = k1_relset_1(sK2,sK3,sK5) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1605,c_1611]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_23,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1612,plain,
% 3.59/0.99      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 3.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3130,plain,
% 3.59/0.99      ( k7_relset_1(sK2,sK3,sK5,sK2) = k2_relset_1(sK2,sK3,sK5) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1605,c_1612]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_20,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1615,plain,
% 3.59/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2653,plain,
% 3.59/0.99      ( k2_relset_1(sK2,sK3,sK5) = k2_relat_1(sK5) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1605,c_1615]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3136,plain,
% 3.59/0.99      ( k7_relset_1(sK2,sK3,sK5,sK2) = k2_relat_1(sK5) ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_3130,c_2653]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4291,plain,
% 3.59/0.99      ( k8_relset_1(sK2,sK3,sK5,k2_relat_1(sK5)) = k10_relat_1(sK5,sK3) ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_4279,c_3136,c_3607]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5766,plain,
% 3.59/0.99      ( k10_relat_1(sK5,k2_relat_1(sK5)) = k10_relat_1(sK5,sK3) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_3115,c_4291]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_16,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | v1_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1617,plain,
% 3.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.59/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2463,plain,
% 3.59/0.99      ( v1_relat_1(sK5) = iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1605,c_1617]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_11,plain,
% 3.59/0.99      ( ~ v1_relat_1(X0)
% 3.59/0.99      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1622,plain,
% 3.59/0.99      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2533,plain,
% 3.59/0.99      ( k10_relat_1(sK5,k2_relat_1(sK5)) = k1_relat_1(sK5) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_2463,c_1622]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5768,plain,
% 3.59/0.99      ( k10_relat_1(sK5,sK3) = k1_relat_1(sK5) ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_5766,c_2533]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7879,plain,
% 3.59/0.99      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_4083,c_5768]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_42,negated_conjecture,
% 3.59/0.99      ( v1_funct_1(sK5) ),
% 3.59/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1604,plain,
% 3.59/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_33,plain,
% 3.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.59/0.99      | ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1608,plain,
% 3.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3643,plain,
% 3.59/0.99      ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1608,c_1615]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7582,plain,
% 3.59/0.99      ( k2_relset_1(k1_relat_1(sK5),k2_relat_1(sK5),sK5) = k2_relat_1(sK5)
% 3.59/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1604,c_3643]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1933,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.59/0.99      | v1_relat_1(sK5) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1954,plain,
% 3.59/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))))
% 3.59/0.99      | ~ v1_funct_1(sK5)
% 3.59/0.99      | ~ v1_relat_1(sK5) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_33]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2129,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK5),k2_relat_1(sK5))))
% 3.59/0.99      | k2_relset_1(k1_relat_1(sK5),k2_relat_1(sK5),sK5) = k2_relat_1(sK5) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_7649,plain,
% 3.59/0.99      ( k2_relset_1(k1_relat_1(sK5),k2_relat_1(sK5),sK5) = k2_relat_1(sK5) ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_7582,c_42,c_40,c_1933,c_1954,c_2129]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8045,plain,
% 3.59/0.99      ( k2_relset_1(sK2,k2_relat_1(sK5),sK5) = k2_relat_1(sK5)
% 3.59/0.99      | sK3 = k1_xboole_0 ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_7879,c_7649]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_36,negated_conjecture,
% 3.59/0.99      ( ~ v2_funct_1(sK4) | ~ v2_funct_1(sK5) ),
% 3.59/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_43,negated_conjecture,
% 3.59/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.59/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1603,plain,
% 3.59/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_32,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.59/0.99      | ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_funct_1(X3)
% 3.59/0.99      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1609,plain,
% 3.59/0.99      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.59/0.99      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.59/0.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.99      | v1_funct_1(X5) != iProver_top
% 3.59/0.99      | v1_funct_1(X4) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4355,plain,
% 3.59/0.99      ( k1_partfun1(X0,X1,sK2,sK3,X2,sK5) = k5_relat_1(X2,sK5)
% 3.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.99      | v1_funct_1(X2) != iProver_top
% 3.59/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1605,c_1609]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_49,plain,
% 3.59/0.99      ( v1_funct_1(sK5) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4580,plain,
% 3.59/0.99      ( v1_funct_1(X2) != iProver_top
% 3.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.99      | k1_partfun1(X0,X1,sK2,sK3,X2,sK5) = k5_relat_1(X2,sK5) ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_4355,c_49]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4581,plain,
% 3.59/0.99      ( k1_partfun1(X0,X1,sK2,sK3,X2,sK5) = k5_relat_1(X2,sK5)
% 3.59/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.59/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.59/0.99      inference(renaming,[status(thm)],[c_4580]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4591,plain,
% 3.59/0.99      ( k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5)
% 3.59/0.99      | v1_funct_1(sK4) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1603,c_4581]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_45,negated_conjecture,
% 3.59/0.99      ( v1_funct_1(sK4) ),
% 3.59/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2096,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 3.59/0.99      | ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_funct_1(sK5)
% 3.59/0.99      | k1_partfun1(X1,X2,X3,X4,X0,sK5) = k5_relat_1(X0,sK5) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_32]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2401,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.59/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 3.59/0.99      | ~ v1_funct_1(sK4)
% 3.59/0.99      | ~ v1_funct_1(sK5)
% 3.59/0.99      | k1_partfun1(X0,X1,X2,X3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2096]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2615,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.59/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.59/0.99      | ~ v1_funct_1(sK4)
% 3.59/0.99      | ~ v1_funct_1(sK5)
% 3.59/0.99      | k1_partfun1(sK1,sK2,X0,X1,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2401]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2799,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.59/0.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.59/0.99      | ~ v1_funct_1(sK4)
% 3.59/0.99      | ~ v1_funct_1(sK5)
% 3.59/0.99      | k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2615]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4662,plain,
% 3.59/0.99      ( k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5) = k5_relat_1(sK4,sK5) ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_4591,c_45,c_43,c_42,c_40,c_2799]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_39,negated_conjecture,
% 3.59/0.99      ( v2_funct_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) ),
% 3.59/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1606,plain,
% 3.59/0.99      ( v2_funct_1(k1_partfun1(sK1,sK2,sK2,sK3,sK4,sK5)) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4665,plain,
% 3.59/0.99      ( v2_funct_1(k5_relat_1(sK4,sK5)) = iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_4662,c_1606]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4666,plain,
% 3.59/0.99      ( v2_funct_1(k5_relat_1(sK4,sK5)) ),
% 3.59/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4665]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2654,plain,
% 3.59/0.99      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1603,c_1615]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_38,negated_conjecture,
% 3.59/0.99      ( k2_relset_1(sK1,sK2,sK4) = sK2 ),
% 3.59/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2656,plain,
% 3.59/0.99      ( k2_relat_1(sK4) = sK2 ),
% 3.59/0.99      inference(light_normalisation,[status(thm)],[c_2654,c_38]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_14,plain,
% 3.59/0.99      ( ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_funct_1(X1)
% 3.59/0.99      | v2_funct_1(X1)
% 3.59/0.99      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 3.59/0.99      | ~ v1_relat_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X1)
% 3.59/0.99      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 3.59/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1619,plain,
% 3.59/0.99      ( k2_relat_1(X0) != k1_relat_1(X1)
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v1_funct_1(X1) != iProver_top
% 3.59/0.99      | v2_funct_1(X1) = iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top
% 3.59/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4484,plain,
% 3.59/0.99      ( k1_relat_1(X0) != sK2
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v1_funct_1(sK4) != iProver_top
% 3.59/0.99      | v2_funct_1(X0) = iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top
% 3.59/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_2656,c_1619]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_46,plain,
% 3.59/0.99      ( v1_funct_1(sK4) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_48,plain,
% 3.59/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1936,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.59/0.99      | v1_relat_1(sK4) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1937,plain,
% 3.59/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.59/0.99      | v1_relat_1(sK4) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1936]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5399,plain,
% 3.59/0.99      ( v1_relat_1(X0) != iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
% 3.59/0.99      | v2_funct_1(X0) = iProver_top
% 3.59/0.99      | k1_relat_1(X0) != sK2
% 3.59/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_4484,c_46,c_48,c_1937]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5400,plain,
% 3.59/0.99      ( k1_relat_1(X0) != sK2
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v2_funct_1(X0) = iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.99      inference(renaming,[status(thm)],[c_5399]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8040,plain,
% 3.59/0.99      ( sK3 = k1_xboole_0
% 3.59/0.99      | v1_funct_1(sK5) != iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(sK4,sK5)) != iProver_top
% 3.59/0.99      | v2_funct_1(sK5) = iProver_top
% 3.59/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_7879,c_5400]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8117,plain,
% 3.59/0.99      ( ~ v1_funct_1(sK5)
% 3.59/0.99      | ~ v2_funct_1(k5_relat_1(sK4,sK5))
% 3.59/0.99      | v2_funct_1(sK5)
% 3.59/0.99      | ~ v1_relat_1(sK5)
% 3.59/0.99      | sK3 = k1_xboole_0 ),
% 3.59/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_8040]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_15,plain,
% 3.59/0.99      ( ~ v1_funct_1(X0)
% 3.59/0.99      | ~ v1_funct_1(X1)
% 3.59/0.99      | v2_funct_1(X0)
% 3.59/0.99      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 3.59/0.99      | ~ v1_relat_1(X0)
% 3.59/0.99      | ~ v1_relat_1(X1)
% 3.59/0.99      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 3.59/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1618,plain,
% 3.59/0.99      ( k2_relat_1(X0) != k1_relat_1(X1)
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v1_funct_1(X1) != iProver_top
% 3.59/0.99      | v2_funct_1(X0) = iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(X0,X1)) != iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top
% 3.59/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4422,plain,
% 3.59/0.99      ( k1_relat_1(X0) != sK2
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v1_funct_1(sK4) != iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
% 3.59/0.99      | v2_funct_1(sK4) = iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top
% 3.59/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_2656,c_1618]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5281,plain,
% 3.59/0.99      ( v1_relat_1(X0) != iProver_top
% 3.59/0.99      | v2_funct_1(sK4) = iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
% 3.59/0.99      | k1_relat_1(X0) != sK2
% 3.59/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_4422,c_46,c_48,c_1937]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5282,plain,
% 3.59/0.99      ( k1_relat_1(X0) != sK2
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
% 3.59/0.99      | v2_funct_1(sK4) = iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.99      inference(renaming,[status(thm)],[c_5281]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8041,plain,
% 3.59/0.99      ( sK3 = k1_xboole_0
% 3.59/0.99      | v1_funct_1(sK5) != iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(sK4,sK5)) != iProver_top
% 3.59/0.99      | v2_funct_1(sK4) = iProver_top
% 3.59/0.99      | v1_relat_1(sK5) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_7879,c_5282]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8118,plain,
% 3.59/0.99      ( ~ v1_funct_1(sK5)
% 3.59/0.99      | ~ v2_funct_1(k5_relat_1(sK4,sK5))
% 3.59/0.99      | v2_funct_1(sK4)
% 3.59/0.99      | ~ v1_relat_1(sK5)
% 3.59/0.99      | sK3 = k1_xboole_0 ),
% 3.59/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_8041]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8122,plain,
% 3.59/0.99      ( sK3 = k1_xboole_0 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_8045,c_42,c_40,c_36,c_1933,c_4666,c_8117,c_8118]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_37,negated_conjecture,
% 3.59/0.99      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 3.59/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8145,plain,
% 3.59/0.99      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_8122,c_37]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8146,plain,
% 3.59/0.99      ( sK2 = k1_xboole_0 ),
% 3.59/0.99      inference(equality_resolution_simp,[status(thm)],[c_8145]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_19,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.59/0.99      | ~ v1_xboole_0(X1)
% 3.59/0.99      | v1_xboole_0(X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1616,plain,
% 3.59/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.59/0.99      | v1_xboole_0(X1) != iProver_top
% 3.59/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3614,plain,
% 3.59/0.99      ( v1_xboole_0(sK2) != iProver_top
% 3.59/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1605,c_1616]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8356,plain,
% 3.59/0.99      ( v1_xboole_0(sK5) = iProver_top
% 3.59/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_8146,c_3614]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_51,plain,
% 3.59/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3,plain,
% 3.59/0.99      ( r1_tarski(X0,X0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_145,plain,
% 3.59/0.99      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1,plain,
% 3.59/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.59/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_149,plain,
% 3.59/0.99      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.59/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_0,plain,
% 3.59/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.59/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_151,plain,
% 3.59/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_974,plain,
% 3.59/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.59/0.99      theory(equality) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2416,plain,
% 3.59/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_974]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2417,plain,
% 3.59/0.99      ( sK2 != X0
% 3.59/0.99      | v1_xboole_0(X0) != iProver_top
% 3.59/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_2416]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2419,plain,
% 3.59/0.99      ( sK2 != k1_xboole_0
% 3.59/0.99      | v1_xboole_0(sK2) = iProver_top
% 3.59/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2417]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_973,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1992,plain,
% 3.59/0.99      ( sK2 != X0 | sK2 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_973]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2564,plain,
% 3.59/0.99      ( sK2 != sK2 | sK2 = k1_xboole_0 | k1_xboole_0 != sK2 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1992]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_972,plain,( X0 = X0 ),theory(equality) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2565,plain,
% 3.59/0.99      ( sK2 = sK2 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_972]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3054,plain,
% 3.59/0.99      ( sK3 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK3 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_973]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3055,plain,
% 3.59/0.99      ( sK3 != k1_xboole_0
% 3.59/0.99      | k1_xboole_0 = sK3
% 3.59/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_3054]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2765,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.59/0.99      | ~ v1_xboole_0(X0)
% 3.59/0.99      | v1_xboole_0(sK5) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3294,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.59/0.99      | ~ v1_xboole_0(sK2)
% 3.59/0.99      | v1_xboole_0(sK5) ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2765]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3295,plain,
% 3.59/0.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.59/0.99      | v1_xboole_0(sK2) != iProver_top
% 3.59/0.99      | v1_xboole_0(sK5) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_3294]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_9339,plain,
% 3.59/0.99      ( v1_xboole_0(sK5) = iProver_top ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_8356,c_42,c_40,c_51,c_37,c_36,c_145,c_149,c_151,
% 3.59/0.99                 c_1933,c_2419,c_2564,c_2565,c_3055,c_3295,c_4666,c_8117,
% 3.59/0.99                 c_8118]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1628,plain,
% 3.59/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_4,plain,
% 3.59/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 3.59/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1625,plain,
% 3.59/0.99      ( X0 = X1
% 3.59/0.99      | v1_xboole_0(X1) != iProver_top
% 3.59/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2587,plain,
% 3.59/0.99      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1628,c_1625]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_9345,plain,
% 3.59/0.99      ( sK5 = k1_xboole_0 ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_9339,c_2587]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_27,plain,
% 3.59/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.59/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.59/0.99      | k1_xboole_0 = X1
% 3.59/0.99      | k1_xboole_0 = X0 ),
% 3.59/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_44,negated_conjecture,
% 3.59/0.99      ( v1_funct_2(sK4,sK1,sK2) ),
% 3.59/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_575,plain,
% 3.59/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.59/0.99      | sK1 != X1
% 3.59/0.99      | sK2 != k1_xboole_0
% 3.59/0.99      | sK4 != X0
% 3.59/0.99      | k1_xboole_0 = X0
% 3.59/0.99      | k1_xboole_0 = X1 ),
% 3.59/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_44]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_576,plain,
% 3.59/0.99      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
% 3.59/0.99      | sK2 != k1_xboole_0
% 3.59/0.99      | k1_xboole_0 = sK1
% 3.59/0.99      | k1_xboole_0 = sK4 ),
% 3.59/0.99      inference(unflattening,[status(thm)],[c_575]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1597,plain,
% 3.59/0.99      ( sK2 != k1_xboole_0
% 3.59/0.99      | k1_xboole_0 = sK1
% 3.59/0.99      | k1_xboole_0 = sK4
% 3.59/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8362,plain,
% 3.59/0.99      ( sK1 = k1_xboole_0
% 3.59/0.99      | sK4 = k1_xboole_0
% 3.59/0.99      | k1_xboole_0 != k1_xboole_0
% 3.59/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_8146,c_1597]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8377,plain,
% 3.59/0.99      ( sK1 = k1_xboole_0
% 3.59/0.99      | sK4 = k1_xboole_0
% 3.59/0.99      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) != iProver_top ),
% 3.59/0.99      inference(equality_resolution_simp,[status(thm)],[c_8362]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8365,plain,
% 3.59/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) = iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_8146,c_1603]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8381,plain,
% 3.59/0.99      ( sK1 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.59/0.99      inference(forward_subsumption_resolution,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_8377,c_8365]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_12,plain,
% 3.59/0.99      ( ~ v1_relat_1(X0)
% 3.59/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.59/0.99      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.59/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1621,plain,
% 3.59/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.59/0.99      | k1_relat_1(X0) = k1_xboole_0
% 3.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2696,plain,
% 3.59/0.99      ( k1_relat_1(sK4) = k1_xboole_0
% 3.59/0.99      | sK2 != k1_xboole_0
% 3.59/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_2656,c_1621]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2702,plain,
% 3.59/0.99      ( ~ v1_xboole_0(X0)
% 3.59/0.99      | v1_xboole_0(k1_relat_1(sK4))
% 3.59/0.99      | k1_relat_1(sK4) != X0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_974]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2704,plain,
% 3.59/0.99      ( v1_xboole_0(k1_relat_1(sK4))
% 3.59/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.59/0.99      | k1_relat_1(sK4) != k1_xboole_0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2702]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2937,plain,
% 3.59/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK4) | sK4 = X0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2939,plain,
% 3.59/0.99      ( ~ v1_xboole_0(sK4)
% 3.59/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.59/0.99      | sK4 = k1_xboole_0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2937]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3639,plain,
% 3.59/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2))) = iProver_top
% 3.59/0.99      | v1_funct_1(sK4) != iProver_top
% 3.59/0.99      | v1_relat_1(sK4) != iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_2656,c_1608]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3932,plain,
% 3.59/0.99      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),sK2))) = iProver_top ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_3639,c_46,c_48,c_1937]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3942,plain,
% 3.59/0.99      ( v1_xboole_0(k1_relat_1(sK4)) != iProver_top
% 3.59/0.99      | v1_xboole_0(sK4) = iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_3932,c_1616]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3965,plain,
% 3.59/0.99      ( ~ v1_xboole_0(k1_relat_1(sK4)) | v1_xboole_0(sK4) ),
% 3.59/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3942]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_11913,plain,
% 3.59/0.99      ( sK4 = k1_xboole_0 ),
% 3.59/0.99      inference(global_propositional_subsumption,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_8381,c_48,c_42,c_40,c_37,c_36,c_145,c_149,c_0,c_1933,
% 3.59/0.99                 c_1937,c_2564,c_2565,c_2696,c_2704,c_2939,c_3055,c_3965,
% 3.59/0.99                 c_4666,c_8117,c_8118]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1607,plain,
% 3.59/0.99      ( v2_funct_1(sK4) != iProver_top | v2_funct_1(sK5) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_11948,plain,
% 3.59/0.99      ( v2_funct_1(sK5) != iProver_top
% 3.59/0.99      | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_11913,c_1607]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_13160,plain,
% 3.59/0.99      ( v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_9345,c_11948]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_11944,plain,
% 3.59/0.99      ( v2_funct_1(k5_relat_1(k1_xboole_0,sK5)) = iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_11913,c_4665]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_13157,plain,
% 3.59/0.99      ( v2_funct_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_9345,c_11944]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8361,plain,
% 3.59/0.99      ( k2_relat_1(sK4) = k1_xboole_0 ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_8146,c_2656]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_11939,plain,
% 3.59/0.99      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_11913,c_8361]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_8347,plain,
% 3.59/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(sK4,X0)) != iProver_top
% 3.59/0.99      | v2_funct_1(sK4) = iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_8146,c_5282]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_11916,plain,
% 3.59/0.99      ( k1_relat_1(X0) != k1_xboole_0
% 3.59/0.99      | v1_funct_1(X0) != iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(k1_xboole_0,X0)) != iProver_top
% 3.59/0.99      | v2_funct_1(k1_xboole_0) = iProver_top
% 3.59/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_11913,c_8347]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_12030,plain,
% 3.59/0.99      ( k1_relat_1(k1_xboole_0) != k1_xboole_0
% 3.59/0.99      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.59/0.99      | v2_funct_1(k5_relat_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.59/0.99      | v2_funct_1(k1_xboole_0) = iProver_top
% 3.59/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_11916]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_5,plain,
% 3.59/0.99      ( v1_xboole_0(sK0(X0)) ),
% 3.59/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1624,plain,
% 3.59/0.99      ( v1_xboole_0(sK0(X0)) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3290,plain,
% 3.59/0.99      ( sK0(X0) = k1_xboole_0 ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1624,c_2587]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_6,plain,
% 3.59/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) ),
% 3.59/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1623,plain,
% 3.59/0.99      ( m1_subset_1(sK0(X0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2462,plain,
% 3.59/0.99      ( v1_relat_1(sK0(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.59/0.99      inference(superposition,[status(thm)],[c_1623,c_1617]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3509,plain,
% 3.59/0.99      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.59/0.99      inference(demodulation,[status(thm)],[c_3290,c_2462]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_3517,plain,
% 3.59/0.99      ( v1_relat_1(k1_xboole_0) ),
% 3.59/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3509]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2418,plain,
% 3.59/0.99      ( v1_xboole_0(sK2)
% 3.59/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.59/0.99      | sK2 != k1_xboole_0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2416]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2257,plain,
% 3.59/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK5) | X0 = sK5 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_2259,plain,
% 3.59/0.99      ( ~ v1_xboole_0(sK5)
% 3.59/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 3.59/0.99      | k1_xboole_0 = sK5 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_2257]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_980,plain,
% 3.59/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.59/0.99      theory(equality) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1944,plain,
% 3.59/0.99      ( v1_funct_1(X0) | ~ v1_funct_1(sK5) | X0 != sK5 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_980]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1945,plain,
% 3.59/0.99      ( X0 != sK5
% 3.59/0.99      | v1_funct_1(X0) = iProver_top
% 3.59/0.99      | v1_funct_1(sK5) != iProver_top ),
% 3.59/0.99      inference(predicate_to_equality,[status(thm)],[c_1944]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_1947,plain,
% 3.59/0.99      ( k1_xboole_0 != sK5
% 3.59/0.99      | v1_funct_1(sK5) != iProver_top
% 3.59/0.99      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_1945]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(c_118,plain,
% 3.59/0.99      ( ~ v1_relat_1(k1_xboole_0)
% 3.59/0.99      | k2_relat_1(k1_xboole_0) != k1_xboole_0
% 3.59/0.99      | k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.59/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.59/0.99  
% 3.59/0.99  cnf(contradiction,plain,
% 3.59/0.99      ( $false ),
% 3.59/0.99      inference(minisat,
% 3.59/0.99                [status(thm)],
% 3.59/0.99                [c_13160,c_13157,c_11939,c_12030,c_8122,c_3517,c_3509,
% 3.59/0.99                 c_3294,c_3055,c_2565,c_2564,c_2418,c_2259,c_1947,c_0,
% 3.59/0.99                 c_149,c_145,c_118,c_37,c_40,c_49]) ).
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.59/0.99  
% 3.59/0.99  ------                               Statistics
% 3.59/0.99  
% 3.59/0.99  ------ General
% 3.59/0.99  
% 3.59/0.99  abstr_ref_over_cycles:                  0
% 3.59/0.99  abstr_ref_under_cycles:                 0
% 3.59/0.99  gc_basic_clause_elim:                   0
% 3.59/0.99  forced_gc_time:                         0
% 3.59/0.99  parsing_time:                           0.008
% 3.59/0.99  unif_index_cands_time:                  0.
% 3.59/0.99  unif_index_add_time:                    0.
% 3.59/0.99  orderings_time:                         0.
% 3.59/0.99  out_proof_time:                         0.017
% 3.59/0.99  total_time:                             0.318
% 3.59/0.99  num_of_symbols:                         58
% 3.59/0.99  num_of_terms:                           9919
% 3.59/0.99  
% 3.59/0.99  ------ Preprocessing
% 3.59/0.99  
% 3.59/0.99  num_of_splits:                          0
% 3.59/0.99  num_of_split_atoms:                     0
% 3.59/0.99  num_of_reused_defs:                     0
% 3.59/0.99  num_eq_ax_congr_red:                    48
% 3.59/0.99  num_of_sem_filtered_clauses:            1
% 3.59/0.99  num_of_subtypes:                        0
% 3.59/0.99  monotx_restored_types:                  0
% 3.59/0.99  sat_num_of_epr_types:                   0
% 3.59/0.99  sat_num_of_non_cyclic_types:            0
% 3.59/0.99  sat_guarded_non_collapsed_types:        0
% 3.59/0.99  num_pure_diseq_elim:                    0
% 3.59/0.99  simp_replaced_by:                       0
% 3.59/0.99  res_preprocessed:                       195
% 3.59/0.99  prep_upred:                             0
% 3.59/0.99  prep_unflattend:                        41
% 3.59/0.99  smt_new_axioms:                         0
% 3.59/0.99  pred_elim_cands:                        6
% 3.59/0.99  pred_elim:                              3
% 3.59/0.99  pred_elim_cl:                           4
% 3.59/0.99  pred_elim_cycles:                       5
% 3.59/0.99  merged_defs:                            0
% 3.59/0.99  merged_defs_ncl:                        0
% 3.59/0.99  bin_hyper_res:                          0
% 3.59/0.99  prep_cycles:                            4
% 3.59/0.99  pred_elim_time:                         0.005
% 3.59/0.99  splitting_time:                         0.
% 3.59/0.99  sem_filter_time:                        0.
% 3.59/0.99  monotx_time:                            0.
% 3.59/0.99  subtype_inf_time:                       0.
% 3.59/0.99  
% 3.59/0.99  ------ Problem properties
% 3.59/0.99  
% 3.59/0.99  clauses:                                40
% 3.59/0.99  conjectures:                            8
% 3.59/0.99  epr:                                    8
% 3.59/0.99  horn:                                   34
% 3.59/0.99  ground:                                 15
% 3.59/0.99  unary:                                  10
% 3.59/0.99  binary:                                 14
% 3.59/0.99  lits:                                   102
% 3.59/0.99  lits_eq:                                40
% 3.59/0.99  fd_pure:                                0
% 3.59/0.99  fd_pseudo:                              0
% 3.59/0.99  fd_cond:                                1
% 3.59/0.99  fd_pseudo_cond:                         2
% 3.59/0.99  ac_symbols:                             0
% 3.59/0.99  
% 3.59/0.99  ------ Propositional Solver
% 3.59/0.99  
% 3.59/0.99  prop_solver_calls:                      28
% 3.59/0.99  prop_fast_solver_calls:                 1637
% 3.59/0.99  smt_solver_calls:                       0
% 3.59/0.99  smt_fast_solver_calls:                  0
% 3.59/0.99  prop_num_of_clauses:                    4612
% 3.59/0.99  prop_preprocess_simplified:             11361
% 3.59/0.99  prop_fo_subsumed:                       76
% 3.59/0.99  prop_solver_time:                       0.
% 3.59/0.99  smt_solver_time:                        0.
% 3.59/0.99  smt_fast_solver_time:                   0.
% 3.59/0.99  prop_fast_solver_time:                  0.
% 3.59/0.99  prop_unsat_core_time:                   0.
% 3.59/0.99  
% 3.59/0.99  ------ QBF
% 3.59/0.99  
% 3.59/0.99  qbf_q_res:                              0
% 3.59/0.99  qbf_num_tautologies:                    0
% 3.59/0.99  qbf_prep_cycles:                        0
% 3.59/0.99  
% 3.59/0.99  ------ BMC1
% 3.59/0.99  
% 3.59/0.99  bmc1_current_bound:                     -1
% 3.59/0.99  bmc1_last_solved_bound:                 -1
% 3.59/0.99  bmc1_unsat_core_size:                   -1
% 3.59/0.99  bmc1_unsat_core_parents_size:           -1
% 3.59/0.99  bmc1_merge_next_fun:                    0
% 3.59/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.59/0.99  
% 3.59/0.99  ------ Instantiation
% 3.59/0.99  
% 3.59/0.99  inst_num_of_clauses:                    1567
% 3.59/0.99  inst_num_in_passive:                    97
% 3.59/0.99  inst_num_in_active:                     854
% 3.59/0.99  inst_num_in_unprocessed:                616
% 3.59/0.99  inst_num_of_loops:                      960
% 3.59/0.99  inst_num_of_learning_restarts:          0
% 3.59/0.99  inst_num_moves_active_passive:          103
% 3.59/0.99  inst_lit_activity:                      0
% 3.59/0.99  inst_lit_activity_moves:                0
% 3.59/0.99  inst_num_tautologies:                   0
% 3.59/0.99  inst_num_prop_implied:                  0
% 3.59/0.99  inst_num_existing_simplified:           0
% 3.59/0.99  inst_num_eq_res_simplified:             0
% 3.59/0.99  inst_num_child_elim:                    0
% 3.59/0.99  inst_num_of_dismatching_blockings:      765
% 3.59/0.99  inst_num_of_non_proper_insts:           1727
% 3.59/0.99  inst_num_of_duplicates:                 0
% 3.59/0.99  inst_inst_num_from_inst_to_res:         0
% 3.59/0.99  inst_dismatching_checking_time:         0.
% 3.59/0.99  
% 3.59/0.99  ------ Resolution
% 3.59/0.99  
% 3.59/0.99  res_num_of_clauses:                     0
% 3.59/0.99  res_num_in_passive:                     0
% 3.59/0.99  res_num_in_active:                      0
% 3.59/0.99  res_num_of_loops:                       199
% 3.59/0.99  res_forward_subset_subsumed:            104
% 3.59/0.99  res_backward_subset_subsumed:           2
% 3.59/0.99  res_forward_subsumed:                   0
% 3.59/0.99  res_backward_subsumed:                  0
% 3.59/0.99  res_forward_subsumption_resolution:     2
% 3.59/0.99  res_backward_subsumption_resolution:    0
% 3.59/0.99  res_clause_to_clause_subsumption:       461
% 3.59/0.99  res_orphan_elimination:                 0
% 3.59/0.99  res_tautology_del:                      212
% 3.59/0.99  res_num_eq_res_simplified:              0
% 3.59/0.99  res_num_sel_changes:                    0
% 3.59/0.99  res_moves_from_active_to_pass:          0
% 3.59/0.99  
% 3.59/0.99  ------ Superposition
% 3.59/0.99  
% 3.59/0.99  sup_time_total:                         0.
% 3.59/0.99  sup_time_generating:                    0.
% 3.59/0.99  sup_time_sim_full:                      0.
% 3.59/0.99  sup_time_sim_immed:                     0.
% 3.59/0.99  
% 3.59/0.99  sup_num_of_clauses:                     114
% 3.59/0.99  sup_num_in_active:                      49
% 3.59/0.99  sup_num_in_passive:                     65
% 3.59/0.99  sup_num_of_loops:                       190
% 3.59/0.99  sup_fw_superposition:                   159
% 3.59/0.99  sup_bw_superposition:                   102
% 3.59/0.99  sup_immediate_simplified:               163
% 3.59/0.99  sup_given_eliminated:                   1
% 3.59/0.99  comparisons_done:                       0
% 3.59/0.99  comparisons_avoided:                    17
% 3.59/0.99  
% 3.59/0.99  ------ Simplifications
% 3.59/0.99  
% 3.59/0.99  
% 3.59/0.99  sim_fw_subset_subsumed:                 42
% 3.59/0.99  sim_bw_subset_subsumed:                 6
% 3.59/0.99  sim_fw_subsumed:                        30
% 3.59/0.99  sim_bw_subsumed:                        2
% 3.59/0.99  sim_fw_subsumption_res:                 2
% 3.59/0.99  sim_bw_subsumption_res:                 1
% 3.59/0.99  sim_tautology_del:                      2
% 3.59/0.99  sim_eq_tautology_del:                   28
% 3.59/0.99  sim_eq_res_simp:                        5
% 3.59/0.99  sim_fw_demodulated:                     32
% 3.59/0.99  sim_bw_demodulated:                     140
% 3.59/0.99  sim_light_normalised:                   98
% 3.59/0.99  sim_joinable_taut:                      0
% 3.59/0.99  sim_joinable_simp:                      0
% 3.59/0.99  sim_ac_normalised:                      0
% 3.59/0.99  sim_smt_subsumption:                    0
% 3.59/0.99  
%------------------------------------------------------------------------------
