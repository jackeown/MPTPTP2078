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
% DateTime   : Thu Dec  3 12:01:44 EST 2020

% Result     : Theorem 15.49s
% Output     : CNFRefutation 15.49s
% Verified   : 
% Statistics : Number of formulae       :  206 ( 928 expanded)
%              Number of clauses        :  127 ( 346 expanded)
%              Number of leaves         :   22 ( 208 expanded)
%              Depth                    :   18
%              Number of atoms          :  590 (5260 expanded)
%              Number of equality atoms :  272 (1728 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

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
    inference(ennf_transformation,[],[f22])).

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

fof(f90,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f93,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

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

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f92,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f96,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f57])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f95,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f91,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f76,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f45])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f94,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(k9_relat_1(X2,X0),X1)
          & r1_tarski(X0,k1_relat_1(X2)) )
       => r1_tarski(X0,k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k10_relat_1(X2,X1))
      | ~ r1_tarski(k9_relat_1(X2,X0),X1)
      | ~ r1_tarski(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f98,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f60,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f97,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1714,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1721,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2606,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1714,c_1721])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1725,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3249,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2606,c_1725])).

cnf(c_42,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3744,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3249,c_42])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1730,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3748,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_3744,c_1730])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1716,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1722,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2707,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1716,c_1722])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_662,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_35])).

cnf(c_663,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_662])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_665,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_663,c_34,c_31])).

cnf(c_2709,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_2707,c_665])).

cnf(c_11,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_494,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK4 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_32])).

cnf(c_495,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_494])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_499,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_495,c_36])).

cnf(c_1710,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_2829,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2709,c_1710])).

cnf(c_2105,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1730])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_287,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_288,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_287])).

cnf(c_353,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_288])).

cnf(c_2139,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_353])).

cnf(c_2824,plain,
    ( ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_2825,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2824])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2949,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2950,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2949])).

cnf(c_5828,plain,
    ( r1_tarski(X0,sK1) != iProver_top
    | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2829,c_2105,c_2825,c_2950])).

cnf(c_5829,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5828])).

cnf(c_5835,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3748,c_5829])).

cnf(c_2106,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_1730])).

cnf(c_1712,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_353])).

cnf(c_13662,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_2106,c_1712])).

cnf(c_2834,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2139])).

cnf(c_2835,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2834])).

cnf(c_2952,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_2953,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2952])).

cnf(c_14302,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13662,c_2106,c_2835,c_2953])).

cnf(c_13661,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2105,c_1712])).

cnf(c_14148,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13661,c_2105,c_2825,c_2950])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1727,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_14152,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_14148,c_1727])).

cnf(c_15102,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_14302,c_14152])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1720,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4044,plain,
    ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1720])).

cnf(c_4324,plain,
    ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_1714,c_4044])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1724,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_4668,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4324,c_1724])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_8421,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4668,c_42,c_45])).

cnf(c_8432,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_8421,c_1721])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1718,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_5040,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1718])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5253,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5040,c_43])).

cnf(c_5254,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5253])).

cnf(c_5265,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1714,c_5254])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_40,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_5393,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5265,c_40])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_5395,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5393,c_33])).

cnf(c_8436,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_8432,c_5395])).

cnf(c_15103,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_15102,c_8436])).

cnf(c_47201,plain,
    ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_5835,c_5835,c_15103])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_9,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_476,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_12,c_9])).

cnf(c_1711,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_5015,plain,
    ( k7_relat_1(sK4,sK1) = sK4
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1716,c_1711])).

cnf(c_5196,plain,
    ( k7_relat_1(sK4,sK1) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5015,c_2105,c_2825,c_2950])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1728,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_14153,plain,
    ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
    inference(superposition,[status(thm)],[c_14148,c_1728])).

cnf(c_14834,plain,
    ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_5196,c_14153])).

cnf(c_10,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2))
    | ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ r1_tarski(k9_relat_1(X1,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1726,plain,
    ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
    | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
    | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_15224,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK1,k10_relat_1(sK4,X0)) = iProver_top
    | r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_14834,c_1726])).

cnf(c_15225,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK1,k10_relat_1(sK4,X0)) = iProver_top
    | r1_tarski(sK1,sK1) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_15224,c_2709])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_2004,plain,
    ( r1_tarski(sK1,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2005,plain,
    ( r1_tarski(sK1,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2004])).

cnf(c_15478,plain,
    ( r1_tarski(sK1,k10_relat_1(sK4,X0)) = iProver_top
    | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_15225,c_43,c_2005,c_2105,c_2825,c_2950])).

cnf(c_15479,plain,
    ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
    | r1_tarski(sK1,k10_relat_1(sK4,X0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_15478])).

cnf(c_47205,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) != iProver_top
    | r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_47201,c_15479])).

cnf(c_2605,plain,
    ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1716,c_1721])).

cnf(c_3251,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2605,c_1725])).

cnf(c_3952,plain,
    ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3251,c_45])).

cnf(c_3956,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3952,c_1730])).

cnf(c_1004,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1990,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3))
    | k2_relset_1(sK0,sK1,sK3) != X1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1004])).

cnf(c_2189,plain,
    ( ~ r1_tarski(sK1,X0)
    | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3))
    | k2_relset_1(sK0,sK1,sK3) != X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1990])).

cnf(c_3167,plain,
    ( r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3))
    | ~ r1_tarski(sK1,k2_relat_1(sK3))
    | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_3168,plain,
    ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | sK1 != sK1
    | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3)) = iProver_top
    | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3167])).

cnf(c_1002,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1998,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_1002])).

cnf(c_1865,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1866,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1865])).

cnf(c_1807,plain,
    ( ~ m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1808,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top
    | r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1807])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1774,plain,
    ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1)
    | ~ r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3))
    | k2_relset_1(sK0,sK1,sK3) = sK1 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1775,plain,
    ( k2_relset_1(sK0,sK1,sK3) = sK1
    | r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1) != iProver_top
    | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1774])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f97])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_47205,c_3956,c_3168,c_2606,c_1998,c_1866,c_1808,c_1775,c_30,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:44:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 15.49/2.52  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 15.49/2.52  
% 15.49/2.52  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.49/2.52  
% 15.49/2.52  ------  iProver source info
% 15.49/2.52  
% 15.49/2.52  git: date: 2020-06-30 10:37:57 +0100
% 15.49/2.52  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.49/2.52  git: non_committed_changes: false
% 15.49/2.52  git: last_make_outside_of_git: false
% 15.49/2.52  
% 15.49/2.52  ------ 
% 15.49/2.52  
% 15.49/2.52  ------ Input Options
% 15.49/2.52  
% 15.49/2.52  --out_options                           all
% 15.49/2.52  --tptp_safe_out                         true
% 15.49/2.52  --problem_path                          ""
% 15.49/2.52  --include_path                          ""
% 15.49/2.52  --clausifier                            res/vclausify_rel
% 15.49/2.52  --clausifier_options                    ""
% 15.49/2.52  --stdin                                 false
% 15.49/2.52  --stats_out                             all
% 15.49/2.52  
% 15.49/2.52  ------ General Options
% 15.49/2.52  
% 15.49/2.52  --fof                                   false
% 15.49/2.52  --time_out_real                         305.
% 15.49/2.52  --time_out_virtual                      -1.
% 15.49/2.52  --symbol_type_check                     false
% 15.49/2.52  --clausify_out                          false
% 15.49/2.52  --sig_cnt_out                           false
% 15.49/2.52  --trig_cnt_out                          false
% 15.49/2.52  --trig_cnt_out_tolerance                1.
% 15.49/2.52  --trig_cnt_out_sk_spl                   false
% 15.49/2.52  --abstr_cl_out                          false
% 15.49/2.52  
% 15.49/2.52  ------ Global Options
% 15.49/2.52  
% 15.49/2.52  --schedule                              default
% 15.49/2.52  --add_important_lit                     false
% 15.49/2.52  --prop_solver_per_cl                    1000
% 15.49/2.52  --min_unsat_core                        false
% 15.49/2.52  --soft_assumptions                      false
% 15.49/2.52  --soft_lemma_size                       3
% 15.49/2.52  --prop_impl_unit_size                   0
% 15.49/2.52  --prop_impl_unit                        []
% 15.49/2.52  --share_sel_clauses                     true
% 15.49/2.52  --reset_solvers                         false
% 15.49/2.52  --bc_imp_inh                            [conj_cone]
% 15.49/2.52  --conj_cone_tolerance                   3.
% 15.49/2.52  --extra_neg_conj                        none
% 15.49/2.52  --large_theory_mode                     true
% 15.49/2.52  --prolific_symb_bound                   200
% 15.49/2.52  --lt_threshold                          2000
% 15.49/2.52  --clause_weak_htbl                      true
% 15.49/2.52  --gc_record_bc_elim                     false
% 15.49/2.52  
% 15.49/2.52  ------ Preprocessing Options
% 15.49/2.52  
% 15.49/2.52  --preprocessing_flag                    true
% 15.49/2.52  --time_out_prep_mult                    0.1
% 15.49/2.52  --splitting_mode                        input
% 15.49/2.52  --splitting_grd                         true
% 15.49/2.52  --splitting_cvd                         false
% 15.49/2.52  --splitting_cvd_svl                     false
% 15.49/2.52  --splitting_nvd                         32
% 15.49/2.52  --sub_typing                            true
% 15.49/2.52  --prep_gs_sim                           true
% 15.49/2.52  --prep_unflatten                        true
% 15.49/2.52  --prep_res_sim                          true
% 15.49/2.52  --prep_upred                            true
% 15.49/2.52  --prep_sem_filter                       exhaustive
% 15.49/2.52  --prep_sem_filter_out                   false
% 15.49/2.52  --pred_elim                             true
% 15.49/2.52  --res_sim_input                         true
% 15.49/2.52  --eq_ax_congr_red                       true
% 15.49/2.52  --pure_diseq_elim                       true
% 15.49/2.52  --brand_transform                       false
% 15.49/2.52  --non_eq_to_eq                          false
% 15.49/2.52  --prep_def_merge                        true
% 15.49/2.52  --prep_def_merge_prop_impl              false
% 15.49/2.52  --prep_def_merge_mbd                    true
% 15.49/2.52  --prep_def_merge_tr_red                 false
% 15.49/2.52  --prep_def_merge_tr_cl                  false
% 15.49/2.52  --smt_preprocessing                     true
% 15.49/2.52  --smt_ac_axioms                         fast
% 15.49/2.52  --preprocessed_out                      false
% 15.49/2.52  --preprocessed_stats                    false
% 15.49/2.52  
% 15.49/2.52  ------ Abstraction refinement Options
% 15.49/2.52  
% 15.49/2.52  --abstr_ref                             []
% 15.49/2.52  --abstr_ref_prep                        false
% 15.49/2.52  --abstr_ref_until_sat                   false
% 15.49/2.52  --abstr_ref_sig_restrict                funpre
% 15.49/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.49/2.52  --abstr_ref_under                       []
% 15.49/2.52  
% 15.49/2.52  ------ SAT Options
% 15.49/2.52  
% 15.49/2.52  --sat_mode                              false
% 15.49/2.52  --sat_fm_restart_options                ""
% 15.49/2.52  --sat_gr_def                            false
% 15.49/2.52  --sat_epr_types                         true
% 15.49/2.52  --sat_non_cyclic_types                  false
% 15.49/2.52  --sat_finite_models                     false
% 15.49/2.52  --sat_fm_lemmas                         false
% 15.49/2.52  --sat_fm_prep                           false
% 15.49/2.52  --sat_fm_uc_incr                        true
% 15.49/2.52  --sat_out_model                         small
% 15.49/2.52  --sat_out_clauses                       false
% 15.49/2.52  
% 15.49/2.52  ------ QBF Options
% 15.49/2.52  
% 15.49/2.52  --qbf_mode                              false
% 15.49/2.52  --qbf_elim_univ                         false
% 15.49/2.52  --qbf_dom_inst                          none
% 15.49/2.52  --qbf_dom_pre_inst                      false
% 15.49/2.52  --qbf_sk_in                             false
% 15.49/2.52  --qbf_pred_elim                         true
% 15.49/2.52  --qbf_split                             512
% 15.49/2.52  
% 15.49/2.52  ------ BMC1 Options
% 15.49/2.52  
% 15.49/2.52  --bmc1_incremental                      false
% 15.49/2.52  --bmc1_axioms                           reachable_all
% 15.49/2.52  --bmc1_min_bound                        0
% 15.49/2.52  --bmc1_max_bound                        -1
% 15.49/2.52  --bmc1_max_bound_default                -1
% 15.49/2.52  --bmc1_symbol_reachability              true
% 15.49/2.52  --bmc1_property_lemmas                  false
% 15.49/2.52  --bmc1_k_induction                      false
% 15.49/2.52  --bmc1_non_equiv_states                 false
% 15.49/2.52  --bmc1_deadlock                         false
% 15.49/2.52  --bmc1_ucm                              false
% 15.49/2.52  --bmc1_add_unsat_core                   none
% 15.49/2.52  --bmc1_unsat_core_children              false
% 15.49/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.49/2.52  --bmc1_out_stat                         full
% 15.49/2.52  --bmc1_ground_init                      false
% 15.49/2.52  --bmc1_pre_inst_next_state              false
% 15.49/2.52  --bmc1_pre_inst_state                   false
% 15.49/2.52  --bmc1_pre_inst_reach_state             false
% 15.49/2.52  --bmc1_out_unsat_core                   false
% 15.49/2.52  --bmc1_aig_witness_out                  false
% 15.49/2.52  --bmc1_verbose                          false
% 15.49/2.52  --bmc1_dump_clauses_tptp                false
% 15.49/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.49/2.52  --bmc1_dump_file                        -
% 15.49/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.49/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.49/2.52  --bmc1_ucm_extend_mode                  1
% 15.49/2.52  --bmc1_ucm_init_mode                    2
% 15.49/2.52  --bmc1_ucm_cone_mode                    none
% 15.49/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.49/2.52  --bmc1_ucm_relax_model                  4
% 15.49/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.49/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.49/2.52  --bmc1_ucm_layered_model                none
% 15.49/2.52  --bmc1_ucm_max_lemma_size               10
% 15.49/2.52  
% 15.49/2.52  ------ AIG Options
% 15.49/2.52  
% 15.49/2.52  --aig_mode                              false
% 15.49/2.52  
% 15.49/2.52  ------ Instantiation Options
% 15.49/2.52  
% 15.49/2.52  --instantiation_flag                    true
% 15.49/2.52  --inst_sos_flag                         true
% 15.49/2.52  --inst_sos_phase                        true
% 15.49/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.49/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.49/2.52  --inst_lit_sel_side                     num_symb
% 15.49/2.52  --inst_solver_per_active                1400
% 15.49/2.52  --inst_solver_calls_frac                1.
% 15.49/2.52  --inst_passive_queue_type               priority_queues
% 15.49/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.49/2.52  --inst_passive_queues_freq              [25;2]
% 15.49/2.52  --inst_dismatching                      true
% 15.49/2.52  --inst_eager_unprocessed_to_passive     true
% 15.49/2.52  --inst_prop_sim_given                   true
% 15.49/2.52  --inst_prop_sim_new                     false
% 15.49/2.52  --inst_subs_new                         false
% 15.49/2.52  --inst_eq_res_simp                      false
% 15.49/2.52  --inst_subs_given                       false
% 15.49/2.52  --inst_orphan_elimination               true
% 15.49/2.52  --inst_learning_loop_flag               true
% 15.49/2.52  --inst_learning_start                   3000
% 15.49/2.52  --inst_learning_factor                  2
% 15.49/2.52  --inst_start_prop_sim_after_learn       3
% 15.49/2.52  --inst_sel_renew                        solver
% 15.49/2.52  --inst_lit_activity_flag                true
% 15.49/2.52  --inst_restr_to_given                   false
% 15.49/2.52  --inst_activity_threshold               500
% 15.49/2.52  --inst_out_proof                        true
% 15.49/2.52  
% 15.49/2.52  ------ Resolution Options
% 15.49/2.52  
% 15.49/2.52  --resolution_flag                       true
% 15.49/2.52  --res_lit_sel                           adaptive
% 15.49/2.52  --res_lit_sel_side                      none
% 15.49/2.52  --res_ordering                          kbo
% 15.49/2.52  --res_to_prop_solver                    active
% 15.49/2.52  --res_prop_simpl_new                    false
% 15.49/2.52  --res_prop_simpl_given                  true
% 15.49/2.52  --res_passive_queue_type                priority_queues
% 15.49/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.49/2.52  --res_passive_queues_freq               [15;5]
% 15.49/2.52  --res_forward_subs                      full
% 15.49/2.52  --res_backward_subs                     full
% 15.49/2.52  --res_forward_subs_resolution           true
% 15.49/2.52  --res_backward_subs_resolution          true
% 15.49/2.52  --res_orphan_elimination                true
% 15.49/2.52  --res_time_limit                        2.
% 15.49/2.52  --res_out_proof                         true
% 15.49/2.52  
% 15.49/2.52  ------ Superposition Options
% 15.49/2.52  
% 15.49/2.52  --superposition_flag                    true
% 15.49/2.52  --sup_passive_queue_type                priority_queues
% 15.49/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.49/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.49/2.52  --demod_completeness_check              fast
% 15.49/2.52  --demod_use_ground                      true
% 15.49/2.52  --sup_to_prop_solver                    passive
% 15.49/2.52  --sup_prop_simpl_new                    true
% 15.49/2.52  --sup_prop_simpl_given                  true
% 15.49/2.52  --sup_fun_splitting                     true
% 15.49/2.52  --sup_smt_interval                      50000
% 15.49/2.52  
% 15.49/2.52  ------ Superposition Simplification Setup
% 15.49/2.52  
% 15.49/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.49/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.49/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.49/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.49/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.49/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.49/2.52  --sup_immed_triv                        [TrivRules]
% 15.49/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.52  --sup_immed_bw_main                     []
% 15.49/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.49/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.49/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.52  --sup_input_bw                          []
% 15.49/2.52  
% 15.49/2.52  ------ Combination Options
% 15.49/2.52  
% 15.49/2.52  --comb_res_mult                         3
% 15.49/2.52  --comb_sup_mult                         2
% 15.49/2.52  --comb_inst_mult                        10
% 15.49/2.52  
% 15.49/2.52  ------ Debug Options
% 15.49/2.52  
% 15.49/2.52  --dbg_backtrace                         false
% 15.49/2.52  --dbg_dump_prop_clauses                 false
% 15.49/2.52  --dbg_dump_prop_clauses_file            -
% 15.49/2.52  --dbg_out_stat                          false
% 15.49/2.52  ------ Parsing...
% 15.49/2.52  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.49/2.52  
% 15.49/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 15.49/2.52  
% 15.49/2.52  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.49/2.52  
% 15.49/2.52  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.49/2.52  ------ Proving...
% 15.49/2.52  ------ Problem Properties 
% 15.49/2.52  
% 15.49/2.52  
% 15.49/2.52  clauses                                 36
% 15.49/2.52  conjectures                             7
% 15.49/2.52  EPR                                     6
% 15.49/2.52  Horn                                    31
% 15.49/2.52  unary                                   10
% 15.49/2.52  binary                                  9
% 15.49/2.52  lits                                    91
% 15.49/2.52  lits eq                                 33
% 15.49/2.52  fd_pure                                 0
% 15.49/2.52  fd_pseudo                               0
% 15.49/2.52  fd_cond                                 1
% 15.49/2.52  fd_pseudo_cond                          1
% 15.49/2.52  AC symbols                              0
% 15.49/2.52  
% 15.49/2.52  ------ Schedule dynamic 5 is on 
% 15.49/2.52  
% 15.49/2.52  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 15.49/2.52  
% 15.49/2.52  
% 15.49/2.52  ------ 
% 15.49/2.52  Current options:
% 15.49/2.52  ------ 
% 15.49/2.52  
% 15.49/2.52  ------ Input Options
% 15.49/2.52  
% 15.49/2.52  --out_options                           all
% 15.49/2.52  --tptp_safe_out                         true
% 15.49/2.52  --problem_path                          ""
% 15.49/2.52  --include_path                          ""
% 15.49/2.52  --clausifier                            res/vclausify_rel
% 15.49/2.52  --clausifier_options                    ""
% 15.49/2.52  --stdin                                 false
% 15.49/2.52  --stats_out                             all
% 15.49/2.52  
% 15.49/2.52  ------ General Options
% 15.49/2.52  
% 15.49/2.52  --fof                                   false
% 15.49/2.52  --time_out_real                         305.
% 15.49/2.52  --time_out_virtual                      -1.
% 15.49/2.52  --symbol_type_check                     false
% 15.49/2.52  --clausify_out                          false
% 15.49/2.52  --sig_cnt_out                           false
% 15.49/2.52  --trig_cnt_out                          false
% 15.49/2.52  --trig_cnt_out_tolerance                1.
% 15.49/2.52  --trig_cnt_out_sk_spl                   false
% 15.49/2.52  --abstr_cl_out                          false
% 15.49/2.52  
% 15.49/2.52  ------ Global Options
% 15.49/2.52  
% 15.49/2.52  --schedule                              default
% 15.49/2.52  --add_important_lit                     false
% 15.49/2.52  --prop_solver_per_cl                    1000
% 15.49/2.52  --min_unsat_core                        false
% 15.49/2.52  --soft_assumptions                      false
% 15.49/2.52  --soft_lemma_size                       3
% 15.49/2.52  --prop_impl_unit_size                   0
% 15.49/2.52  --prop_impl_unit                        []
% 15.49/2.52  --share_sel_clauses                     true
% 15.49/2.52  --reset_solvers                         false
% 15.49/2.52  --bc_imp_inh                            [conj_cone]
% 15.49/2.52  --conj_cone_tolerance                   3.
% 15.49/2.52  --extra_neg_conj                        none
% 15.49/2.52  --large_theory_mode                     true
% 15.49/2.52  --prolific_symb_bound                   200
% 15.49/2.52  --lt_threshold                          2000
% 15.49/2.52  --clause_weak_htbl                      true
% 15.49/2.52  --gc_record_bc_elim                     false
% 15.49/2.52  
% 15.49/2.52  ------ Preprocessing Options
% 15.49/2.52  
% 15.49/2.52  --preprocessing_flag                    true
% 15.49/2.52  --time_out_prep_mult                    0.1
% 15.49/2.52  --splitting_mode                        input
% 15.49/2.52  --splitting_grd                         true
% 15.49/2.52  --splitting_cvd                         false
% 15.49/2.52  --splitting_cvd_svl                     false
% 15.49/2.52  --splitting_nvd                         32
% 15.49/2.52  --sub_typing                            true
% 15.49/2.52  --prep_gs_sim                           true
% 15.49/2.52  --prep_unflatten                        true
% 15.49/2.52  --prep_res_sim                          true
% 15.49/2.52  --prep_upred                            true
% 15.49/2.52  --prep_sem_filter                       exhaustive
% 15.49/2.52  --prep_sem_filter_out                   false
% 15.49/2.52  --pred_elim                             true
% 15.49/2.52  --res_sim_input                         true
% 15.49/2.52  --eq_ax_congr_red                       true
% 15.49/2.52  --pure_diseq_elim                       true
% 15.49/2.52  --brand_transform                       false
% 15.49/2.52  --non_eq_to_eq                          false
% 15.49/2.52  --prep_def_merge                        true
% 15.49/2.52  --prep_def_merge_prop_impl              false
% 15.49/2.52  --prep_def_merge_mbd                    true
% 15.49/2.52  --prep_def_merge_tr_red                 false
% 15.49/2.52  --prep_def_merge_tr_cl                  false
% 15.49/2.52  --smt_preprocessing                     true
% 15.49/2.52  --smt_ac_axioms                         fast
% 15.49/2.52  --preprocessed_out                      false
% 15.49/2.52  --preprocessed_stats                    false
% 15.49/2.52  
% 15.49/2.52  ------ Abstraction refinement Options
% 15.49/2.52  
% 15.49/2.52  --abstr_ref                             []
% 15.49/2.52  --abstr_ref_prep                        false
% 15.49/2.52  --abstr_ref_until_sat                   false
% 15.49/2.52  --abstr_ref_sig_restrict                funpre
% 15.49/2.52  --abstr_ref_af_restrict_to_split_sk     false
% 15.49/2.52  --abstr_ref_under                       []
% 15.49/2.52  
% 15.49/2.52  ------ SAT Options
% 15.49/2.52  
% 15.49/2.52  --sat_mode                              false
% 15.49/2.52  --sat_fm_restart_options                ""
% 15.49/2.52  --sat_gr_def                            false
% 15.49/2.52  --sat_epr_types                         true
% 15.49/2.52  --sat_non_cyclic_types                  false
% 15.49/2.52  --sat_finite_models                     false
% 15.49/2.52  --sat_fm_lemmas                         false
% 15.49/2.52  --sat_fm_prep                           false
% 15.49/2.52  --sat_fm_uc_incr                        true
% 15.49/2.52  --sat_out_model                         small
% 15.49/2.52  --sat_out_clauses                       false
% 15.49/2.52  
% 15.49/2.52  ------ QBF Options
% 15.49/2.52  
% 15.49/2.52  --qbf_mode                              false
% 15.49/2.52  --qbf_elim_univ                         false
% 15.49/2.52  --qbf_dom_inst                          none
% 15.49/2.52  --qbf_dom_pre_inst                      false
% 15.49/2.52  --qbf_sk_in                             false
% 15.49/2.52  --qbf_pred_elim                         true
% 15.49/2.52  --qbf_split                             512
% 15.49/2.52  
% 15.49/2.52  ------ BMC1 Options
% 15.49/2.52  
% 15.49/2.52  --bmc1_incremental                      false
% 15.49/2.52  --bmc1_axioms                           reachable_all
% 15.49/2.52  --bmc1_min_bound                        0
% 15.49/2.52  --bmc1_max_bound                        -1
% 15.49/2.52  --bmc1_max_bound_default                -1
% 15.49/2.52  --bmc1_symbol_reachability              true
% 15.49/2.52  --bmc1_property_lemmas                  false
% 15.49/2.52  --bmc1_k_induction                      false
% 15.49/2.52  --bmc1_non_equiv_states                 false
% 15.49/2.52  --bmc1_deadlock                         false
% 15.49/2.52  --bmc1_ucm                              false
% 15.49/2.52  --bmc1_add_unsat_core                   none
% 15.49/2.52  --bmc1_unsat_core_children              false
% 15.49/2.52  --bmc1_unsat_core_extrapolate_axioms    false
% 15.49/2.52  --bmc1_out_stat                         full
% 15.49/2.52  --bmc1_ground_init                      false
% 15.49/2.52  --bmc1_pre_inst_next_state              false
% 15.49/2.52  --bmc1_pre_inst_state                   false
% 15.49/2.52  --bmc1_pre_inst_reach_state             false
% 15.49/2.52  --bmc1_out_unsat_core                   false
% 15.49/2.52  --bmc1_aig_witness_out                  false
% 15.49/2.52  --bmc1_verbose                          false
% 15.49/2.52  --bmc1_dump_clauses_tptp                false
% 15.49/2.52  --bmc1_dump_unsat_core_tptp             false
% 15.49/2.52  --bmc1_dump_file                        -
% 15.49/2.52  --bmc1_ucm_expand_uc_limit              128
% 15.49/2.52  --bmc1_ucm_n_expand_iterations          6
% 15.49/2.52  --bmc1_ucm_extend_mode                  1
% 15.49/2.52  --bmc1_ucm_init_mode                    2
% 15.49/2.52  --bmc1_ucm_cone_mode                    none
% 15.49/2.52  --bmc1_ucm_reduced_relation_type        0
% 15.49/2.52  --bmc1_ucm_relax_model                  4
% 15.49/2.52  --bmc1_ucm_full_tr_after_sat            true
% 15.49/2.52  --bmc1_ucm_expand_neg_assumptions       false
% 15.49/2.52  --bmc1_ucm_layered_model                none
% 15.49/2.52  --bmc1_ucm_max_lemma_size               10
% 15.49/2.52  
% 15.49/2.52  ------ AIG Options
% 15.49/2.52  
% 15.49/2.52  --aig_mode                              false
% 15.49/2.52  
% 15.49/2.52  ------ Instantiation Options
% 15.49/2.52  
% 15.49/2.52  --instantiation_flag                    true
% 15.49/2.52  --inst_sos_flag                         true
% 15.49/2.52  --inst_sos_phase                        true
% 15.49/2.52  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 15.49/2.52  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 15.49/2.52  --inst_lit_sel_side                     none
% 15.49/2.52  --inst_solver_per_active                1400
% 15.49/2.52  --inst_solver_calls_frac                1.
% 15.49/2.52  --inst_passive_queue_type               priority_queues
% 15.49/2.52  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 15.49/2.52  --inst_passive_queues_freq              [25;2]
% 15.49/2.52  --inst_dismatching                      true
% 15.49/2.52  --inst_eager_unprocessed_to_passive     true
% 15.49/2.52  --inst_prop_sim_given                   true
% 15.49/2.52  --inst_prop_sim_new                     false
% 15.49/2.52  --inst_subs_new                         false
% 15.49/2.52  --inst_eq_res_simp                      false
% 15.49/2.52  --inst_subs_given                       false
% 15.49/2.52  --inst_orphan_elimination               true
% 15.49/2.52  --inst_learning_loop_flag               true
% 15.49/2.52  --inst_learning_start                   3000
% 15.49/2.52  --inst_learning_factor                  2
% 15.49/2.52  --inst_start_prop_sim_after_learn       3
% 15.49/2.52  --inst_sel_renew                        solver
% 15.49/2.52  --inst_lit_activity_flag                true
% 15.49/2.52  --inst_restr_to_given                   false
% 15.49/2.52  --inst_activity_threshold               500
% 15.49/2.52  --inst_out_proof                        true
% 15.49/2.52  
% 15.49/2.52  ------ Resolution Options
% 15.49/2.52  
% 15.49/2.52  --resolution_flag                       false
% 15.49/2.52  --res_lit_sel                           adaptive
% 15.49/2.52  --res_lit_sel_side                      none
% 15.49/2.52  --res_ordering                          kbo
% 15.49/2.52  --res_to_prop_solver                    active
% 15.49/2.52  --res_prop_simpl_new                    false
% 15.49/2.52  --res_prop_simpl_given                  true
% 15.49/2.52  --res_passive_queue_type                priority_queues
% 15.49/2.52  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 15.49/2.52  --res_passive_queues_freq               [15;5]
% 15.49/2.52  --res_forward_subs                      full
% 15.49/2.52  --res_backward_subs                     full
% 15.49/2.52  --res_forward_subs_resolution           true
% 15.49/2.52  --res_backward_subs_resolution          true
% 15.49/2.52  --res_orphan_elimination                true
% 15.49/2.52  --res_time_limit                        2.
% 15.49/2.52  --res_out_proof                         true
% 15.49/2.52  
% 15.49/2.52  ------ Superposition Options
% 15.49/2.52  
% 15.49/2.52  --superposition_flag                    true
% 15.49/2.52  --sup_passive_queue_type                priority_queues
% 15.49/2.52  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 15.49/2.52  --sup_passive_queues_freq               [8;1;4]
% 15.49/2.52  --demod_completeness_check              fast
% 15.49/2.52  --demod_use_ground                      true
% 15.49/2.52  --sup_to_prop_solver                    passive
% 15.49/2.52  --sup_prop_simpl_new                    true
% 15.49/2.52  --sup_prop_simpl_given                  true
% 15.49/2.52  --sup_fun_splitting                     true
% 15.49/2.52  --sup_smt_interval                      50000
% 15.49/2.52  
% 15.49/2.52  ------ Superposition Simplification Setup
% 15.49/2.52  
% 15.49/2.52  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 15.49/2.52  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 15.49/2.52  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 15.49/2.52  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 15.49/2.52  --sup_full_triv                         [TrivRules;PropSubs]
% 15.49/2.52  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 15.49/2.52  --sup_full_bw                           [BwDemod;BwSubsumption]
% 15.49/2.52  --sup_immed_triv                        [TrivRules]
% 15.49/2.52  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.52  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.52  --sup_immed_bw_main                     []
% 15.49/2.52  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 15.49/2.52  --sup_input_triv                        [Unflattening;TrivRules]
% 15.49/2.52  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 15.49/2.52  --sup_input_bw                          []
% 15.49/2.52  
% 15.49/2.52  ------ Combination Options
% 15.49/2.52  
% 15.49/2.52  --comb_res_mult                         3
% 15.49/2.52  --comb_sup_mult                         2
% 15.49/2.52  --comb_inst_mult                        10
% 15.49/2.52  
% 15.49/2.52  ------ Debug Options
% 15.49/2.52  
% 15.49/2.52  --dbg_backtrace                         false
% 15.49/2.52  --dbg_dump_prop_clauses                 false
% 15.49/2.52  --dbg_dump_prop_clauses_file            -
% 15.49/2.52  --dbg_out_stat                          false
% 15.49/2.52  
% 15.49/2.52  
% 15.49/2.52  
% 15.49/2.52  
% 15.49/2.52  ------ Proving...
% 15.49/2.52  
% 15.49/2.52  
% 15.49/2.52  % SZS status Theorem for theBenchmark.p
% 15.49/2.52  
% 15.49/2.52  % SZS output start CNFRefutation for theBenchmark.p
% 15.49/2.52  
% 15.49/2.52  fof(f21,conjecture,(
% 15.49/2.52    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f22,negated_conjecture,(
% 15.49/2.52    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 15.49/2.52    inference(negated_conjecture,[],[f21])).
% 15.49/2.52  
% 15.49/2.52  fof(f49,plain,(
% 15.49/2.52    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 15.49/2.52    inference(ennf_transformation,[],[f22])).
% 15.49/2.52  
% 15.49/2.52  fof(f50,plain,(
% 15.49/2.52    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 15.49/2.52    inference(flattening,[],[f49])).
% 15.49/2.52  
% 15.49/2.52  fof(f56,plain,(
% 15.49/2.52    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 15.49/2.52    introduced(choice_axiom,[])).
% 15.49/2.52  
% 15.49/2.52  fof(f55,plain,(
% 15.49/2.52    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 15.49/2.52    introduced(choice_axiom,[])).
% 15.49/2.52  
% 15.49/2.52  fof(f57,plain,(
% 15.49/2.52    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 15.49/2.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f50,f56,f55])).
% 15.49/2.52  
% 15.49/2.52  fof(f90,plain,(
% 15.49/2.52    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 15.49/2.52    inference(cnf_transformation,[],[f57])).
% 15.49/2.52  
% 15.49/2.52  fof(f15,axiom,(
% 15.49/2.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f39,plain,(
% 15.49/2.52    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.52    inference(ennf_transformation,[],[f15])).
% 15.49/2.52  
% 15.49/2.52  fof(f75,plain,(
% 15.49/2.52    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.52    inference(cnf_transformation,[],[f39])).
% 15.49/2.52  
% 15.49/2.52  fof(f11,axiom,(
% 15.49/2.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f34,plain,(
% 15.49/2.52    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.52    inference(ennf_transformation,[],[f11])).
% 15.49/2.52  
% 15.49/2.52  fof(f71,plain,(
% 15.49/2.52    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.52    inference(cnf_transformation,[],[f34])).
% 15.49/2.52  
% 15.49/2.52  fof(f2,axiom,(
% 15.49/2.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f53,plain,(
% 15.49/2.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.49/2.52    inference(nnf_transformation,[],[f2])).
% 15.49/2.52  
% 15.49/2.52  fof(f61,plain,(
% 15.49/2.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.49/2.52    inference(cnf_transformation,[],[f53])).
% 15.49/2.52  
% 15.49/2.52  fof(f93,plain,(
% 15.49/2.52    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 15.49/2.52    inference(cnf_transformation,[],[f57])).
% 15.49/2.52  
% 15.49/2.52  fof(f14,axiom,(
% 15.49/2.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f38,plain,(
% 15.49/2.52    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.52    inference(ennf_transformation,[],[f14])).
% 15.49/2.52  
% 15.49/2.52  fof(f74,plain,(
% 15.49/2.52    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.52    inference(cnf_transformation,[],[f38])).
% 15.49/2.52  
% 15.49/2.52  fof(f18,axiom,(
% 15.49/2.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f43,plain,(
% 15.49/2.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.52    inference(ennf_transformation,[],[f18])).
% 15.49/2.52  
% 15.49/2.52  fof(f44,plain,(
% 15.49/2.52    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.52    inference(flattening,[],[f43])).
% 15.49/2.52  
% 15.49/2.52  fof(f54,plain,(
% 15.49/2.52    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.52    inference(nnf_transformation,[],[f44])).
% 15.49/2.52  
% 15.49/2.52  fof(f78,plain,(
% 15.49/2.52    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.52    inference(cnf_transformation,[],[f54])).
% 15.49/2.52  
% 15.49/2.52  fof(f92,plain,(
% 15.49/2.52    v1_funct_2(sK4,sK1,sK2)),
% 15.49/2.52    inference(cnf_transformation,[],[f57])).
% 15.49/2.52  
% 15.49/2.52  fof(f96,plain,(
% 15.49/2.52    k1_xboole_0 != sK2),
% 15.49/2.52    inference(cnf_transformation,[],[f57])).
% 15.49/2.52  
% 15.49/2.52  fof(f9,axiom,(
% 15.49/2.52    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f31,plain,(
% 15.49/2.52    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 15.49/2.52    inference(ennf_transformation,[],[f9])).
% 15.49/2.52  
% 15.49/2.52  fof(f32,plain,(
% 15.49/2.52    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 15.49/2.52    inference(flattening,[],[f31])).
% 15.49/2.52  
% 15.49/2.52  fof(f69,plain,(
% 15.49/2.52    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 15.49/2.52    inference(cnf_transformation,[],[f32])).
% 15.49/2.52  
% 15.49/2.52  fof(f95,plain,(
% 15.49/2.52    v2_funct_1(sK4)),
% 15.49/2.52    inference(cnf_transformation,[],[f57])).
% 15.49/2.52  
% 15.49/2.52  fof(f91,plain,(
% 15.49/2.52    v1_funct_1(sK4)),
% 15.49/2.52    inference(cnf_transformation,[],[f57])).
% 15.49/2.52  
% 15.49/2.52  fof(f3,axiom,(
% 15.49/2.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f24,plain,(
% 15.49/2.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.49/2.52    inference(ennf_transformation,[],[f3])).
% 15.49/2.52  
% 15.49/2.52  fof(f63,plain,(
% 15.49/2.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.49/2.52    inference(cnf_transformation,[],[f24])).
% 15.49/2.52  
% 15.49/2.52  fof(f62,plain,(
% 15.49/2.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.49/2.52    inference(cnf_transformation,[],[f53])).
% 15.49/2.52  
% 15.49/2.52  fof(f4,axiom,(
% 15.49/2.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f64,plain,(
% 15.49/2.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.49/2.52    inference(cnf_transformation,[],[f4])).
% 15.49/2.52  
% 15.49/2.52  fof(f6,axiom,(
% 15.49/2.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f26,plain,(
% 15.49/2.52    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 15.49/2.52    inference(ennf_transformation,[],[f6])).
% 15.49/2.52  
% 15.49/2.52  fof(f66,plain,(
% 15.49/2.52    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 15.49/2.52    inference(cnf_transformation,[],[f26])).
% 15.49/2.52  
% 15.49/2.52  fof(f16,axiom,(
% 15.49/2.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f40,plain,(
% 15.49/2.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.49/2.52    inference(ennf_transformation,[],[f16])).
% 15.49/2.52  
% 15.49/2.52  fof(f41,plain,(
% 15.49/2.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.52    inference(flattening,[],[f40])).
% 15.49/2.52  
% 15.49/2.52  fof(f76,plain,(
% 15.49/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k4_relset_1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.52    inference(cnf_transformation,[],[f41])).
% 15.49/2.52  
% 15.49/2.52  fof(f12,axiom,(
% 15.49/2.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f35,plain,(
% 15.49/2.52    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 15.49/2.52    inference(ennf_transformation,[],[f12])).
% 15.49/2.52  
% 15.49/2.52  fof(f36,plain,(
% 15.49/2.52    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.52    inference(flattening,[],[f35])).
% 15.49/2.52  
% 15.49/2.52  fof(f72,plain,(
% 15.49/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.52    inference(cnf_transformation,[],[f36])).
% 15.49/2.52  
% 15.49/2.52  fof(f19,axiom,(
% 15.49/2.52    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f45,plain,(
% 15.49/2.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 15.49/2.52    inference(ennf_transformation,[],[f19])).
% 15.49/2.52  
% 15.49/2.52  fof(f46,plain,(
% 15.49/2.52    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 15.49/2.52    inference(flattening,[],[f45])).
% 15.49/2.52  
% 15.49/2.52  fof(f84,plain,(
% 15.49/2.52    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 15.49/2.52    inference(cnf_transformation,[],[f46])).
% 15.49/2.52  
% 15.49/2.52  fof(f88,plain,(
% 15.49/2.52    v1_funct_1(sK3)),
% 15.49/2.52    inference(cnf_transformation,[],[f57])).
% 15.49/2.52  
% 15.49/2.52  fof(f94,plain,(
% 15.49/2.52    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 15.49/2.52    inference(cnf_transformation,[],[f57])).
% 15.49/2.52  
% 15.49/2.52  fof(f10,axiom,(
% 15.49/2.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f23,plain,(
% 15.49/2.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 15.49/2.52    inference(pure_predicate_removal,[],[f10])).
% 15.49/2.52  
% 15.49/2.52  fof(f33,plain,(
% 15.49/2.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.49/2.52    inference(ennf_transformation,[],[f23])).
% 15.49/2.52  
% 15.49/2.52  fof(f70,plain,(
% 15.49/2.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.49/2.52    inference(cnf_transformation,[],[f33])).
% 15.49/2.52  
% 15.49/2.52  fof(f7,axiom,(
% 15.49/2.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f27,plain,(
% 15.49/2.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 15.49/2.52    inference(ennf_transformation,[],[f7])).
% 15.49/2.52  
% 15.49/2.52  fof(f28,plain,(
% 15.49/2.52    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.49/2.52    inference(flattening,[],[f27])).
% 15.49/2.52  
% 15.49/2.52  fof(f67,plain,(
% 15.49/2.52    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.49/2.52    inference(cnf_transformation,[],[f28])).
% 15.49/2.52  
% 15.49/2.52  fof(f5,axiom,(
% 15.49/2.52    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f25,plain,(
% 15.49/2.52    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 15.49/2.52    inference(ennf_transformation,[],[f5])).
% 15.49/2.52  
% 15.49/2.52  fof(f65,plain,(
% 15.49/2.52    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.49/2.52    inference(cnf_transformation,[],[f25])).
% 15.49/2.52  
% 15.49/2.52  fof(f8,axiom,(
% 15.49/2.52    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(k9_relat_1(X2,X0),X1) & r1_tarski(X0,k1_relat_1(X2))) => r1_tarski(X0,k10_relat_1(X2,X1))))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f29,plain,(
% 15.49/2.52    ! [X0,X1,X2] : ((r1_tarski(X0,k10_relat_1(X2,X1)) | (~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 15.49/2.52    inference(ennf_transformation,[],[f8])).
% 15.49/2.52  
% 15.49/2.52  fof(f30,plain,(
% 15.49/2.52    ! [X0,X1,X2] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 15.49/2.52    inference(flattening,[],[f29])).
% 15.49/2.52  
% 15.49/2.52  fof(f68,plain,(
% 15.49/2.52    ( ! [X2,X0,X1] : (r1_tarski(X0,k10_relat_1(X2,X1)) | ~r1_tarski(k9_relat_1(X2,X0),X1) | ~r1_tarski(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 15.49/2.52    inference(cnf_transformation,[],[f30])).
% 15.49/2.52  
% 15.49/2.52  fof(f1,axiom,(
% 15.49/2.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.49/2.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 15.49/2.52  
% 15.49/2.52  fof(f51,plain,(
% 15.49/2.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.49/2.52    inference(nnf_transformation,[],[f1])).
% 15.49/2.52  
% 15.49/2.52  fof(f52,plain,(
% 15.49/2.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.49/2.52    inference(flattening,[],[f51])).
% 15.49/2.52  
% 15.49/2.52  fof(f59,plain,(
% 15.49/2.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 15.49/2.52    inference(cnf_transformation,[],[f52])).
% 15.49/2.52  
% 15.49/2.52  fof(f98,plain,(
% 15.49/2.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.49/2.52    inference(equality_resolution,[],[f59])).
% 15.49/2.52  
% 15.49/2.52  fof(f60,plain,(
% 15.49/2.52    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.49/2.52    inference(cnf_transformation,[],[f52])).
% 15.49/2.52  
% 15.49/2.52  fof(f97,plain,(
% 15.49/2.52    k2_relset_1(sK0,sK1,sK3) != sK1),
% 15.49/2.52    inference(cnf_transformation,[],[f57])).
% 15.49/2.52  
% 15.49/2.52  cnf(c_37,negated_conjecture,
% 15.49/2.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.49/2.52      inference(cnf_transformation,[],[f90]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1714,plain,
% 15.49/2.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_17,plain,
% 15.49/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.49/2.52      inference(cnf_transformation,[],[f75]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1721,plain,
% 15.49/2.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.49/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2606,plain,
% 15.49/2.52      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_1714,c_1721]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_13,plain,
% 15.49/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.52      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 15.49/2.52      inference(cnf_transformation,[],[f71]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1725,plain,
% 15.49/2.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.49/2.52      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_3249,plain,
% 15.49/2.52      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top
% 15.49/2.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_2606,c_1725]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_42,plain,
% 15.49/2.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_3744,plain,
% 15.49/2.52      ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) = iProver_top ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_3249,c_42]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_4,plain,
% 15.49/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.49/2.52      inference(cnf_transformation,[],[f61]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1730,plain,
% 15.49/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.49/2.52      | r1_tarski(X0,X1) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_3748,plain,
% 15.49/2.52      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_3744,c_1730]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_34,negated_conjecture,
% 15.49/2.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 15.49/2.52      inference(cnf_transformation,[],[f93]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1716,plain,
% 15.49/2.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_16,plain,
% 15.49/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.52      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.49/2.52      inference(cnf_transformation,[],[f74]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1722,plain,
% 15.49/2.52      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.49/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2707,plain,
% 15.49/2.52      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_1716,c_1722]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_25,plain,
% 15.49/2.52      ( ~ v1_funct_2(X0,X1,X2)
% 15.49/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.52      | k1_relset_1(X1,X2,X0) = X1
% 15.49/2.52      | k1_xboole_0 = X2 ),
% 15.49/2.52      inference(cnf_transformation,[],[f78]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_35,negated_conjecture,
% 15.49/2.52      ( v1_funct_2(sK4,sK1,sK2) ),
% 15.49/2.52      inference(cnf_transformation,[],[f92]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_662,plain,
% 15.49/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.52      | k1_relset_1(X1,X2,X0) = X1
% 15.49/2.52      | sK4 != X0
% 15.49/2.52      | sK2 != X2
% 15.49/2.52      | sK1 != X1
% 15.49/2.52      | k1_xboole_0 = X2 ),
% 15.49/2.52      inference(resolution_lifted,[status(thm)],[c_25,c_35]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_663,plain,
% 15.49/2.52      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 15.49/2.52      | k1_relset_1(sK1,sK2,sK4) = sK1
% 15.49/2.52      | k1_xboole_0 = sK2 ),
% 15.49/2.52      inference(unflattening,[status(thm)],[c_662]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_31,negated_conjecture,
% 15.49/2.52      ( k1_xboole_0 != sK2 ),
% 15.49/2.52      inference(cnf_transformation,[],[f96]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_665,plain,
% 15.49/2.52      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_663,c_34,c_31]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2709,plain,
% 15.49/2.52      ( k1_relat_1(sK4) = sK1 ),
% 15.49/2.52      inference(light_normalisation,[status(thm)],[c_2707,c_665]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_11,plain,
% 15.49/2.52      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 15.49/2.52      | ~ v2_funct_1(X1)
% 15.49/2.52      | ~ v1_funct_1(X1)
% 15.49/2.52      | ~ v1_relat_1(X1)
% 15.49/2.52      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 15.49/2.52      inference(cnf_transformation,[],[f69]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_32,negated_conjecture,
% 15.49/2.52      ( v2_funct_1(sK4) ),
% 15.49/2.52      inference(cnf_transformation,[],[f95]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_494,plain,
% 15.49/2.52      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 15.49/2.52      | ~ v1_funct_1(X1)
% 15.49/2.52      | ~ v1_relat_1(X1)
% 15.49/2.52      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 15.49/2.52      | sK4 != X1 ),
% 15.49/2.52      inference(resolution_lifted,[status(thm)],[c_11,c_32]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_495,plain,
% 15.49/2.52      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 15.49/2.52      | ~ v1_funct_1(sK4)
% 15.49/2.52      | ~ v1_relat_1(sK4)
% 15.49/2.52      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 15.49/2.52      inference(unflattening,[status(thm)],[c_494]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_36,negated_conjecture,
% 15.49/2.52      ( v1_funct_1(sK4) ),
% 15.49/2.52      inference(cnf_transformation,[],[f91]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_499,plain,
% 15.49/2.52      ( ~ r1_tarski(X0,k1_relat_1(sK4))
% 15.49/2.52      | ~ v1_relat_1(sK4)
% 15.49/2.52      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_495,c_36]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1710,plain,
% 15.49/2.52      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 15.49/2.52      | r1_tarski(X0,k1_relat_1(sK4)) != iProver_top
% 15.49/2.52      | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2829,plain,
% 15.49/2.52      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 15.49/2.52      | r1_tarski(X0,sK1) != iProver_top
% 15.49/2.52      | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.52      inference(demodulation,[status(thm)],[c_2709,c_1710]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2105,plain,
% 15.49/2.52      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_1716,c_1730]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5,plain,
% 15.49/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.49/2.52      | ~ v1_relat_1(X1)
% 15.49/2.52      | v1_relat_1(X0) ),
% 15.49/2.52      inference(cnf_transformation,[],[f63]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_3,plain,
% 15.49/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.49/2.52      inference(cnf_transformation,[],[f62]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_287,plain,
% 15.49/2.52      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.49/2.52      inference(prop_impl,[status(thm)],[c_3]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_288,plain,
% 15.49/2.52      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.49/2.52      inference(renaming,[status(thm)],[c_287]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_353,plain,
% 15.49/2.52      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.49/2.52      inference(bin_hyper_res,[status(thm)],[c_5,c_288]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2139,plain,
% 15.49/2.52      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 15.49/2.52      | v1_relat_1(X0)
% 15.49/2.52      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_353]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2824,plain,
% 15.49/2.52      ( ~ r1_tarski(sK4,k2_zfmisc_1(sK1,sK2))
% 15.49/2.52      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
% 15.49/2.52      | v1_relat_1(sK4) ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_2139]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2825,plain,
% 15.49/2.52      ( r1_tarski(sK4,k2_zfmisc_1(sK1,sK2)) != iProver_top
% 15.49/2.52      | v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 15.49/2.52      | v1_relat_1(sK4) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_2824]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_6,plain,
% 15.49/2.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.49/2.52      inference(cnf_transformation,[],[f64]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2949,plain,
% 15.49/2.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_6]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2950,plain,
% 15.49/2.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_2949]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5828,plain,
% 15.49/2.52      ( r1_tarski(X0,sK1) != iProver_top
% 15.49/2.52      | k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0 ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_2829,c_2105,c_2825,c_2950]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5829,plain,
% 15.49/2.52      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 15.49/2.52      | r1_tarski(X0,sK1) != iProver_top ),
% 15.49/2.52      inference(renaming,[status(thm)],[c_5828]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5835,plain,
% 15.49/2.52      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_3748,c_5829]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2106,plain,
% 15.49/2.52      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_1714,c_1730]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1712,plain,
% 15.49/2.52      ( r1_tarski(X0,X1) != iProver_top
% 15.49/2.52      | v1_relat_1(X1) != iProver_top
% 15.49/2.52      | v1_relat_1(X0) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_353]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_13662,plain,
% 15.49/2.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 15.49/2.52      | v1_relat_1(sK3) = iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_2106,c_1712]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2834,plain,
% 15.49/2.52      ( ~ r1_tarski(sK3,k2_zfmisc_1(sK0,sK1))
% 15.49/2.52      | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
% 15.49/2.52      | v1_relat_1(sK3) ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_2139]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2835,plain,
% 15.49/2.52      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) != iProver_top
% 15.49/2.52      | v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 15.49/2.52      | v1_relat_1(sK3) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_2834]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2952,plain,
% 15.49/2.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_6]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2953,plain,
% 15.49/2.52      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_2952]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_14302,plain,
% 15.49/2.52      ( v1_relat_1(sK3) = iProver_top ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_13662,c_2106,c_2835,c_2953]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_13661,plain,
% 15.49/2.52      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 15.49/2.52      | v1_relat_1(sK4) = iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_2105,c_1712]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_14148,plain,
% 15.49/2.52      ( v1_relat_1(sK4) = iProver_top ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_13661,c_2105,c_2825,c_2950]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_8,plain,
% 15.49/2.52      ( ~ v1_relat_1(X0)
% 15.49/2.52      | ~ v1_relat_1(X1)
% 15.49/2.52      | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 15.49/2.52      inference(cnf_transformation,[],[f66]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1727,plain,
% 15.49/2.52      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 15.49/2.52      | v1_relat_1(X1) != iProver_top
% 15.49/2.52      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_14152,plain,
% 15.49/2.52      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 15.49/2.52      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_14148,c_1727]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_15102,plain,
% 15.49/2.52      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_14302,c_14152]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_18,plain,
% 15.49/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.49/2.52      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.49/2.52      inference(cnf_transformation,[],[f76]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1720,plain,
% 15.49/2.52      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.49/2.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.49/2.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_4044,plain,
% 15.49/2.52      ( k4_relset_1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 15.49/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_1716,c_1720]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_4324,plain,
% 15.49/2.52      ( k4_relset_1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_1714,c_4044]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_14,plain,
% 15.49/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.49/2.52      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 15.49/2.52      inference(cnf_transformation,[],[f72]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1724,plain,
% 15.49/2.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.49/2.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 15.49/2.52      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_4668,plain,
% 15.49/2.52      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 15.49/2.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 15.49/2.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_4324,c_1724]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_45,plain,
% 15.49/2.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_8421,plain,
% 15.49/2.52      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_4668,c_42,c_45]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_8432,plain,
% 15.49/2.52      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_8421,c_1721]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_26,plain,
% 15.49/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 15.49/2.52      | ~ v1_funct_1(X0)
% 15.49/2.52      | ~ v1_funct_1(X3)
% 15.49/2.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 15.49/2.52      inference(cnf_transformation,[],[f84]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1718,plain,
% 15.49/2.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 15.49/2.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 15.49/2.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.52      | v1_funct_1(X5) != iProver_top
% 15.49/2.52      | v1_funct_1(X4) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5040,plain,
% 15.49/2.52      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 15.49/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.52      | v1_funct_1(X2) != iProver_top
% 15.49/2.52      | v1_funct_1(sK4) != iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_1716,c_1718]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_43,plain,
% 15.49/2.52      ( v1_funct_1(sK4) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5253,plain,
% 15.49/2.52      ( v1_funct_1(X2) != iProver_top
% 15.49/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.52      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_5040,c_43]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5254,plain,
% 15.49/2.52      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 15.49/2.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 15.49/2.52      | v1_funct_1(X2) != iProver_top ),
% 15.49/2.52      inference(renaming,[status(thm)],[c_5253]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5265,plain,
% 15.49/2.52      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 15.49/2.52      | v1_funct_1(sK3) != iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_1714,c_5254]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_39,negated_conjecture,
% 15.49/2.52      ( v1_funct_1(sK3) ),
% 15.49/2.52      inference(cnf_transformation,[],[f88]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_40,plain,
% 15.49/2.52      ( v1_funct_1(sK3) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5393,plain,
% 15.49/2.52      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_5265,c_40]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_33,negated_conjecture,
% 15.49/2.52      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 15.49/2.52      inference(cnf_transformation,[],[f94]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5395,plain,
% 15.49/2.52      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 15.49/2.52      inference(demodulation,[status(thm)],[c_5393,c_33]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_8436,plain,
% 15.49/2.52      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 15.49/2.52      inference(light_normalisation,[status(thm)],[c_8432,c_5395]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_15103,plain,
% 15.49/2.52      ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
% 15.49/2.52      inference(light_normalisation,[status(thm)],[c_15102,c_8436]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_47201,plain,
% 15.49/2.52      ( k10_relat_1(sK4,sK2) = k2_relat_1(sK3) ),
% 15.49/2.52      inference(light_normalisation,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_5835,c_5835,c_15103]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_12,plain,
% 15.49/2.52      ( v4_relat_1(X0,X1)
% 15.49/2.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 15.49/2.52      inference(cnf_transformation,[],[f70]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_9,plain,
% 15.49/2.52      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 15.49/2.52      inference(cnf_transformation,[],[f67]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_476,plain,
% 15.49/2.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.49/2.52      | ~ v1_relat_1(X0)
% 15.49/2.52      | k7_relat_1(X0,X1) = X0 ),
% 15.49/2.52      inference(resolution,[status(thm)],[c_12,c_9]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1711,plain,
% 15.49/2.52      ( k7_relat_1(X0,X1) = X0
% 15.49/2.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 15.49/2.52      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5015,plain,
% 15.49/2.52      ( k7_relat_1(sK4,sK1) = sK4 | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_1716,c_1711]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_5196,plain,
% 15.49/2.52      ( k7_relat_1(sK4,sK1) = sK4 ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_5015,c_2105,c_2825,c_2950]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_7,plain,
% 15.49/2.52      ( ~ v1_relat_1(X0)
% 15.49/2.52      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 15.49/2.52      inference(cnf_transformation,[],[f65]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1728,plain,
% 15.49/2.52      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 15.49/2.52      | v1_relat_1(X0) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_14153,plain,
% 15.49/2.52      ( k2_relat_1(k7_relat_1(sK4,X0)) = k9_relat_1(sK4,X0) ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_14148,c_1728]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_14834,plain,
% 15.49/2.52      ( k9_relat_1(sK4,sK1) = k2_relat_1(sK4) ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_5196,c_14153]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_10,plain,
% 15.49/2.52      ( r1_tarski(X0,k10_relat_1(X1,X2))
% 15.49/2.52      | ~ r1_tarski(X0,k1_relat_1(X1))
% 15.49/2.52      | ~ r1_tarski(k9_relat_1(X1,X0),X2)
% 15.49/2.52      | ~ v1_funct_1(X1)
% 15.49/2.52      | ~ v1_relat_1(X1) ),
% 15.49/2.52      inference(cnf_transformation,[],[f68]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1726,plain,
% 15.49/2.52      ( r1_tarski(X0,k10_relat_1(X1,X2)) = iProver_top
% 15.49/2.52      | r1_tarski(X0,k1_relat_1(X1)) != iProver_top
% 15.49/2.52      | r1_tarski(k9_relat_1(X1,X0),X2) != iProver_top
% 15.49/2.52      | v1_funct_1(X1) != iProver_top
% 15.49/2.52      | v1_relat_1(X1) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_15224,plain,
% 15.49/2.52      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 15.49/2.52      | r1_tarski(sK1,k10_relat_1(sK4,X0)) = iProver_top
% 15.49/2.52      | r1_tarski(sK1,k1_relat_1(sK4)) != iProver_top
% 15.49/2.52      | v1_funct_1(sK4) != iProver_top
% 15.49/2.52      | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_14834,c_1726]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_15225,plain,
% 15.49/2.52      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 15.49/2.52      | r1_tarski(sK1,k10_relat_1(sK4,X0)) = iProver_top
% 15.49/2.52      | r1_tarski(sK1,sK1) != iProver_top
% 15.49/2.52      | v1_funct_1(sK4) != iProver_top
% 15.49/2.52      | v1_relat_1(sK4) != iProver_top ),
% 15.49/2.52      inference(light_normalisation,[status(thm)],[c_15224,c_2709]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1,plain,
% 15.49/2.52      ( r1_tarski(X0,X0) ),
% 15.49/2.52      inference(cnf_transformation,[],[f98]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2004,plain,
% 15.49/2.52      ( r1_tarski(sK1,sK1) ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_1]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2005,plain,
% 15.49/2.52      ( r1_tarski(sK1,sK1) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_2004]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_15478,plain,
% 15.49/2.52      ( r1_tarski(sK1,k10_relat_1(sK4,X0)) = iProver_top
% 15.49/2.52      | r1_tarski(k2_relat_1(sK4),X0) != iProver_top ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_15225,c_43,c_2005,c_2105,c_2825,c_2950]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_15479,plain,
% 15.49/2.52      ( r1_tarski(k2_relat_1(sK4),X0) != iProver_top
% 15.49/2.52      | r1_tarski(sK1,k10_relat_1(sK4,X0)) = iProver_top ),
% 15.49/2.52      inference(renaming,[status(thm)],[c_15478]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_47205,plain,
% 15.49/2.52      ( r1_tarski(k2_relat_1(sK4),sK2) != iProver_top
% 15.49/2.52      | r1_tarski(sK1,k2_relat_1(sK3)) = iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_47201,c_15479]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2605,plain,
% 15.49/2.52      ( k2_relset_1(sK1,sK2,sK4) = k2_relat_1(sK4) ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_1716,c_1721]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_3251,plain,
% 15.49/2.52      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top
% 15.49/2.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_2605,c_1725]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_3952,plain,
% 15.49/2.52      ( m1_subset_1(k2_relat_1(sK4),k1_zfmisc_1(sK2)) = iProver_top ),
% 15.49/2.52      inference(global_propositional_subsumption,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_3251,c_45]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_3956,plain,
% 15.49/2.52      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 15.49/2.52      inference(superposition,[status(thm)],[c_3952,c_1730]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1004,plain,
% 15.49/2.52      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 15.49/2.52      theory(equality) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1990,plain,
% 15.49/2.52      ( ~ r1_tarski(X0,X1)
% 15.49/2.52      | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3))
% 15.49/2.52      | k2_relset_1(sK0,sK1,sK3) != X1
% 15.49/2.52      | sK1 != X0 ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_1004]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_2189,plain,
% 15.49/2.52      ( ~ r1_tarski(sK1,X0)
% 15.49/2.52      | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3))
% 15.49/2.52      | k2_relset_1(sK0,sK1,sK3) != X0
% 15.49/2.52      | sK1 != sK1 ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_1990]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_3167,plain,
% 15.49/2.52      ( r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3))
% 15.49/2.52      | ~ r1_tarski(sK1,k2_relat_1(sK3))
% 15.49/2.52      | k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 15.49/2.52      | sK1 != sK1 ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_2189]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_3168,plain,
% 15.49/2.52      ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 15.49/2.52      | sK1 != sK1
% 15.49/2.52      | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3)) = iProver_top
% 15.49/2.52      | r1_tarski(sK1,k2_relat_1(sK3)) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_3167]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1002,plain,( X0 = X0 ),theory(equality) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1998,plain,
% 15.49/2.52      ( sK1 = sK1 ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_1002]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1865,plain,
% 15.49/2.52      ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
% 15.49/2.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_13]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1866,plain,
% 15.49/2.52      ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) = iProver_top
% 15.49/2.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_1865]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1807,plain,
% 15.49/2.52      ( ~ m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
% 15.49/2.52      | r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1) ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_4]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1808,plain,
% 15.49/2.52      ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1)) != iProver_top
% 15.49/2.52      | r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1) = iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_1807]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_0,plain,
% 15.49/2.52      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 15.49/2.52      inference(cnf_transformation,[],[f60]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1774,plain,
% 15.49/2.52      ( ~ r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1)
% 15.49/2.52      | ~ r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3))
% 15.49/2.52      | k2_relset_1(sK0,sK1,sK3) = sK1 ),
% 15.49/2.52      inference(instantiation,[status(thm)],[c_0]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_1775,plain,
% 15.49/2.52      ( k2_relset_1(sK0,sK1,sK3) = sK1
% 15.49/2.52      | r1_tarski(k2_relset_1(sK0,sK1,sK3),sK1) != iProver_top
% 15.49/2.52      | r1_tarski(sK1,k2_relset_1(sK0,sK1,sK3)) != iProver_top ),
% 15.49/2.52      inference(predicate_to_equality,[status(thm)],[c_1774]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(c_30,negated_conjecture,
% 15.49/2.52      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 15.49/2.52      inference(cnf_transformation,[],[f97]) ).
% 15.49/2.52  
% 15.49/2.52  cnf(contradiction,plain,
% 15.49/2.52      ( $false ),
% 15.49/2.52      inference(minisat,
% 15.49/2.52                [status(thm)],
% 15.49/2.52                [c_47205,c_3956,c_3168,c_2606,c_1998,c_1866,c_1808,
% 15.49/2.52                 c_1775,c_30,c_42]) ).
% 15.49/2.52  
% 15.49/2.52  
% 15.49/2.52  % SZS output end CNFRefutation for theBenchmark.p
% 15.49/2.52  
% 15.49/2.52  ------                               Statistics
% 15.49/2.52  
% 15.49/2.52  ------ General
% 15.49/2.52  
% 15.49/2.52  abstr_ref_over_cycles:                  0
% 15.49/2.52  abstr_ref_under_cycles:                 0
% 15.49/2.52  gc_basic_clause_elim:                   0
% 15.49/2.52  forced_gc_time:                         0
% 15.49/2.52  parsing_time:                           0.028
% 15.49/2.52  unif_index_cands_time:                  0.
% 15.49/2.52  unif_index_add_time:                    0.
% 15.49/2.52  orderings_time:                         0.
% 15.49/2.52  out_proof_time:                         0.016
% 15.49/2.52  total_time:                             1.566
% 15.49/2.52  num_of_symbols:                         57
% 15.49/2.52  num_of_terms:                           57479
% 15.49/2.52  
% 15.49/2.52  ------ Preprocessing
% 15.49/2.52  
% 15.49/2.52  num_of_splits:                          0
% 15.49/2.52  num_of_split_atoms:                     0
% 15.49/2.52  num_of_reused_defs:                     0
% 15.49/2.52  num_eq_ax_congr_red:                    49
% 15.49/2.52  num_of_sem_filtered_clauses:            1
% 15.49/2.52  num_of_subtypes:                        0
% 15.49/2.52  monotx_restored_types:                  0
% 15.49/2.52  sat_num_of_epr_types:                   0
% 15.49/2.52  sat_num_of_non_cyclic_types:            0
% 15.49/2.52  sat_guarded_non_collapsed_types:        0
% 15.49/2.52  num_pure_diseq_elim:                    0
% 15.49/2.52  simp_replaced_by:                       0
% 15.49/2.52  res_preprocessed:                       177
% 15.49/2.52  prep_upred:                             0
% 15.49/2.52  prep_unflattend:                        42
% 15.49/2.52  smt_new_axioms:                         0
% 15.49/2.52  pred_elim_cands:                        4
% 15.49/2.52  pred_elim:                              3
% 15.49/2.52  pred_elim_cl:                           2
% 15.49/2.52  pred_elim_cycles:                       5
% 15.49/2.52  merged_defs:                            8
% 15.49/2.52  merged_defs_ncl:                        0
% 15.49/2.52  bin_hyper_res:                          9
% 15.49/2.52  prep_cycles:                            4
% 15.49/2.52  pred_elim_time:                         0.006
% 15.49/2.52  splitting_time:                         0.
% 15.49/2.52  sem_filter_time:                        0.
% 15.49/2.52  monotx_time:                            0.
% 15.49/2.52  subtype_inf_time:                       0.
% 15.49/2.52  
% 15.49/2.52  ------ Problem properties
% 15.49/2.52  
% 15.49/2.52  clauses:                                36
% 15.49/2.52  conjectures:                            7
% 15.49/2.52  epr:                                    6
% 15.49/2.52  horn:                                   31
% 15.49/2.52  ground:                                 13
% 15.49/2.52  unary:                                  10
% 15.49/2.52  binary:                                 9
% 15.49/2.52  lits:                                   91
% 15.49/2.52  lits_eq:                                33
% 15.49/2.52  fd_pure:                                0
% 15.49/2.52  fd_pseudo:                              0
% 15.49/2.52  fd_cond:                                1
% 15.49/2.52  fd_pseudo_cond:                         1
% 15.49/2.52  ac_symbols:                             0
% 15.49/2.52  
% 15.49/2.52  ------ Propositional Solver
% 15.49/2.52  
% 15.49/2.52  prop_solver_calls:                      35
% 15.49/2.52  prop_fast_solver_calls:                 2148
% 15.49/2.52  smt_solver_calls:                       0
% 15.49/2.52  smt_fast_solver_calls:                  0
% 15.49/2.52  prop_num_of_clauses:                    22254
% 15.49/2.52  prop_preprocess_simplified:             28074
% 15.49/2.52  prop_fo_subsumed:                       116
% 15.49/2.52  prop_solver_time:                       0.
% 15.49/2.52  smt_solver_time:                        0.
% 15.49/2.52  smt_fast_solver_time:                   0.
% 15.49/2.52  prop_fast_solver_time:                  0.
% 15.49/2.52  prop_unsat_core_time:                   0.002
% 15.49/2.52  
% 15.49/2.52  ------ QBF
% 15.49/2.52  
% 15.49/2.52  qbf_q_res:                              0
% 15.49/2.52  qbf_num_tautologies:                    0
% 15.49/2.52  qbf_prep_cycles:                        0
% 15.49/2.52  
% 15.49/2.52  ------ BMC1
% 15.49/2.52  
% 15.49/2.52  bmc1_current_bound:                     -1
% 15.49/2.52  bmc1_last_solved_bound:                 -1
% 15.49/2.52  bmc1_unsat_core_size:                   -1
% 15.49/2.52  bmc1_unsat_core_parents_size:           -1
% 15.49/2.52  bmc1_merge_next_fun:                    0
% 15.49/2.52  bmc1_unsat_core_clauses_time:           0.
% 15.49/2.52  
% 15.49/2.52  ------ Instantiation
% 15.49/2.52  
% 15.49/2.52  inst_num_of_clauses:                    5103
% 15.49/2.52  inst_num_in_passive:                    1749
% 15.49/2.52  inst_num_in_active:                     2437
% 15.49/2.52  inst_num_in_unprocessed:                917
% 15.49/2.52  inst_num_of_loops:                      2630
% 15.49/2.52  inst_num_of_learning_restarts:          0
% 15.49/2.52  inst_num_moves_active_passive:          187
% 15.49/2.52  inst_lit_activity:                      0
% 15.49/2.52  inst_lit_activity_moves:                1
% 15.49/2.52  inst_num_tautologies:                   0
% 15.49/2.52  inst_num_prop_implied:                  0
% 15.49/2.52  inst_num_existing_simplified:           0
% 15.49/2.52  inst_num_eq_res_simplified:             0
% 15.49/2.52  inst_num_child_elim:                    0
% 15.49/2.52  inst_num_of_dismatching_blockings:      5371
% 15.49/2.52  inst_num_of_non_proper_insts:           8482
% 15.49/2.52  inst_num_of_duplicates:                 0
% 15.49/2.52  inst_inst_num_from_inst_to_res:         0
% 15.49/2.52  inst_dismatching_checking_time:         0.
% 15.49/2.52  
% 15.49/2.52  ------ Resolution
% 15.49/2.52  
% 15.49/2.52  res_num_of_clauses:                     0
% 15.49/2.52  res_num_in_passive:                     0
% 15.49/2.52  res_num_in_active:                      0
% 15.49/2.52  res_num_of_loops:                       181
% 15.49/2.52  res_forward_subset_subsumed:            423
% 15.49/2.52  res_backward_subset_subsumed:           0
% 15.49/2.52  res_forward_subsumed:                   0
% 15.49/2.52  res_backward_subsumed:                  0
% 15.49/2.52  res_forward_subsumption_resolution:     0
% 15.49/2.52  res_backward_subsumption_resolution:    0
% 15.49/2.52  res_clause_to_clause_subsumption:       6253
% 15.49/2.52  res_orphan_elimination:                 0
% 15.49/2.52  res_tautology_del:                      541
% 15.49/2.52  res_num_eq_res_simplified:              0
% 15.49/2.52  res_num_sel_changes:                    0
% 15.49/2.52  res_moves_from_active_to_pass:          0
% 15.49/2.52  
% 15.49/2.52  ------ Superposition
% 15.49/2.52  
% 15.49/2.52  sup_time_total:                         0.
% 15.49/2.52  sup_time_generating:                    0.
% 15.49/2.52  sup_time_sim_full:                      0.
% 15.49/2.52  sup_time_sim_immed:                     0.
% 15.49/2.52  
% 15.49/2.52  sup_num_of_clauses:                     2570
% 15.49/2.52  sup_num_in_active:                      509
% 15.49/2.52  sup_num_in_passive:                     2061
% 15.49/2.52  sup_num_of_loops:                       524
% 15.49/2.52  sup_fw_superposition:                   2371
% 15.49/2.52  sup_bw_superposition:                   1295
% 15.49/2.52  sup_immediate_simplified:               1037
% 15.49/2.52  sup_given_eliminated:                   0
% 15.49/2.52  comparisons_done:                       0
% 15.49/2.52  comparisons_avoided:                    23
% 15.49/2.52  
% 15.49/2.52  ------ Simplifications
% 15.49/2.52  
% 15.49/2.52  
% 15.49/2.52  sim_fw_subset_subsumed:                 70
% 15.49/2.52  sim_bw_subset_subsumed:                 7
% 15.49/2.52  sim_fw_subsumed:                        35
% 15.49/2.52  sim_bw_subsumed:                        2
% 15.49/2.52  sim_fw_subsumption_res:                 0
% 15.49/2.52  sim_bw_subsumption_res:                 0
% 15.49/2.52  sim_tautology_del:                      4
% 15.49/2.52  sim_eq_tautology_del:                   138
% 15.49/2.52  sim_eq_res_simp:                        0
% 15.49/2.52  sim_fw_demodulated:                     191
% 15.49/2.52  sim_bw_demodulated:                     85
% 15.49/2.52  sim_light_normalised:                   691
% 15.49/2.52  sim_joinable_taut:                      0
% 15.49/2.52  sim_joinable_simp:                      0
% 15.49/2.52  sim_ac_normalised:                      0
% 15.49/2.52  sim_smt_subsumption:                    0
% 15.49/2.52  
%------------------------------------------------------------------------------
