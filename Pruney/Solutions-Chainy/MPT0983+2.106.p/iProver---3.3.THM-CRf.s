%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:07 EST 2020

% Result     : Theorem 31.31s
% Output     : CNFRefutation 31.77s
% Verified   : 
% Statistics : Number of formulae       :  171 ( 619 expanded)
%              Number of clauses        :   94 ( 177 expanded)
%              Number of leaves         :   23 ( 162 expanded)
%              Depth                    :   17
%              Number of atoms          :  546 (4068 expanded)
%              Number of equality atoms :  184 ( 287 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
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
    inference(negated_conjecture,[],[f21])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
     => ( ( ~ v2_funct_2(sK4,X0)
          | ~ v2_funct_1(X2) )
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0))
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK4,X1,X0)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK1)
            | ~ v2_funct_1(sK3) )
          & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X3,sK2,sK1)
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ v2_funct_2(sK4,sK1)
      | ~ v2_funct_1(sK3) )
    & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f46,f52,f51])).

fof(f81,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f82,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f85,plain,(
    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f35])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f18,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f71,f75])).

fof(f20,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f83,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f8,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f88,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f63,f75])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f87,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f61,f75])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f19,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f92,plain,(
    ! [X1] :
      ( v2_funct_2(X1,k2_relat_1(X1))
      | ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f73])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_834,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_837,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_843,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4994,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_837,c_843])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_5455,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4994,c_35])).

cnf(c_5456,plain,
    ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5455])).

cnf(c_5468,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_834,c_5456])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1280,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X3,X4,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1551,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X0,X1,X2,X3,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1280])).

cnf(c_2230,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(X0,X1,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1551])).

cnf(c_3829,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK4)
    | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_2230])).

cnf(c_5622,plain,
    ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5468,c_31,c_29,c_28,c_26,c_3829])).

cnf(c_25,negated_conjecture,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_838,plain,
    ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5625,plain,
    ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5622,c_838])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_849,plain,
    ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3974,plain,
    ( k4_relset_1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_837,c_849])).

cnf(c_4300,plain,
    ( k4_relset_1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_834,c_3974])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_851,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4504,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4300,c_851])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8898,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4504,c_34,c_37])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_847,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_8915,plain,
    ( k5_relat_1(sK3,sK4) = X0
    | r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_8898,c_847])).

cnf(c_129998,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
    | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5625,c_8915])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_9100,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_9103,plain,
    ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9100])).

cnf(c_130802,plain,
    ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_129998,c_9103])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X4)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
    | k1_xboole_0 = X4 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_840,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X3) != iProver_top
    | v1_funct_2(X4,X3,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5627,plain,
    ( sK1 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5622,c_840])).

cnf(c_32,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_33,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_36,plain,
    ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_24,negated_conjecture,
    ( ~ v2_funct_2(sK4,sK1)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_39,plain,
    ( v2_funct_2(sK4,sK1) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_8,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_83,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_85,plain,
    ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_83])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1178,plain,
    ( v5_relat_1(sK4,sK1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1179,plain,
    ( v5_relat_1(sK4,sK1) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1178])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1600,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1))
    | v1_relat_1(sK4) ),
    inference(resolution,[status(thm)],[c_5,c_26])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1728,plain,
    ( v1_relat_1(sK4) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1600,c_6])).

cnf(c_1729,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1728])).

cnf(c_281,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1775,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_281])).

cnf(c_1777,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK1 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1775])).

cnf(c_7,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_2141,plain,
    ( v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_281,c_7])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2309,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(sK1) ),
    inference(resolution,[status(thm)],[c_11,c_29])).

cnf(c_287,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1140,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k6_partfun1(X1))
    | X0 != k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_287])).

cnf(c_3451,plain,
    ( ~ v2_funct_1(k6_partfun1(X0))
    | v2_funct_1(sK3)
    | sK3 != k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_1140])).

cnf(c_3452,plain,
    ( sK3 != k6_partfun1(X0)
    | v2_funct_1(k6_partfun1(X0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3451])).

cnf(c_3454,plain,
    ( sK3 != k6_partfun1(k1_xboole_0)
    | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3452])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1743,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(k6_partfun1(X1))
    | X0 = k6_partfun1(X1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_6235,plain,
    ( ~ v1_xboole_0(k6_partfun1(X0))
    | ~ v1_xboole_0(sK3)
    | sK3 = k6_partfun1(X0) ),
    inference(instantiation,[status(thm)],[c_1743])).

cnf(c_6239,plain,
    ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
    | ~ v1_xboole_0(sK3)
    | sK3 = k6_partfun1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6235])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_842,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3844,plain,
    ( k2_relset_1(sK2,sK1,sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_838,c_842])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_850,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2274,plain,
    ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_837,c_850])).

cnf(c_3869,plain,
    ( k2_relat_1(sK4) = sK1
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | v1_funct_2(sK4,sK2,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3844,c_2274])).

cnf(c_12310,plain,
    ( k2_relat_1(sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3869,c_32,c_33,c_34,c_35,c_36,c_37])).

cnf(c_18,plain,
    ( v2_funct_2(X0,k2_relat_1(X0))
    | ~ v5_relat_1(X0,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_845,plain,
    ( v2_funct_2(X0,k2_relat_1(X0)) = iProver_top
    | v5_relat_1(X0,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_12314,plain,
    ( v2_funct_2(sK4,k2_relat_1(sK4)) = iProver_top
    | v5_relat_1(sK4,sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_12310,c_845])).

cnf(c_12315,plain,
    ( v2_funct_2(sK4,sK1) = iProver_top
    | v5_relat_1(sK4,sK1) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_12314,c_12310])).

cnf(c_75012,plain,
    ( v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5627,c_32,c_33,c_34,c_35,c_36,c_37,c_39,c_85,c_0,c_1179,c_1729,c_1777,c_2141,c_2309,c_3454,c_6239,c_12315])).

cnf(c_130814,plain,
    ( v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_130802,c_75012])).

cnf(c_28131,plain,
    ( v2_funct_1(k6_partfun1(sK1)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_28132,plain,
    ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28131])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_130814,c_28132])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 31.31/4.51  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 31.31/4.51  
% 31.31/4.51  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 31.31/4.51  
% 31.31/4.51  ------  iProver source info
% 31.31/4.51  
% 31.31/4.51  git: date: 2020-06-30 10:37:57 +0100
% 31.31/4.51  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 31.31/4.51  git: non_committed_changes: false
% 31.31/4.51  git: last_make_outside_of_git: false
% 31.31/4.51  
% 31.31/4.51  ------ 
% 31.31/4.51  ------ Parsing...
% 31.31/4.51  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 31.31/4.51  
% 31.31/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 31.31/4.51  
% 31.31/4.51  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 31.31/4.51  
% 31.31/4.51  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 31.31/4.51  ------ Proving...
% 31.31/4.51  ------ Problem Properties 
% 31.31/4.51  
% 31.31/4.51  
% 31.31/4.51  clauses                                 32
% 31.31/4.51  conjectures                             8
% 31.31/4.51  EPR                                     7
% 31.31/4.51  Horn                                    30
% 31.31/4.51  unary                                   13
% 31.31/4.51  binary                                  6
% 31.31/4.51  lits                                    84
% 31.31/4.51  lits eq                                 9
% 31.31/4.51  fd_pure                                 0
% 31.31/4.51  fd_pseudo                               0
% 31.31/4.51  fd_cond                                 1
% 31.31/4.51  fd_pseudo_cond                          3
% 31.31/4.51  AC symbols                              0
% 31.31/4.51  
% 31.31/4.51  ------ Input Options Time Limit: Unbounded
% 31.31/4.51  
% 31.31/4.51  
% 31.31/4.51  ------ 
% 31.31/4.51  Current options:
% 31.31/4.51  ------ 
% 31.31/4.51  
% 31.31/4.51  
% 31.31/4.51  
% 31.31/4.51  
% 31.31/4.51  ------ Proving...
% 31.31/4.51  
% 31.31/4.51  
% 31.31/4.51  % SZS status Theorem for theBenchmark.p
% 31.31/4.51  
% 31.31/4.51  % SZS output start CNFRefutation for theBenchmark.p
% 31.31/4.51  
% 31.31/4.51  fof(f21,conjecture,(
% 31.31/4.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 31.31/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.31/4.51  
% 31.31/4.51  fof(f22,negated_conjecture,(
% 31.31/4.51    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 31.31/4.51    inference(negated_conjecture,[],[f21])).
% 31.31/4.51  
% 31.31/4.51  fof(f45,plain,(
% 31.31/4.51    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 31.31/4.51    inference(ennf_transformation,[],[f22])).
% 31.31/4.51  
% 31.31/4.51  fof(f46,plain,(
% 31.31/4.51    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 31.31/4.51    inference(flattening,[],[f45])).
% 31.31/4.51  
% 31.31/4.51  fof(f52,plain,(
% 31.31/4.51    ( ! [X2,X0,X1] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((~v2_funct_2(sK4,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK4),k6_partfun1(X0)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK4,X1,X0) & v1_funct_1(sK4))) )),
% 31.77/4.51    introduced(choice_axiom,[])).
% 31.77/4.51  
% 31.77/4.51  fof(f51,plain,(
% 31.77/4.51    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,X3),k6_partfun1(sK1)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X3,sK2,sK1) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 31.77/4.51    introduced(choice_axiom,[])).
% 31.77/4.51  
% 31.77/4.51  fof(f53,plain,(
% 31.77/4.51    ((~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)) & r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 31.77/4.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f46,f52,f51])).
% 31.77/4.51  
% 31.77/4.51  fof(f81,plain,(
% 31.77/4.51    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 31.77/4.51    inference(cnf_transformation,[],[f53])).
% 31.77/4.51  
% 31.77/4.51  fof(f84,plain,(
% 31.77/4.51    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 31.77/4.51    inference(cnf_transformation,[],[f53])).
% 31.77/4.51  
% 31.77/4.51  fof(f17,axiom,(
% 31.77/4.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 31.77/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.51  
% 31.77/4.51  fof(f39,plain,(
% 31.77/4.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 31.77/4.51    inference(ennf_transformation,[],[f17])).
% 31.77/4.51  
% 31.77/4.51  fof(f40,plain,(
% 31.77/4.51    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 31.77/4.51    inference(flattening,[],[f39])).
% 31.77/4.51  
% 31.77/4.51  fof(f74,plain,(
% 31.77/4.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 31.77/4.51    inference(cnf_transformation,[],[f40])).
% 31.77/4.51  
% 31.77/4.51  fof(f82,plain,(
% 31.77/4.51    v1_funct_1(sK4)),
% 31.77/4.51    inference(cnf_transformation,[],[f53])).
% 31.77/4.51  
% 31.77/4.51  fof(f79,plain,(
% 31.77/4.51    v1_funct_1(sK3)),
% 31.77/4.51    inference(cnf_transformation,[],[f53])).
% 31.77/4.51  
% 31.77/4.51  fof(f85,plain,(
% 31.77/4.51    r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1))),
% 31.77/4.51    inference(cnf_transformation,[],[f53])).
% 31.77/4.51  
% 31.77/4.51  fof(f13,axiom,(
% 31.77/4.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 31.77/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.51  
% 31.77/4.51  fof(f33,plain,(
% 31.77/4.51    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.77/4.51    inference(ennf_transformation,[],[f13])).
% 31.77/4.51  
% 31.77/4.51  fof(f34,plain,(
% 31.77/4.51    ! [X0,X1,X2,X3,X4,X5] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.51    inference(flattening,[],[f33])).
% 31.77/4.51  
% 31.77/4.51  fof(f68,plain,(
% 31.77/4.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.51    inference(cnf_transformation,[],[f34])).
% 31.77/4.51  
% 31.77/4.51  fof(f11,axiom,(
% 31.77/4.51    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))))),
% 31.77/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.51  
% 31.77/4.51  fof(f30,plain,(
% 31.77/4.51    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.77/4.51    inference(ennf_transformation,[],[f11])).
% 31.77/4.51  
% 31.77/4.51  fof(f31,plain,(
% 31.77/4.51    ! [X0,X1,X2,X3,X4,X5] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.51    inference(flattening,[],[f30])).
% 31.77/4.51  
% 31.77/4.51  fof(f66,plain,(
% 31.77/4.51    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k4_relset_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.51    inference(cnf_transformation,[],[f31])).
% 31.77/4.51  
% 31.77/4.51  fof(f14,axiom,(
% 31.77/4.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 31.77/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.51  
% 31.77/4.51  fof(f35,plain,(
% 31.77/4.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 31.77/4.51    inference(ennf_transformation,[],[f14])).
% 31.77/4.51  
% 31.77/4.51  fof(f36,plain,(
% 31.77/4.51    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.51    inference(flattening,[],[f35])).
% 31.77/4.51  
% 31.77/4.51  fof(f49,plain,(
% 31.77/4.51    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.51    inference(nnf_transformation,[],[f36])).
% 31.77/4.51  
% 31.77/4.51  fof(f69,plain,(
% 31.77/4.51    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.51    inference(cnf_transformation,[],[f49])).
% 31.77/4.51  
% 31.77/4.51  fof(f15,axiom,(
% 31.77/4.51    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 31.77/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.51  
% 31.77/4.51  fof(f71,plain,(
% 31.77/4.51    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 31.77/4.51    inference(cnf_transformation,[],[f15])).
% 31.77/4.51  
% 31.77/4.51  fof(f18,axiom,(
% 31.77/4.51    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 31.77/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.51  
% 31.77/4.51  fof(f75,plain,(
% 31.77/4.51    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 31.77/4.51    inference(cnf_transformation,[],[f18])).
% 31.77/4.51  
% 31.77/4.51  fof(f90,plain,(
% 31.77/4.51    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 31.77/4.51    inference(definition_unfolding,[],[f71,f75])).
% 31.77/4.51  
% 31.77/4.51  fof(f20,axiom,(
% 31.77/4.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 31.77/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.51  
% 31.77/4.51  fof(f43,plain,(
% 31.77/4.51    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 31.77/4.51    inference(ennf_transformation,[],[f20])).
% 31.77/4.51  
% 31.77/4.51  fof(f44,plain,(
% 31.77/4.51    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 31.77/4.51    inference(flattening,[],[f43])).
% 31.77/4.51  
% 31.77/4.51  fof(f77,plain,(
% 31.77/4.51    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 31.77/4.51    inference(cnf_transformation,[],[f44])).
% 31.77/4.51  
% 31.77/4.51  fof(f80,plain,(
% 31.77/4.51    v1_funct_2(sK3,sK1,sK2)),
% 31.77/4.51    inference(cnf_transformation,[],[f53])).
% 31.77/4.51  
% 31.77/4.51  fof(f83,plain,(
% 31.77/4.51    v1_funct_2(sK4,sK2,sK1)),
% 31.77/4.51    inference(cnf_transformation,[],[f53])).
% 31.77/4.51  
% 31.77/4.51  fof(f86,plain,(
% 31.77/4.51    ~v2_funct_2(sK4,sK1) | ~v2_funct_1(sK3)),
% 31.77/4.51    inference(cnf_transformation,[],[f53])).
% 31.77/4.51  
% 31.77/4.51  fof(f8,axiom,(
% 31.77/4.51    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 31.77/4.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.51  
% 31.77/4.51  fof(f63,plain,(
% 31.77/4.51    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 31.77/4.51    inference(cnf_transformation,[],[f8])).
% 31.77/4.52  
% 31.77/4.52  fof(f88,plain,(
% 31.77/4.52    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 31.77/4.52    inference(definition_unfolding,[],[f63,f75])).
% 31.77/4.52  
% 31.77/4.52  fof(f1,axiom,(
% 31.77/4.52    v1_xboole_0(k1_xboole_0)),
% 31.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.52  
% 31.77/4.52  fof(f54,plain,(
% 31.77/4.52    v1_xboole_0(k1_xboole_0)),
% 31.77/4.52    inference(cnf_transformation,[],[f1])).
% 31.77/4.52  
% 31.77/4.52  fof(f9,axiom,(
% 31.77/4.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 31.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.52  
% 31.77/4.52  fof(f23,plain,(
% 31.77/4.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 31.77/4.52    inference(pure_predicate_removal,[],[f9])).
% 31.77/4.52  
% 31.77/4.52  fof(f28,plain,(
% 31.77/4.52    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.52    inference(ennf_transformation,[],[f23])).
% 31.77/4.52  
% 31.77/4.52  fof(f64,plain,(
% 31.77/4.52    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.52    inference(cnf_transformation,[],[f28])).
% 31.77/4.52  
% 31.77/4.52  fof(f5,axiom,(
% 31.77/4.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 31.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.52  
% 31.77/4.52  fof(f27,plain,(
% 31.77/4.52    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 31.77/4.52    inference(ennf_transformation,[],[f5])).
% 31.77/4.52  
% 31.77/4.52  fof(f59,plain,(
% 31.77/4.52    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 31.77/4.52    inference(cnf_transformation,[],[f27])).
% 31.77/4.52  
% 31.77/4.52  fof(f6,axiom,(
% 31.77/4.52    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 31.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.52  
% 31.77/4.52  fof(f60,plain,(
% 31.77/4.52    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 31.77/4.52    inference(cnf_transformation,[],[f6])).
% 31.77/4.52  
% 31.77/4.52  fof(f7,axiom,(
% 31.77/4.52    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 31.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.52  
% 31.77/4.52  fof(f61,plain,(
% 31.77/4.52    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 31.77/4.52    inference(cnf_transformation,[],[f7])).
% 31.77/4.52  
% 31.77/4.52  fof(f87,plain,(
% 31.77/4.52    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 31.77/4.52    inference(definition_unfolding,[],[f61,f75])).
% 31.77/4.52  
% 31.77/4.52  fof(f10,axiom,(
% 31.77/4.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 31.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.52  
% 31.77/4.52  fof(f29,plain,(
% 31.77/4.52    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 31.77/4.52    inference(ennf_transformation,[],[f10])).
% 31.77/4.52  
% 31.77/4.52  fof(f65,plain,(
% 31.77/4.52    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 31.77/4.52    inference(cnf_transformation,[],[f29])).
% 31.77/4.52  
% 31.77/4.52  fof(f2,axiom,(
% 31.77/4.52    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 31.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.52  
% 31.77/4.52  fof(f24,plain,(
% 31.77/4.52    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 31.77/4.52    inference(ennf_transformation,[],[f2])).
% 31.77/4.52  
% 31.77/4.52  fof(f55,plain,(
% 31.77/4.52    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 31.77/4.52    inference(cnf_transformation,[],[f24])).
% 31.77/4.52  
% 31.77/4.52  fof(f19,axiom,(
% 31.77/4.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 31.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.52  
% 31.77/4.52  fof(f41,plain,(
% 31.77/4.52    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 31.77/4.52    inference(ennf_transformation,[],[f19])).
% 31.77/4.52  
% 31.77/4.52  fof(f42,plain,(
% 31.77/4.52    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 31.77/4.52    inference(flattening,[],[f41])).
% 31.77/4.52  
% 31.77/4.52  fof(f76,plain,(
% 31.77/4.52    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 31.77/4.52    inference(cnf_transformation,[],[f42])).
% 31.77/4.52  
% 31.77/4.52  fof(f12,axiom,(
% 31.77/4.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 31.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.52  
% 31.77/4.52  fof(f32,plain,(
% 31.77/4.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 31.77/4.52    inference(ennf_transformation,[],[f12])).
% 31.77/4.52  
% 31.77/4.52  fof(f67,plain,(
% 31.77/4.52    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 31.77/4.52    inference(cnf_transformation,[],[f32])).
% 31.77/4.52  
% 31.77/4.52  fof(f16,axiom,(
% 31.77/4.52    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 31.77/4.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 31.77/4.52  
% 31.77/4.52  fof(f37,plain,(
% 31.77/4.52    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 31.77/4.52    inference(ennf_transformation,[],[f16])).
% 31.77/4.52  
% 31.77/4.52  fof(f38,plain,(
% 31.77/4.52    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.77/4.52    inference(flattening,[],[f37])).
% 31.77/4.52  
% 31.77/4.52  fof(f50,plain,(
% 31.77/4.52    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 31.77/4.52    inference(nnf_transformation,[],[f38])).
% 31.77/4.52  
% 31.77/4.52  fof(f73,plain,(
% 31.77/4.52    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 31.77/4.52    inference(cnf_transformation,[],[f50])).
% 31.77/4.52  
% 31.77/4.52  fof(f92,plain,(
% 31.77/4.52    ( ! [X1] : (v2_funct_2(X1,k2_relat_1(X1)) | ~v5_relat_1(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 31.77/4.52    inference(equality_resolution,[],[f73])).
% 31.77/4.52  
% 31.77/4.52  cnf(c_29,negated_conjecture,
% 31.77/4.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 31.77/4.52      inference(cnf_transformation,[],[f81]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_834,plain,
% 31.77/4.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_26,negated_conjecture,
% 31.77/4.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 31.77/4.52      inference(cnf_transformation,[],[f84]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_837,plain,
% 31.77/4.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_20,plain,
% 31.77/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.77/4.52      | ~ v1_funct_1(X0)
% 31.77/4.52      | ~ v1_funct_1(X3)
% 31.77/4.52      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 31.77/4.52      inference(cnf_transformation,[],[f74]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_843,plain,
% 31.77/4.52      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 31.77/4.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 31.77/4.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.77/4.52      | v1_funct_1(X4) != iProver_top
% 31.77/4.52      | v1_funct_1(X5) != iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_4994,plain,
% 31.77/4.52      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 31.77/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.77/4.52      | v1_funct_1(X2) != iProver_top
% 31.77/4.52      | v1_funct_1(sK4) != iProver_top ),
% 31.77/4.52      inference(superposition,[status(thm)],[c_837,c_843]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_28,negated_conjecture,
% 31.77/4.52      ( v1_funct_1(sK4) ),
% 31.77/4.52      inference(cnf_transformation,[],[f82]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_35,plain,
% 31.77/4.52      ( v1_funct_1(sK4) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_5455,plain,
% 31.77/4.52      ( v1_funct_1(X2) != iProver_top
% 31.77/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.77/4.52      | k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4) ),
% 31.77/4.52      inference(global_propositional_subsumption,
% 31.77/4.52                [status(thm)],
% 31.77/4.52                [c_4994,c_35]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_5456,plain,
% 31.77/4.52      ( k1_partfun1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 31.77/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.77/4.52      | v1_funct_1(X2) != iProver_top ),
% 31.77/4.52      inference(renaming,[status(thm)],[c_5455]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_5468,plain,
% 31.77/4.52      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4)
% 31.77/4.52      | v1_funct_1(sK3) != iProver_top ),
% 31.77/4.52      inference(superposition,[status(thm)],[c_834,c_5456]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_31,negated_conjecture,
% 31.77/4.52      ( v1_funct_1(sK3) ),
% 31.77/4.52      inference(cnf_transformation,[],[f79]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1280,plain,
% 31.77/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.52      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 31.77/4.52      | ~ v1_funct_1(X0)
% 31.77/4.52      | ~ v1_funct_1(sK3)
% 31.77/4.52      | k1_partfun1(X3,X4,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_20]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1551,plain,
% 31.77/4.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.77/4.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 31.77/4.52      | ~ v1_funct_1(sK3)
% 31.77/4.52      | ~ v1_funct_1(sK4)
% 31.77/4.52      | k1_partfun1(X0,X1,X2,X3,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_1280]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_2230,plain,
% 31.77/4.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.77/4.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.77/4.52      | ~ v1_funct_1(sK3)
% 31.77/4.52      | ~ v1_funct_1(sK4)
% 31.77/4.52      | k1_partfun1(X0,X1,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_1551]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_3829,plain,
% 31.77/4.52      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 31.77/4.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 31.77/4.52      | ~ v1_funct_1(sK3)
% 31.77/4.52      | ~ v1_funct_1(sK4)
% 31.77/4.52      | k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_2230]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_5622,plain,
% 31.77/4.52      ( k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 31.77/4.52      inference(global_propositional_subsumption,
% 31.77/4.52                [status(thm)],
% 31.77/4.52                [c_5468,c_31,c_29,c_28,c_26,c_3829]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_25,negated_conjecture,
% 31.77/4.52      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) ),
% 31.77/4.52      inference(cnf_transformation,[],[f85]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_838,plain,
% 31.77/4.52      ( r2_relset_1(sK1,sK1,k1_partfun1(sK1,sK2,sK2,sK1,sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_5625,plain,
% 31.77/4.52      ( r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),k6_partfun1(sK1)) = iProver_top ),
% 31.77/4.52      inference(demodulation,[status(thm)],[c_5622,c_838]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_14,plain,
% 31.77/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.77/4.52      | k4_relset_1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 31.77/4.52      inference(cnf_transformation,[],[f68]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_849,plain,
% 31.77/4.52      ( k4_relset_1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 31.77/4.52      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 31.77/4.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_3974,plain,
% 31.77/4.52      ( k4_relset_1(X0,X1,sK2,sK1,X2,sK4) = k5_relat_1(X2,sK4)
% 31.77/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.77/4.52      inference(superposition,[status(thm)],[c_837,c_849]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_4300,plain,
% 31.77/4.52      ( k4_relset_1(sK1,sK2,sK2,sK1,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 31.77/4.52      inference(superposition,[status(thm)],[c_834,c_3974]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_12,plain,
% 31.77/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 31.77/4.52      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) ),
% 31.77/4.52      inference(cnf_transformation,[],[f66]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_851,plain,
% 31.77/4.52      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 31.77/4.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 31.77/4.52      | m1_subset_1(k4_relset_1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_4504,plain,
% 31.77/4.52      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top
% 31.77/4.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 31.77/4.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 31.77/4.52      inference(superposition,[status(thm)],[c_4300,c_851]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_34,plain,
% 31.77/4.52      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_37,plain,
% 31.77/4.52      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_8898,plain,
% 31.77/4.52      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 31.77/4.52      inference(global_propositional_subsumption,
% 31.77/4.52                [status(thm)],
% 31.77/4.52                [c_4504,c_34,c_37]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_16,plain,
% 31.77/4.52      ( ~ r2_relset_1(X0,X1,X2,X3)
% 31.77/4.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.77/4.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.77/4.52      | X3 = X2 ),
% 31.77/4.52      inference(cnf_transformation,[],[f69]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_847,plain,
% 31.77/4.52      ( X0 = X1
% 31.77/4.52      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 31.77/4.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 31.77/4.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_8915,plain,
% 31.77/4.52      ( k5_relat_1(sK3,sK4) = X0
% 31.77/4.52      | r2_relset_1(sK1,sK1,k5_relat_1(sK3,sK4),X0) != iProver_top
% 31.77/4.52      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 31.77/4.52      inference(superposition,[status(thm)],[c_8898,c_847]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_129998,plain,
% 31.77/4.52      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1)
% 31.77/4.52      | m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) != iProver_top ),
% 31.77/4.52      inference(superposition,[status(thm)],[c_5625,c_8915]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_17,plain,
% 31.77/4.52      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 31.77/4.52      inference(cnf_transformation,[],[f90]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_9100,plain,
% 31.77/4.52      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_17]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_9103,plain,
% 31.77/4.52      ( m1_subset_1(k6_partfun1(sK1),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_9100]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_130802,plain,
% 31.77/4.52      ( k5_relat_1(sK3,sK4) = k6_partfun1(sK1) ),
% 31.77/4.52      inference(global_propositional_subsumption,
% 31.77/4.52                [status(thm)],
% 31.77/4.52                [c_129998,c_9103]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_23,plain,
% 31.77/4.52      ( ~ v1_funct_2(X0,X1,X2)
% 31.77/4.52      | ~ v1_funct_2(X3,X2,X4)
% 31.77/4.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X4)))
% 31.77/4.52      | ~ v1_funct_1(X3)
% 31.77/4.52      | ~ v1_funct_1(X0)
% 31.77/4.52      | v2_funct_1(X0)
% 31.77/4.52      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X4,X0,X3))
% 31.77/4.52      | k1_xboole_0 = X4 ),
% 31.77/4.52      inference(cnf_transformation,[],[f77]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_840,plain,
% 31.77/4.52      ( k1_xboole_0 = X0
% 31.77/4.52      | v1_funct_2(X1,X2,X3) != iProver_top
% 31.77/4.52      | v1_funct_2(X4,X3,X0) != iProver_top
% 31.77/4.52      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 31.77/4.52      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 31.77/4.52      | v1_funct_1(X4) != iProver_top
% 31.77/4.52      | v1_funct_1(X1) != iProver_top
% 31.77/4.52      | v2_funct_1(X1) = iProver_top
% 31.77/4.52      | v2_funct_1(k1_partfun1(X2,X3,X3,X0,X1,X4)) != iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_5627,plain,
% 31.77/4.52      ( sK1 = k1_xboole_0
% 31.77/4.52      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 31.77/4.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.77/4.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 31.77/4.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.77/4.52      | v1_funct_1(sK3) != iProver_top
% 31.77/4.52      | v1_funct_1(sK4) != iProver_top
% 31.77/4.52      | v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top
% 31.77/4.52      | v2_funct_1(sK3) = iProver_top ),
% 31.77/4.52      inference(superposition,[status(thm)],[c_5622,c_840]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_32,plain,
% 31.77/4.52      ( v1_funct_1(sK3) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_30,negated_conjecture,
% 31.77/4.52      ( v1_funct_2(sK3,sK1,sK2) ),
% 31.77/4.52      inference(cnf_transformation,[],[f80]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_33,plain,
% 31.77/4.52      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_27,negated_conjecture,
% 31.77/4.52      ( v1_funct_2(sK4,sK2,sK1) ),
% 31.77/4.52      inference(cnf_transformation,[],[f83]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_36,plain,
% 31.77/4.52      ( v1_funct_2(sK4,sK2,sK1) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_24,negated_conjecture,
% 31.77/4.52      ( ~ v2_funct_2(sK4,sK1) | ~ v2_funct_1(sK3) ),
% 31.77/4.52      inference(cnf_transformation,[],[f86]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_39,plain,
% 31.77/4.52      ( v2_funct_2(sK4,sK1) != iProver_top
% 31.77/4.52      | v2_funct_1(sK3) != iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_8,plain,
% 31.77/4.52      ( v2_funct_1(k6_partfun1(X0)) ),
% 31.77/4.52      inference(cnf_transformation,[],[f88]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_83,plain,
% 31.77/4.52      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_85,plain,
% 31.77/4.52      ( v2_funct_1(k6_partfun1(k1_xboole_0)) = iProver_top ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_83]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_0,plain,
% 31.77/4.52      ( v1_xboole_0(k1_xboole_0) ),
% 31.77/4.52      inference(cnf_transformation,[],[f54]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_10,plain,
% 31.77/4.52      ( v5_relat_1(X0,X1)
% 31.77/4.52      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 31.77/4.52      inference(cnf_transformation,[],[f64]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1178,plain,
% 31.77/4.52      ( v5_relat_1(sK4,sK1)
% 31.77/4.52      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_10]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1179,plain,
% 31.77/4.52      ( v5_relat_1(sK4,sK1) = iProver_top
% 31.77/4.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_1178]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_5,plain,
% 31.77/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 31.77/4.52      | ~ v1_relat_1(X1)
% 31.77/4.52      | v1_relat_1(X0) ),
% 31.77/4.52      inference(cnf_transformation,[],[f59]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1600,plain,
% 31.77/4.52      ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK1)) | v1_relat_1(sK4) ),
% 31.77/4.52      inference(resolution,[status(thm)],[c_5,c_26]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_6,plain,
% 31.77/4.52      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 31.77/4.52      inference(cnf_transformation,[],[f60]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1728,plain,
% 31.77/4.52      ( v1_relat_1(sK4) ),
% 31.77/4.52      inference(forward_subsumption_resolution,
% 31.77/4.52                [status(thm)],
% 31.77/4.52                [c_1600,c_6]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1729,plain,
% 31.77/4.52      ( v1_relat_1(sK4) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_1728]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_281,plain,
% 31.77/4.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 31.77/4.52      theory(equality) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1775,plain,
% 31.77/4.52      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_281]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1777,plain,
% 31.77/4.52      ( v1_xboole_0(sK1)
% 31.77/4.52      | ~ v1_xboole_0(k1_xboole_0)
% 31.77/4.52      | sK1 != k1_xboole_0 ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_1775]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_7,plain,
% 31.77/4.52      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 31.77/4.52      inference(cnf_transformation,[],[f87]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_2141,plain,
% 31.77/4.52      ( v1_xboole_0(k6_partfun1(k1_xboole_0))
% 31.77/4.52      | ~ v1_xboole_0(k1_xboole_0) ),
% 31.77/4.52      inference(resolution,[status(thm)],[c_281,c_7]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_11,plain,
% 31.77/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.52      | ~ v1_xboole_0(X1)
% 31.77/4.52      | v1_xboole_0(X0) ),
% 31.77/4.52      inference(cnf_transformation,[],[f65]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_2309,plain,
% 31.77/4.52      ( v1_xboole_0(sK3) | ~ v1_xboole_0(sK1) ),
% 31.77/4.52      inference(resolution,[status(thm)],[c_11,c_29]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_287,plain,
% 31.77/4.52      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 31.77/4.52      theory(equality) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1140,plain,
% 31.77/4.52      ( v2_funct_1(X0)
% 31.77/4.52      | ~ v2_funct_1(k6_partfun1(X1))
% 31.77/4.52      | X0 != k6_partfun1(X1) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_287]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_3451,plain,
% 31.77/4.52      ( ~ v2_funct_1(k6_partfun1(X0))
% 31.77/4.52      | v2_funct_1(sK3)
% 31.77/4.52      | sK3 != k6_partfun1(X0) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_1140]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_3452,plain,
% 31.77/4.52      ( sK3 != k6_partfun1(X0)
% 31.77/4.52      | v2_funct_1(k6_partfun1(X0)) != iProver_top
% 31.77/4.52      | v2_funct_1(sK3) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_3451]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_3454,plain,
% 31.77/4.52      ( sK3 != k6_partfun1(k1_xboole_0)
% 31.77/4.52      | v2_funct_1(k6_partfun1(k1_xboole_0)) != iProver_top
% 31.77/4.52      | v2_funct_1(sK3) = iProver_top ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_3452]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1,plain,
% 31.77/4.52      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 31.77/4.52      inference(cnf_transformation,[],[f55]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_1743,plain,
% 31.77/4.52      ( ~ v1_xboole_0(X0)
% 31.77/4.52      | ~ v1_xboole_0(k6_partfun1(X1))
% 31.77/4.52      | X0 = k6_partfun1(X1) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_1]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_6235,plain,
% 31.77/4.52      ( ~ v1_xboole_0(k6_partfun1(X0))
% 31.77/4.52      | ~ v1_xboole_0(sK3)
% 31.77/4.52      | sK3 = k6_partfun1(X0) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_1743]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_6239,plain,
% 31.77/4.52      ( ~ v1_xboole_0(k6_partfun1(k1_xboole_0))
% 31.77/4.52      | ~ v1_xboole_0(sK3)
% 31.77/4.52      | sK3 = k6_partfun1(k1_xboole_0) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_6235]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_21,plain,
% 31.77/4.52      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 31.77/4.52      | ~ v1_funct_2(X2,X0,X1)
% 31.77/4.52      | ~ v1_funct_2(X3,X1,X0)
% 31.77/4.52      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 31.77/4.52      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 31.77/4.52      | ~ v1_funct_1(X2)
% 31.77/4.52      | ~ v1_funct_1(X3)
% 31.77/4.52      | k2_relset_1(X1,X0,X3) = X0 ),
% 31.77/4.52      inference(cnf_transformation,[],[f76]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_842,plain,
% 31.77/4.52      ( k2_relset_1(X0,X1,X2) = X1
% 31.77/4.52      | r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) != iProver_top
% 31.77/4.52      | v1_funct_2(X3,X1,X0) != iProver_top
% 31.77/4.52      | v1_funct_2(X2,X0,X1) != iProver_top
% 31.77/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 31.77/4.52      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 31.77/4.52      | v1_funct_1(X2) != iProver_top
% 31.77/4.52      | v1_funct_1(X3) != iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_3844,plain,
% 31.77/4.52      ( k2_relset_1(sK2,sK1,sK4) = sK1
% 31.77/4.52      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 31.77/4.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.77/4.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 31.77/4.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.77/4.52      | v1_funct_1(sK3) != iProver_top
% 31.77/4.52      | v1_funct_1(sK4) != iProver_top ),
% 31.77/4.52      inference(superposition,[status(thm)],[c_838,c_842]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_13,plain,
% 31.77/4.52      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 31.77/4.52      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 31.77/4.52      inference(cnf_transformation,[],[f67]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_850,plain,
% 31.77/4.52      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 31.77/4.52      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_2274,plain,
% 31.77/4.52      ( k2_relset_1(sK2,sK1,sK4) = k2_relat_1(sK4) ),
% 31.77/4.52      inference(superposition,[status(thm)],[c_837,c_850]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_3869,plain,
% 31.77/4.52      ( k2_relat_1(sK4) = sK1
% 31.77/4.52      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 31.77/4.52      | v1_funct_2(sK4,sK2,sK1) != iProver_top
% 31.77/4.52      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 31.77/4.52      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 31.77/4.52      | v1_funct_1(sK3) != iProver_top
% 31.77/4.52      | v1_funct_1(sK4) != iProver_top ),
% 31.77/4.52      inference(demodulation,[status(thm)],[c_3844,c_2274]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_12310,plain,
% 31.77/4.52      ( k2_relat_1(sK4) = sK1 ),
% 31.77/4.52      inference(global_propositional_subsumption,
% 31.77/4.52                [status(thm)],
% 31.77/4.52                [c_3869,c_32,c_33,c_34,c_35,c_36,c_37]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_18,plain,
% 31.77/4.52      ( v2_funct_2(X0,k2_relat_1(X0))
% 31.77/4.52      | ~ v5_relat_1(X0,k2_relat_1(X0))
% 31.77/4.52      | ~ v1_relat_1(X0) ),
% 31.77/4.52      inference(cnf_transformation,[],[f92]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_845,plain,
% 31.77/4.52      ( v2_funct_2(X0,k2_relat_1(X0)) = iProver_top
% 31.77/4.52      | v5_relat_1(X0,k2_relat_1(X0)) != iProver_top
% 31.77/4.52      | v1_relat_1(X0) != iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_12314,plain,
% 31.77/4.52      ( v2_funct_2(sK4,k2_relat_1(sK4)) = iProver_top
% 31.77/4.52      | v5_relat_1(sK4,sK1) != iProver_top
% 31.77/4.52      | v1_relat_1(sK4) != iProver_top ),
% 31.77/4.52      inference(superposition,[status(thm)],[c_12310,c_845]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_12315,plain,
% 31.77/4.52      ( v2_funct_2(sK4,sK1) = iProver_top
% 31.77/4.52      | v5_relat_1(sK4,sK1) != iProver_top
% 31.77/4.52      | v1_relat_1(sK4) != iProver_top ),
% 31.77/4.52      inference(light_normalisation,[status(thm)],[c_12314,c_12310]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_75012,plain,
% 31.77/4.52      ( v2_funct_1(k5_relat_1(sK3,sK4)) != iProver_top ),
% 31.77/4.52      inference(global_propositional_subsumption,
% 31.77/4.52                [status(thm)],
% 31.77/4.52                [c_5627,c_32,c_33,c_34,c_35,c_36,c_37,c_39,c_85,c_0,
% 31.77/4.52                 c_1179,c_1729,c_1777,c_2141,c_2309,c_3454,c_6239,
% 31.77/4.52                 c_12315]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_130814,plain,
% 31.77/4.52      ( v2_funct_1(k6_partfun1(sK1)) != iProver_top ),
% 31.77/4.52      inference(demodulation,[status(thm)],[c_130802,c_75012]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_28131,plain,
% 31.77/4.52      ( v2_funct_1(k6_partfun1(sK1)) ),
% 31.77/4.52      inference(instantiation,[status(thm)],[c_8]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(c_28132,plain,
% 31.77/4.52      ( v2_funct_1(k6_partfun1(sK1)) = iProver_top ),
% 31.77/4.52      inference(predicate_to_equality,[status(thm)],[c_28131]) ).
% 31.77/4.52  
% 31.77/4.52  cnf(contradiction,plain,
% 31.77/4.52      ( $false ),
% 31.77/4.52      inference(minisat,[status(thm)],[c_130814,c_28132]) ).
% 31.77/4.52  
% 31.77/4.52  
% 31.77/4.52  % SZS output end CNFRefutation for theBenchmark.p
% 31.77/4.52  
% 31.77/4.52  ------                               Statistics
% 31.77/4.52  
% 31.77/4.52  ------ Selected
% 31.77/4.52  
% 31.77/4.52  total_time:                             4.001
% 31.77/4.52  
%------------------------------------------------------------------------------
