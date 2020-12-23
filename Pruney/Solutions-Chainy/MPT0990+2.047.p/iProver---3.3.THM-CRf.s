%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:06 EST 2020

% Result     : Theorem 39.48s
% Output     : CNFRefutation 39.48s
% Verified   : 
% Statistics : Number of formulae       :  290 (4054 expanded)
%              Number of clauses        :  216 (1138 expanded)
%              Number of leaves         :   19 (1038 expanded)
%              Depth                    :   28
%              Number of atoms          : 1099 (35353 expanded)
%              Number of equality atoms :  686 (13212 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f36])).

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40])).

fof(f69,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f72,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f10,axiom,(
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

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f10])).

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
    inference(flattening,[],[f28])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f71,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f42])).

fof(f2,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f30])).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f26])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f74,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f55,f65])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f64,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f79,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f44,f65])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f47,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f82,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f65])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

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
    inference(definition_unfolding,[],[f49,f65])).

fof(f14,axiom,(
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

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f68,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f78,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_100228,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_100240,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_100825,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_100228,c_100240])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_100827,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_100825,c_28])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_100231,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_100233,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_101181,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_100231,c_100233])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_100241,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_100858,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_100231,c_100241])).

cnf(c_101193,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_101181,c_100858])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_39,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_25,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_657,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_686,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_658,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_7603,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_658])).

cnf(c_7604,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7603])).

cnf(c_24506,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_24507,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_24559,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_24506,c_24507])).

cnf(c_24508,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_24550,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_24506,c_24508])).

cnf(c_24560,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_24559,c_24550])).

cnf(c_105173,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_101193,c_39,c_25,c_686,c_7604,c_24560])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_100247,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_105185,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_105173,c_100247])).

cnf(c_64912,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_64577,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1)))
    | ~ iProver_ARSWP_238 ),
    inference(arg_filter_abstr,[status(unp)],[c_29])).

cnf(c_64890,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1))) = iProver_top
    | iProver_ARSWP_238 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64577])).

cnf(c_64573,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_234
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(arg_filter_abstr,[status(unp)],[c_18])).

cnf(c_64894,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
    | iProver_ARSWP_234 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64573])).

cnf(c_66353,plain,
    ( k1_relset_1(sK1,X0,sK3) = sK1
    | k1_xboole_0 = X0
    | v1_funct_2(sK3,sK1,X0) != iProver_top
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_234 != iProver_top ),
    inference(superposition,[status(thm)],[c_64890,c_64894])).

cnf(c_68104,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_234 != iProver_top ),
    inference(superposition,[status(thm)],[c_64912,c_66353])).

cnf(c_24539,plain,
    ( ~ v1_funct_2(sK3,sK1,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | k1_relset_1(sK1,sK0,sK3) = sK1
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_68139,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_68104,c_30,c_29,c_25,c_24539])).

cnf(c_64565,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
    | ~ iProver_ARSWP_226
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(arg_filter_abstr,[status(unp)],[c_8])).

cnf(c_64902,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_64565])).

cnf(c_65948,plain,
    ( k1_relset_1(sK1,X0,sK3) = k1_relat_1(sK3)
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(superposition,[status(thm)],[c_64890,c_64902])).

cnf(c_68144,plain,
    ( k1_relat_1(sK3) = sK1
    | iProver_ARSWP_238 != iProver_top
    | iProver_ARSWP_226 != iProver_top ),
    inference(superposition,[status(thm)],[c_68139,c_65948])).

cnf(c_68402,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_68144,c_39,c_25,c_686,c_7604,c_24560])).

cnf(c_64918,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_68435,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_68402,c_64918])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_42039,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_42040,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42039])).

cnf(c_68946,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_68435,c_38,c_40,c_42040])).

cnf(c_68947,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_68946])).

cnf(c_131144,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_105185,c_38,c_40,c_42040,c_68435])).

cnf(c_131145,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_131144])).

cnf(c_131154,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_100827,c_131145])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_99931,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ iProver_ARSWP_245 ),
    inference(arg_filter_abstr,[status(unp)],[c_19])).

cnf(c_100220,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99931])).

cnf(c_102120,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(superposition,[status(thm)],[c_100231,c_100220])).

cnf(c_102261,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_102120,c_38])).

cnf(c_102262,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(renaming,[status(thm)],[c_102261])).

cnf(c_102273,plain,
    ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(superposition,[status(thm)],[c_100228,c_102262])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_102420,plain,
    ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_102273,c_35])).

cnf(c_11,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_27,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_385,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_386,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_12,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_394,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_386,c_12])).

cnf(c_99935,plain,
    ( ~ m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ iProver_ARSWP_249
    | k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
    inference(arg_filter_abstr,[status(unp)],[c_394])).

cnf(c_100216,plain,
    ( k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | iProver_ARSWP_249 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99935])).

cnf(c_102439,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
    | iProver_ARSWP_249 != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(superposition,[status(thm)],[c_102420,c_100216])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_99933,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | ~ iProver_ARSWP_247
    | arAF1_k1_partfun1_0_1_2(X4,X5) = k5_relat_1(X3,X0) ),
    inference(arg_filter_abstr,[status(unp)],[c_21])).

cnf(c_100218,plain,
    ( arAF1_k1_partfun1_0_1_2(X0,X1) = k5_relat_1(X2,X3)
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99933])).

cnf(c_101032,plain,
    ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_100228,c_100218])).

cnf(c_101380,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_101032,c_35])).

cnf(c_101381,plain,
    ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(renaming,[status(thm)],[c_101380])).

cnf(c_101391,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_100231,c_101381])).

cnf(c_101446,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_101391,c_38])).

cnf(c_103355,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | iProver_ARSWP_249 != iProver_top
    | iProver_ARSWP_247 != iProver_top
    | iProver_ARSWP_245 != iProver_top ),
    inference(superposition,[status(thm)],[c_102439,c_101446])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_60510,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_60513,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_60515,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_60907,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_60513,c_60515])).

cnf(c_60976,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_60907,c_38])).

cnf(c_60977,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_60976])).

cnf(c_60988,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_60510,c_60977])).

cnf(c_60634,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3)
    | k1_partfun1(X1,X2,sK1,sK0,X0,sK3) = k5_relat_1(X0,sK3) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_60727,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(instantiation,[status(thm)],[c_60634])).

cnf(c_61063,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_60988,c_34,c_32,c_31,c_29,c_60727])).

cnf(c_60507,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_61066,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_61063,c_60507])).

cnf(c_60516,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_61068,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_61063,c_60516])).

cnf(c_107055,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_103355,c_35,c_37,c_38,c_40,c_61066,c_61068])).

cnf(c_131189,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_131154,c_107055])).

cnf(c_60667,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_60668,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60667])).

cnf(c_131311,plain,
    ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_131189,c_35,c_37,c_60668])).

cnf(c_0,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_100249,plain,
    ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_131317,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_131311,c_100249])).

cnf(c_100229,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v2_funct_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_100244,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_101106,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_100229,c_100244])).

cnf(c_41921,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_41931,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_42118,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_41921,c_41931])).

cnf(c_101258,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_101106,c_40,c_42040,c_42118])).

cnf(c_105176,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_105173,c_101258])).

cnf(c_131319,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_131317,c_105176])).

cnf(c_101392,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
    | v1_funct_1(sK2) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_100228,c_101381])).

cnf(c_101767,plain,
    ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
    | iProver_ARSWP_247 != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_101392,c_35])).

cnf(c_101773,plain,
    ( k5_relat_1(sK2,sK2) = k5_relat_1(sK2,sK3)
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_101446,c_101767])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_100243,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_102080,plain,
    ( k5_relat_1(sK2,sK2) != k6_partfun1(k2_relat_1(sK3))
    | k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(superposition,[status(thm)],[c_101773,c_100243])).

cnf(c_100824,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_100231,c_100240])).

cnf(c_22,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X3,X1,X0)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_398,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X0)
    | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X2,X1,X3) = X1
    | k6_partfun1(X1) != k6_partfun1(sK0)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_399,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X0)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_483,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_399])).

cnf(c_99936,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | ~ iProver_ARSWP_250
    | k2_relset_1(X1,sK0,X0) = sK0
    | arAF1_k1_partfun1_0_1_2(sK0,X1) != arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
    inference(arg_filter_abstr,[status(unp)],[c_483])).

cnf(c_100215,plain,
    ( k2_relset_1(X0,sK0,X1) = sK0
    | arAF1_k1_partfun1_0_1_2(sK0,X0) != arAF1_k1_partfun1_0_1_2(sK0,sK1)
    | v1_funct_2(X1,X0,sK0) != iProver_top
    | v1_funct_2(X2,sK0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_99936])).

cnf(c_100589,plain,
    ( k2_relset_1(sK1,sK0,X0) = sK0
    | v1_funct_2(X1,sK0,sK1) != iProver_top
    | v1_funct_2(X0,sK1,sK0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_100215])).

cnf(c_100650,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(X0,sK0,sK1) != iProver_top
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | iProver_ARSWP_250 != iProver_top ),
    inference(superposition,[status(thm)],[c_100231,c_100589])).

cnf(c_60633,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_60714,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_60633])).

cnf(c_95925,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_34,c_32,c_31,c_29,c_60714])).

cnf(c_10,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_350,plain,
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

cnf(c_351,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(k1_partfun1(X2,X1,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_373,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_351,c_19])).

cnf(c_96009,plain,
    ( k2_relset_1(X0,X1,X2) = X1
    | k6_partfun1(X1) != k1_partfun1(X1,X0,X0,X1,X3,X2)
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_96301,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_95925,c_96009])).

cnf(c_96015,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_96022,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_96273,plain,
    ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_96015,c_96022])).

cnf(c_96302,plain,
    ( k2_relat_1(sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_96301,c_96273])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_36,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_96858,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_96302,c_35,c_36,c_37,c_38,c_39,c_40])).

cnf(c_96862,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(demodulation,[status(thm)],[c_96858,c_96273])).

cnf(c_100682,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_100650,c_96862])).

cnf(c_100830,plain,
    ( k2_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_100824,c_100682])).

cnf(c_102081,plain,
    ( k5_relat_1(sK2,sK2) != k6_partfun1(sK0)
    | k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | iProver_ARSWP_247 != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_102080,c_100827,c_100830])).

cnf(c_96012,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_96017,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_96580,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_96015,c_96017])).

cnf(c_96650,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_96580,c_38,c_60907])).

cnf(c_96651,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_96650])).

cnf(c_96660,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_96012,c_96651])).

cnf(c_96663,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_96660,c_95925])).

cnf(c_96805,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_96663,c_35,c_37,c_38,c_40,c_61066,c_61068])).

cnf(c_96025,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_96808,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_96805,c_96025])).

cnf(c_96274,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_96012,c_96022])).

cnf(c_96276,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_96274,c_28])).

cnf(c_96019,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_96363,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_96015,c_96019])).

cnf(c_96415,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_96363,c_30,c_29,c_25,c_24539])).

cnf(c_96023,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_96317,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_96015,c_96023])).

cnf(c_96418,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_96415,c_96317])).

cnf(c_96809,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_96808,c_96276,c_96418])).

cnf(c_96810,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_96809])).

cnf(c_61577,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_61066,c_35,c_37,c_38,c_40,c_61068])).

cnf(c_60522,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v2_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_61585,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_61577,c_60522])).

cnf(c_60519,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_60744,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_60510,c_60519])).

cnf(c_60746,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_60744,c_28])).

cnf(c_60517,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_60859,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_60513,c_60517])).

cnf(c_61231,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_60859,c_30,c_29,c_25,c_24539])).

cnf(c_60520,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_60830,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_60513,c_60520])).

cnf(c_61234,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(demodulation,[status(thm)],[c_61231,c_60830])).

cnf(c_61586,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | sK1 != sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_61585,c_60746,c_61234])).

cnf(c_61587,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_61586])).

cnf(c_62493,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_61587,c_35,c_37,c_38,c_40,c_42040,c_60668])).

cnf(c_97133,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_96810,c_35,c_37,c_38,c_40,c_42040,c_60668,c_61587])).

cnf(c_97137,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_97133,c_96858])).

cnf(c_97138,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_97137])).

cnf(c_102869,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_102081,c_97138])).

cnf(c_102870,plain,
    ( k2_funct_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_102869])).

cnf(c_131321,plain,
    ( k2_funct_1(sK3) = sK2 ),
    inference(superposition,[status(thm)],[c_131317,c_102870])).

cnf(c_131326,plain,
    ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
    inference(light_normalisation,[status(thm)],[c_131319,c_131321])).

cnf(c_166437,plain,
    ( k2_funct_1(sK2) = sK3
    | k1_relat_1(sK2) != k2_relat_1(sK3)
    | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_131326,c_100243])).

cnf(c_101182,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_100228,c_100233])).

cnf(c_100859,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_100228,c_100241])).

cnf(c_101186,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_101182,c_100859])).

cnf(c_60860,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_60510,c_60517])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_60664,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_61239,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_60860,c_33,c_32,c_24,c_60664])).

cnf(c_60831,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_60510,c_60520])).

cnf(c_61242,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(demodulation,[status(thm)],[c_61239,c_60831])).

cnf(c_104268,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_101186,c_61242])).

cnf(c_166438,plain,
    ( k2_funct_1(sK2) = sK3
    | k6_partfun1(sK1) != k6_partfun1(sK1)
    | sK0 != sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_166437,c_100827,c_100830,c_104268])).

cnf(c_166439,plain,
    ( k2_funct_1(sK2) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_166438])).

cnf(c_23,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_26,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_42,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_166439,c_60668,c_42040,c_23,c_42,c_40,c_38,c_37,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:48:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 39.48/5.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.48/5.50  
% 39.48/5.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.48/5.50  
% 39.48/5.50  ------  iProver source info
% 39.48/5.50  
% 39.48/5.50  git: date: 2020-06-30 10:37:57 +0100
% 39.48/5.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.48/5.50  git: non_committed_changes: false
% 39.48/5.50  git: last_make_outside_of_git: false
% 39.48/5.50  
% 39.48/5.50  ------ 
% 39.48/5.50  ------ Parsing...
% 39.48/5.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  ------ Proving...
% 39.48/5.50  ------ Problem Properties 
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  clauses                                 34
% 39.48/5.50  conjectures                             11
% 39.48/5.50  EPR                                     7
% 39.48/5.50  Horn                                    30
% 39.48/5.50  unary                                   14
% 39.48/5.50  binary                                  4
% 39.48/5.50  lits                                    104
% 39.48/5.50  lits eq                                 28
% 39.48/5.50  fd_pure                                 0
% 39.48/5.50  fd_pseudo                               0
% 39.48/5.50  fd_cond                                 3
% 39.48/5.50  fd_pseudo_cond                          1
% 39.48/5.50  AC symbols                              0
% 39.48/5.50  
% 39.48/5.50  ------ Input Options Time Limit: Unbounded
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e ------ 
% 39.48/5.50  Current options:
% 39.48/5.50  ------ 
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 7 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 4 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 8 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  ------ Preprocessing... sf_s  rm: 0 0s  sf_e 
% 39.48/5.50  
% 39.48/5.50  ------ Proving...
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  % SZS status Theorem for theBenchmark.p
% 39.48/5.50  
% 39.48/5.50  % SZS output start CNFRefutation for theBenchmark.p
% 39.48/5.50  
% 39.48/5.50  fof(f15,conjecture,(
% 39.48/5.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f16,negated_conjecture,(
% 39.48/5.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 39.48/5.50    inference(negated_conjecture,[],[f15])).
% 39.48/5.50  
% 39.48/5.50  fof(f36,plain,(
% 39.48/5.50    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 39.48/5.50    inference(ennf_transformation,[],[f16])).
% 39.48/5.50  
% 39.48/5.50  fof(f37,plain,(
% 39.48/5.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 39.48/5.50    inference(flattening,[],[f36])).
% 39.48/5.50  
% 39.48/5.50  fof(f41,plain,(
% 39.48/5.50    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 39.48/5.50    introduced(choice_axiom,[])).
% 39.48/5.50  
% 39.48/5.50  fof(f40,plain,(
% 39.48/5.50    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 39.48/5.50    introduced(choice_axiom,[])).
% 39.48/5.50  
% 39.48/5.50  fof(f42,plain,(
% 39.48/5.50    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 39.48/5.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f37,f41,f40])).
% 39.48/5.50  
% 39.48/5.50  fof(f69,plain,(
% 39.48/5.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  fof(f7,axiom,(
% 39.48/5.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f25,plain,(
% 39.48/5.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.48/5.50    inference(ennf_transformation,[],[f7])).
% 39.48/5.50  
% 39.48/5.50  fof(f52,plain,(
% 39.48/5.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.48/5.50    inference(cnf_transformation,[],[f25])).
% 39.48/5.50  
% 39.48/5.50  fof(f73,plain,(
% 39.48/5.50    k2_relset_1(sK0,sK1,sK2) = sK1),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  fof(f72,plain,(
% 39.48/5.50    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  fof(f10,axiom,(
% 39.48/5.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f28,plain,(
% 39.48/5.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.48/5.50    inference(ennf_transformation,[],[f10])).
% 39.48/5.50  
% 39.48/5.50  fof(f29,plain,(
% 39.48/5.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.48/5.50    inference(flattening,[],[f28])).
% 39.48/5.50  
% 39.48/5.50  fof(f39,plain,(
% 39.48/5.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.48/5.50    inference(nnf_transformation,[],[f29])).
% 39.48/5.50  
% 39.48/5.50  fof(f56,plain,(
% 39.48/5.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.48/5.50    inference(cnf_transformation,[],[f39])).
% 39.48/5.50  
% 39.48/5.50  fof(f6,axiom,(
% 39.48/5.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f24,plain,(
% 39.48/5.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.48/5.50    inference(ennf_transformation,[],[f6])).
% 39.48/5.50  
% 39.48/5.50  fof(f51,plain,(
% 39.48/5.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.48/5.50    inference(cnf_transformation,[],[f24])).
% 39.48/5.50  
% 39.48/5.50  fof(f71,plain,(
% 39.48/5.50    v1_funct_2(sK3,sK1,sK0)),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  fof(f76,plain,(
% 39.48/5.50    k1_xboole_0 != sK0),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  fof(f2,axiom,(
% 39.48/5.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f17,plain,(
% 39.48/5.50    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 39.48/5.50    inference(ennf_transformation,[],[f2])).
% 39.48/5.50  
% 39.48/5.50  fof(f18,plain,(
% 39.48/5.50    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.48/5.50    inference(flattening,[],[f17])).
% 39.48/5.50  
% 39.48/5.50  fof(f46,plain,(
% 39.48/5.50    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.48/5.50    inference(cnf_transformation,[],[f18])).
% 39.48/5.50  
% 39.48/5.50  fof(f70,plain,(
% 39.48/5.50    v1_funct_1(sK3)),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  fof(f5,axiom,(
% 39.48/5.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f23,plain,(
% 39.48/5.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.48/5.50    inference(ennf_transformation,[],[f5])).
% 39.48/5.50  
% 39.48/5.50  fof(f50,plain,(
% 39.48/5.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.48/5.50    inference(cnf_transformation,[],[f23])).
% 39.48/5.50  
% 39.48/5.50  fof(f11,axiom,(
% 39.48/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f30,plain,(
% 39.48/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 39.48/5.50    inference(ennf_transformation,[],[f11])).
% 39.48/5.50  
% 39.48/5.50  fof(f31,plain,(
% 39.48/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 39.48/5.50    inference(flattening,[],[f30])).
% 39.48/5.50  
% 39.48/5.50  fof(f63,plain,(
% 39.48/5.50    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 39.48/5.50    inference(cnf_transformation,[],[f31])).
% 39.48/5.50  
% 39.48/5.50  fof(f67,plain,(
% 39.48/5.50    v1_funct_1(sK2)),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  fof(f8,axiom,(
% 39.48/5.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f26,plain,(
% 39.48/5.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 39.48/5.50    inference(ennf_transformation,[],[f8])).
% 39.48/5.50  
% 39.48/5.50  fof(f27,plain,(
% 39.48/5.50    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.48/5.50    inference(flattening,[],[f26])).
% 39.48/5.50  
% 39.48/5.50  fof(f38,plain,(
% 39.48/5.50    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.48/5.50    inference(nnf_transformation,[],[f27])).
% 39.48/5.50  
% 39.48/5.50  fof(f53,plain,(
% 39.48/5.50    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.48/5.50    inference(cnf_transformation,[],[f38])).
% 39.48/5.50  
% 39.48/5.50  fof(f74,plain,(
% 39.48/5.50    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  fof(f9,axiom,(
% 39.48/5.50    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f55,plain,(
% 39.48/5.50    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 39.48/5.50    inference(cnf_transformation,[],[f9])).
% 39.48/5.50  
% 39.48/5.50  fof(f13,axiom,(
% 39.48/5.50    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f65,plain,(
% 39.48/5.50    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 39.48/5.50    inference(cnf_transformation,[],[f13])).
% 39.48/5.50  
% 39.48/5.50  fof(f84,plain,(
% 39.48/5.50    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 39.48/5.50    inference(definition_unfolding,[],[f55,f65])).
% 39.48/5.50  
% 39.48/5.50  fof(f12,axiom,(
% 39.48/5.50    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f32,plain,(
% 39.48/5.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 39.48/5.50    inference(ennf_transformation,[],[f12])).
% 39.48/5.50  
% 39.48/5.50  fof(f33,plain,(
% 39.48/5.50    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 39.48/5.50    inference(flattening,[],[f32])).
% 39.48/5.50  
% 39.48/5.50  fof(f64,plain,(
% 39.48/5.50    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 39.48/5.50    inference(cnf_transformation,[],[f33])).
% 39.48/5.50  
% 39.48/5.50  fof(f1,axiom,(
% 39.48/5.50    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f44,plain,(
% 39.48/5.50    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 39.48/5.50    inference(cnf_transformation,[],[f1])).
% 39.48/5.50  
% 39.48/5.50  fof(f79,plain,(
% 39.48/5.50    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 39.48/5.50    inference(definition_unfolding,[],[f44,f65])).
% 39.48/5.50  
% 39.48/5.50  fof(f3,axiom,(
% 39.48/5.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f19,plain,(
% 39.48/5.50    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 39.48/5.50    inference(ennf_transformation,[],[f3])).
% 39.48/5.50  
% 39.48/5.50  fof(f20,plain,(
% 39.48/5.50    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.48/5.50    inference(flattening,[],[f19])).
% 39.48/5.50  
% 39.48/5.50  fof(f47,plain,(
% 39.48/5.50    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.48/5.50    inference(cnf_transformation,[],[f20])).
% 39.48/5.50  
% 39.48/5.50  fof(f82,plain,(
% 39.48/5.50    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.48/5.50    inference(definition_unfolding,[],[f47,f65])).
% 39.48/5.50  
% 39.48/5.50  fof(f4,axiom,(
% 39.48/5.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f21,plain,(
% 39.48/5.50    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 39.48/5.50    inference(ennf_transformation,[],[f4])).
% 39.48/5.50  
% 39.48/5.50  fof(f22,plain,(
% 39.48/5.50    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.48/5.50    inference(flattening,[],[f21])).
% 39.48/5.50  
% 39.48/5.50  fof(f49,plain,(
% 39.48/5.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.48/5.50    inference(cnf_transformation,[],[f22])).
% 39.48/5.50  
% 39.48/5.50  fof(f83,plain,(
% 39.48/5.50    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.48/5.50    inference(definition_unfolding,[],[f49,f65])).
% 39.48/5.50  
% 39.48/5.50  fof(f14,axiom,(
% 39.48/5.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 39.48/5.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.48/5.50  
% 39.48/5.50  fof(f34,plain,(
% 39.48/5.50    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 39.48/5.50    inference(ennf_transformation,[],[f14])).
% 39.48/5.50  
% 39.48/5.50  fof(f35,plain,(
% 39.48/5.50    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 39.48/5.50    inference(flattening,[],[f34])).
% 39.48/5.50  
% 39.48/5.50  fof(f66,plain,(
% 39.48/5.50    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 39.48/5.50    inference(cnf_transformation,[],[f35])).
% 39.48/5.50  
% 39.48/5.50  fof(f54,plain,(
% 39.48/5.50    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.48/5.50    inference(cnf_transformation,[],[f38])).
% 39.48/5.50  
% 39.48/5.50  fof(f85,plain,(
% 39.48/5.50    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.48/5.50    inference(equality_resolution,[],[f54])).
% 39.48/5.50  
% 39.48/5.50  fof(f68,plain,(
% 39.48/5.50    v1_funct_2(sK2,sK0,sK1)),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  fof(f77,plain,(
% 39.48/5.50    k1_xboole_0 != sK1),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  fof(f78,plain,(
% 39.48/5.50    k2_funct_1(sK2) != sK3),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  fof(f75,plain,(
% 39.48/5.50    v2_funct_1(sK2)),
% 39.48/5.50    inference(cnf_transformation,[],[f42])).
% 39.48/5.50  
% 39.48/5.50  cnf(c_32,negated_conjecture,
% 39.48/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 39.48/5.50      inference(cnf_transformation,[],[f69]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100228,plain,
% 39.48/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_9,plain,
% 39.48/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 39.48/5.50      inference(cnf_transformation,[],[f52]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100240,plain,
% 39.48/5.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100825,plain,
% 39.48/5.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100228,c_100240]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_28,negated_conjecture,
% 39.48/5.50      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 39.48/5.50      inference(cnf_transformation,[],[f73]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100827,plain,
% 39.48/5.50      ( k2_relat_1(sK2) = sK1 ),
% 39.48/5.50      inference(light_normalisation,[status(thm)],[c_100825,c_28]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_29,negated_conjecture,
% 39.48/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 39.48/5.50      inference(cnf_transformation,[],[f72]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100231,plain,
% 39.48/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_18,plain,
% 39.48/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 39.48/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | k1_relset_1(X1,X2,X0) = X1
% 39.48/5.50      | k1_xboole_0 = X2 ),
% 39.48/5.50      inference(cnf_transformation,[],[f56]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100233,plain,
% 39.48/5.50      ( k1_relset_1(X0,X1,X2) = X0
% 39.48/5.50      | k1_xboole_0 = X1
% 39.48/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101181,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.48/5.50      | sK0 = k1_xboole_0
% 39.48/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100231,c_100233]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_8,plain,
% 39.48/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 39.48/5.50      inference(cnf_transformation,[],[f51]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100241,plain,
% 39.48/5.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100858,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100231,c_100241]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101193,plain,
% 39.48/5.50      ( k1_relat_1(sK3) = sK1
% 39.48/5.50      | sK0 = k1_xboole_0
% 39.48/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.48/5.50      inference(demodulation,[status(thm)],[c_101181,c_100858]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_30,negated_conjecture,
% 39.48/5.50      ( v1_funct_2(sK3,sK1,sK0) ),
% 39.48/5.50      inference(cnf_transformation,[],[f71]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_39,plain,
% 39.48/5.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_25,negated_conjecture,
% 39.48/5.50      ( k1_xboole_0 != sK0 ),
% 39.48/5.50      inference(cnf_transformation,[],[f76]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_657,plain,( X0 = X0 ),theory(equality) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_686,plain,
% 39.48/5.50      ( k1_xboole_0 = k1_xboole_0 ),
% 39.48/5.50      inference(instantiation,[status(thm)],[c_657]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_658,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_7603,plain,
% 39.48/5.50      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 39.48/5.50      inference(instantiation,[status(thm)],[c_658]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_7604,plain,
% 39.48/5.50      ( sK0 != k1_xboole_0
% 39.48/5.50      | k1_xboole_0 = sK0
% 39.48/5.50      | k1_xboole_0 != k1_xboole_0 ),
% 39.48/5.50      inference(instantiation,[status(thm)],[c_7603]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_24506,plain,
% 39.48/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_24507,plain,
% 39.48/5.50      ( k1_relset_1(X0,X1,X2) = X0
% 39.48/5.50      | k1_xboole_0 = X1
% 39.48/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_24559,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.48/5.50      | sK0 = k1_xboole_0
% 39.48/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_24506,c_24507]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_24508,plain,
% 39.48/5.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_24550,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_24506,c_24508]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_24560,plain,
% 39.48/5.50      ( k1_relat_1(sK3) = sK1
% 39.48/5.50      | sK0 = k1_xboole_0
% 39.48/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.48/5.50      inference(demodulation,[status(thm)],[c_24559,c_24550]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_105173,plain,
% 39.48/5.50      ( k1_relat_1(sK3) = sK1 ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_101193,c_39,c_25,c_686,c_7604,c_24560]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_2,plain,
% 39.48/5.50      ( ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(X1)
% 39.48/5.50      | ~ v1_relat_1(X0)
% 39.48/5.50      | ~ v1_relat_1(X1)
% 39.48/5.50      | v2_funct_1(X1)
% 39.48/5.50      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 39.48/5.50      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 39.48/5.50      inference(cnf_transformation,[],[f46]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100247,plain,
% 39.48/5.50      ( k1_relat_1(X0) != k2_relat_1(X1)
% 39.48/5.50      | v1_funct_1(X1) != iProver_top
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_relat_1(X1) != iProver_top
% 39.48/5.50      | v1_relat_1(X0) != iProver_top
% 39.48/5.50      | v2_funct_1(X0) = iProver_top
% 39.48/5.50      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_105185,plain,
% 39.48/5.50      ( k2_relat_1(X0) != sK1
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(X0) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_105173,c_100247]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_64912,plain,
% 39.48/5.50      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_64577,negated_conjecture,
% 39.48/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1)))
% 39.48/5.50      | ~ iProver_ARSWP_238 ),
% 39.48/5.50      inference(arg_filter_abstr,[status(unp)],[c_29]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_64890,plain,
% 39.48/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(sK1))) = iProver_top
% 39.48/5.50      | iProver_ARSWP_238 != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_64577]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_64573,plain,
% 39.48/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 39.48/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
% 39.48/5.50      | ~ iProver_ARSWP_234
% 39.48/5.50      | k1_relset_1(X1,X2,X0) = X1
% 39.48/5.50      | k1_xboole_0 = X2 ),
% 39.48/5.50      inference(arg_filter_abstr,[status(unp)],[c_18]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_64894,plain,
% 39.48/5.50      ( k1_relset_1(X0,X1,X2) = X0
% 39.48/5.50      | k1_xboole_0 = X1
% 39.48/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
% 39.48/5.50      | iProver_ARSWP_234 != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_64573]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_66353,plain,
% 39.48/5.50      ( k1_relset_1(sK1,X0,sK3) = sK1
% 39.48/5.50      | k1_xboole_0 = X0
% 39.48/5.50      | v1_funct_2(sK3,sK1,X0) != iProver_top
% 39.48/5.50      | iProver_ARSWP_238 != iProver_top
% 39.48/5.50      | iProver_ARSWP_234 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_64890,c_64894]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_68104,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.48/5.50      | sK0 = k1_xboole_0
% 39.48/5.50      | iProver_ARSWP_238 != iProver_top
% 39.48/5.50      | iProver_ARSWP_234 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_64912,c_66353]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_24539,plain,
% 39.48/5.50      ( ~ v1_funct_2(sK3,sK1,sK0)
% 39.48/5.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.48/5.50      | k1_relset_1(sK1,sK0,sK3) = sK1
% 39.48/5.50      | k1_xboole_0 = sK0 ),
% 39.48/5.50      inference(instantiation,[status(thm)],[c_18]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_68139,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_68104,c_30,c_29,c_25,c_24539]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_64565,plain,
% 39.48/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X1)))
% 39.48/5.50      | ~ iProver_ARSWP_226
% 39.48/5.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 39.48/5.50      inference(arg_filter_abstr,[status(unp)],[c_8]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_64902,plain,
% 39.48/5.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(arAF1_k2_zfmisc_1_0_1(X0))) != iProver_top
% 39.48/5.50      | iProver_ARSWP_226 != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_64565]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_65948,plain,
% 39.48/5.50      ( k1_relset_1(sK1,X0,sK3) = k1_relat_1(sK3)
% 39.48/5.50      | iProver_ARSWP_238 != iProver_top
% 39.48/5.50      | iProver_ARSWP_226 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_64890,c_64902]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_68144,plain,
% 39.48/5.50      ( k1_relat_1(sK3) = sK1
% 39.48/5.50      | iProver_ARSWP_238 != iProver_top
% 39.48/5.50      | iProver_ARSWP_226 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_68139,c_65948]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_68402,plain,
% 39.48/5.50      ( k1_relat_1(sK3) = sK1 ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_68144,c_39,c_25,c_686,c_7604,c_24560]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_64918,plain,
% 39.48/5.50      ( k1_relat_1(X0) != k2_relat_1(X1)
% 39.48/5.50      | v1_funct_1(X1) != iProver_top
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_relat_1(X1) != iProver_top
% 39.48/5.50      | v1_relat_1(X0) != iProver_top
% 39.48/5.50      | v2_funct_1(X0) = iProver_top
% 39.48/5.50      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_68435,plain,
% 39.48/5.50      ( k2_relat_1(X0) != sK1
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(X0) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_68402,c_64918]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_31,negated_conjecture,
% 39.48/5.50      ( v1_funct_1(sK3) ),
% 39.48/5.50      inference(cnf_transformation,[],[f70]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_38,plain,
% 39.48/5.50      ( v1_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_40,plain,
% 39.48/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_7,plain,
% 39.48/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | v1_relat_1(X0) ),
% 39.48/5.50      inference(cnf_transformation,[],[f50]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_42039,plain,
% 39.48/5.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.48/5.50      | v1_relat_1(sK3) ),
% 39.48/5.50      inference(instantiation,[status(thm)],[c_7]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_42040,plain,
% 39.48/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_42039]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_68946,plain,
% 39.48/5.50      ( v1_relat_1(X0) != iProver_top
% 39.48/5.50      | k2_relat_1(X0) != sK1
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_68435,c_38,c_40,c_42040]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_68947,plain,
% 39.48/5.50      ( k2_relat_1(X0) != sK1
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_relat_1(X0) != iProver_top
% 39.48/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(renaming,[status(thm)],[c_68946]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_131144,plain,
% 39.48/5.50      ( v1_relat_1(X0) != iProver_top
% 39.48/5.50      | k2_relat_1(X0) != sK1
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_105185,c_38,c_40,c_42040,c_68435]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_131145,plain,
% 39.48/5.50      ( k2_relat_1(X0) != sK1
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_relat_1(X0) != iProver_top
% 39.48/5.50      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(renaming,[status(thm)],[c_131144]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_131154,plain,
% 39.48/5.50      ( v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100827,c_131145]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_19,plain,
% 39.48/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.48/5.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(X3) ),
% 39.48/5.50      inference(cnf_transformation,[],[f63]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_99931,plain,
% 39.48/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.48/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(X3)
% 39.48/5.50      | ~ iProver_ARSWP_245 ),
% 39.48/5.50      inference(arg_filter_abstr,[status(unp)],[c_19]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100220,plain,
% 39.48/5.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.48/5.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 39.48/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 39.48/5.50      | v1_funct_1(X3) != iProver_top
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | iProver_ARSWP_245 != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_99931]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_102120,plain,
% 39.48/5.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.48/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | iProver_ARSWP_245 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100231,c_100220]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_102261,plain,
% 39.48/5.50      ( v1_funct_1(X0) != iProver_top
% 39.48/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
% 39.48/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.48/5.50      | iProver_ARSWP_245 != iProver_top ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_102120,c_38]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_102262,plain,
% 39.48/5.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.48/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,sK0))) = iProver_top
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | iProver_ARSWP_245 != iProver_top ),
% 39.48/5.50      inference(renaming,[status(thm)],[c_102261]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_102273,plain,
% 39.48/5.50      ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | iProver_ARSWP_245 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100228,c_102262]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_34,negated_conjecture,
% 39.48/5.50      ( v1_funct_1(sK2) ),
% 39.48/5.50      inference(cnf_transformation,[],[f67]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_35,plain,
% 39.48/5.50      ( v1_funct_1(sK2) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_102420,plain,
% 39.48/5.50      ( m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 39.48/5.50      | iProver_ARSWP_245 != iProver_top ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_102273,c_35]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_11,plain,
% 39.48/5.50      ( ~ r2_relset_1(X0,X1,X2,X3)
% 39.48/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.48/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.48/5.50      | X3 = X2 ),
% 39.48/5.50      inference(cnf_transformation,[],[f53]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_27,negated_conjecture,
% 39.48/5.50      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 39.48/5.50      inference(cnf_transformation,[],[f74]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_385,plain,
% 39.48/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | X3 = X0
% 39.48/5.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 39.48/5.50      | k6_partfun1(sK0) != X3
% 39.48/5.50      | sK0 != X2
% 39.48/5.50      | sK0 != X1 ),
% 39.48/5.50      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_386,plain,
% 39.48/5.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.48/5.50      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.48/5.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 39.48/5.50      inference(unflattening,[status(thm)],[c_385]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_12,plain,
% 39.48/5.50      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 39.48/5.50      inference(cnf_transformation,[],[f84]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_394,plain,
% 39.48/5.50      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.48/5.50      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 39.48/5.50      inference(forward_subsumption_resolution,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_386,c_12]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_99935,plain,
% 39.48/5.50      ( ~ m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.48/5.50      | ~ iProver_ARSWP_249
% 39.48/5.50      | k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
% 39.48/5.50      inference(arg_filter_abstr,[status(unp)],[c_394]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100216,plain,
% 39.48/5.50      ( k6_partfun1(sK0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.48/5.50      | m1_subset_1(arAF1_k1_partfun1_0_1_2(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 39.48/5.50      | iProver_ARSWP_249 != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_99935]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_102439,plain,
% 39.48/5.50      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k6_partfun1(sK0)
% 39.48/5.50      | iProver_ARSWP_249 != iProver_top
% 39.48/5.50      | iProver_ARSWP_245 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_102420,c_100216]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_21,plain,
% 39.48/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(X3)
% 39.48/5.50      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 39.48/5.50      inference(cnf_transformation,[],[f64]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_99933,plain,
% 39.48/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(X3)
% 39.48/5.50      | ~ iProver_ARSWP_247
% 39.48/5.50      | arAF1_k1_partfun1_0_1_2(X4,X5) = k5_relat_1(X3,X0) ),
% 39.48/5.50      inference(arg_filter_abstr,[status(unp)],[c_21]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100218,plain,
% 39.48/5.50      ( arAF1_k1_partfun1_0_1_2(X0,X1) = k5_relat_1(X2,X3)
% 39.48/5.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.48/5.50      | v1_funct_1(X2) != iProver_top
% 39.48/5.50      | v1_funct_1(X3) != iProver_top
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_99933]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101032,plain,
% 39.48/5.50      ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.48/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100228,c_100218]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101380,plain,
% 39.48/5.50      ( v1_funct_1(X0) != iProver_top
% 39.48/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.48/5.50      | k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_101032,c_35]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101381,plain,
% 39.48/5.50      ( k5_relat_1(sK2,X0) = arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.48/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top ),
% 39.48/5.50      inference(renaming,[status(thm)],[c_101380]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101391,plain,
% 39.48/5.50      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100231,c_101381]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101446,plain,
% 39.48/5.50      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK3)
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_101391,c_38]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_103355,plain,
% 39.48/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 39.48/5.50      | iProver_ARSWP_249 != iProver_top
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top
% 39.48/5.50      | iProver_ARSWP_245 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_102439,c_101446]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_37,plain,
% 39.48/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60510,plain,
% 39.48/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60513,plain,
% 39.48/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60515,plain,
% 39.48/5.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 39.48/5.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 39.48/5.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.48/5.50      | v1_funct_1(X4) != iProver_top
% 39.48/5.50      | v1_funct_1(X5) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60907,plain,
% 39.48/5.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.48/5.50      | v1_funct_1(X2) != iProver_top
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_60513,c_60515]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60976,plain,
% 39.48/5.50      ( v1_funct_1(X2) != iProver_top
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.48/5.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_60907,c_38]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60977,plain,
% 39.48/5.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.48/5.50      | v1_funct_1(X2) != iProver_top ),
% 39.48/5.50      inference(renaming,[status(thm)],[c_60976]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60988,plain,
% 39.48/5.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_60510,c_60977]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60634,plain,
% 39.48/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(sK3)
% 39.48/5.50      | k1_partfun1(X1,X2,sK1,sK0,X0,sK3) = k5_relat_1(X0,sK3) ),
% 39.48/5.50      inference(instantiation,[status(thm)],[c_21]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60727,plain,
% 39.48/5.50      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.48/5.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.48/5.50      | ~ v1_funct_1(sK3)
% 39.48/5.50      | ~ v1_funct_1(sK2)
% 39.48/5.50      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 39.48/5.50      inference(instantiation,[status(thm)],[c_60634]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_61063,plain,
% 39.48/5.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_60988,c_34,c_32,c_31,c_29,c_60727]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60507,plain,
% 39.48/5.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.48/5.50      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_61066,plain,
% 39.48/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 39.48/5.50      | m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 39.48/5.50      inference(demodulation,[status(thm)],[c_61063,c_60507]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60516,plain,
% 39.48/5.50      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 39.48/5.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 39.48/5.50      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 39.48/5.50      | v1_funct_1(X3) != iProver_top
% 39.48/5.50      | v1_funct_1(X0) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_61068,plain,
% 39.48/5.50      ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top
% 39.48/5.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.48/5.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_61063,c_60516]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_107055,plain,
% 39.48/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_103355,c_35,c_37,c_38,c_40,c_61066,c_61068]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_131189,plain,
% 39.48/5.50      ( v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(light_normalisation,[status(thm)],[c_131154,c_107055]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60667,plain,
% 39.48/5.50      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.48/5.50      | v1_relat_1(sK2) ),
% 39.48/5.50      inference(instantiation,[status(thm)],[c_7]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60668,plain,
% 39.48/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_60667]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_131311,plain,
% 39.48/5.50      ( v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_131189,c_35,c_37,c_60668]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_0,plain,
% 39.48/5.50      ( v2_funct_1(k6_partfun1(X0)) ),
% 39.48/5.50      inference(cnf_transformation,[],[f79]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100249,plain,
% 39.48/5.50      ( v2_funct_1(k6_partfun1(X0)) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_131317,plain,
% 39.48/5.50      ( v2_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(forward_subsumption_resolution,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_131311,c_100249]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100229,plain,
% 39.48/5.50      ( v1_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_5,plain,
% 39.48/5.50      ( ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_relat_1(X0)
% 39.48/5.50      | ~ v2_funct_1(X0)
% 39.48/5.50      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 39.48/5.50      inference(cnf_transformation,[],[f82]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100244,plain,
% 39.48/5.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_relat_1(X0) != iProver_top
% 39.48/5.50      | v2_funct_1(X0) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101106,plain,
% 39.48/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100229,c_100244]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_41921,plain,
% 39.48/5.50      ( v1_funct_1(sK3) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_41931,plain,
% 39.48/5.50      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_relat_1(X0) != iProver_top
% 39.48/5.50      | v2_funct_1(X0) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_42118,plain,
% 39.48/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_41921,c_41931]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101258,plain,
% 39.48/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(k1_relat_1(sK3))
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_101106,c_40,c_42040,c_42118]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_105176,plain,
% 39.48/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(demodulation,[status(thm)],[c_105173,c_101258]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_131319,plain,
% 39.48/5.50      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_131317,c_105176]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101392,plain,
% 39.48/5.50      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100228,c_101381]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101767,plain,
% 39.48/5.50      ( arAF1_k1_partfun1_0_1_2(sK0,sK1) = k5_relat_1(sK2,sK2)
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_101392,c_35]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101773,plain,
% 39.48/5.50      ( k5_relat_1(sK2,sK2) = k5_relat_1(sK2,sK3)
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_101446,c_101767]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_6,plain,
% 39.48/5.50      ( ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(X1)
% 39.48/5.50      | ~ v1_relat_1(X0)
% 39.48/5.50      | ~ v1_relat_1(X1)
% 39.48/5.50      | ~ v2_funct_1(X1)
% 39.48/5.50      | k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 39.48/5.50      | k2_funct_1(X1) = X0
% 39.48/5.50      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 39.48/5.50      inference(cnf_transformation,[],[f83]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100243,plain,
% 39.48/5.50      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 39.48/5.50      | k2_funct_1(X1) = X0
% 39.48/5.50      | k1_relat_1(X1) != k2_relat_1(X0)
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_funct_1(X1) != iProver_top
% 39.48/5.50      | v1_relat_1(X0) != iProver_top
% 39.48/5.50      | v1_relat_1(X1) != iProver_top
% 39.48/5.50      | v2_funct_1(X1) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_102080,plain,
% 39.48/5.50      ( k5_relat_1(sK2,sK2) != k6_partfun1(k2_relat_1(sK3))
% 39.48/5.50      | k2_funct_1(sK3) = sK2
% 39.48/5.50      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_101773,c_100243]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100824,plain,
% 39.48/5.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100231,c_100240]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_22,plain,
% 39.48/5.50      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 39.48/5.50      | ~ v1_funct_2(X3,X1,X0)
% 39.48/5.50      | ~ v1_funct_2(X2,X0,X1)
% 39.48/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 39.48/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 39.48/5.50      | ~ v1_funct_1(X2)
% 39.48/5.50      | ~ v1_funct_1(X3)
% 39.48/5.50      | k2_relset_1(X1,X0,X3) = X0 ),
% 39.48/5.50      inference(cnf_transformation,[],[f66]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_398,plain,
% 39.48/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 39.48/5.50      | ~ v1_funct_2(X3,X2,X1)
% 39.48/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 39.48/5.50      | ~ v1_funct_1(X3)
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | k1_partfun1(X1,X2,X2,X1,X0,X3) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.48/5.50      | k2_relset_1(X2,X1,X3) = X1
% 39.48/5.50      | k6_partfun1(X1) != k6_partfun1(sK0)
% 39.48/5.50      | sK0 != X1 ),
% 39.48/5.50      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_399,plain,
% 39.48/5.50      ( ~ v1_funct_2(X0,X1,sK0)
% 39.48/5.50      | ~ v1_funct_2(X2,sK0,X1)
% 39.48/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 39.48/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 39.48/5.50      | ~ v1_funct_1(X2)
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.48/5.50      | k2_relset_1(X1,sK0,X0) = sK0
% 39.48/5.50      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 39.48/5.50      inference(unflattening,[status(thm)],[c_398]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_483,plain,
% 39.48/5.50      ( ~ v1_funct_2(X0,X1,sK0)
% 39.48/5.50      | ~ v1_funct_2(X2,sK0,X1)
% 39.48/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 39.48/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(X2)
% 39.48/5.50      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 39.48/5.50      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 39.48/5.50      inference(equality_resolution_simp,[status(thm)],[c_399]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_99936,plain,
% 39.48/5.50      ( ~ v1_funct_2(X0,X1,sK0)
% 39.48/5.50      | ~ v1_funct_2(X2,sK0,X1)
% 39.48/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 39.48/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(X2)
% 39.48/5.50      | ~ iProver_ARSWP_250
% 39.48/5.50      | k2_relset_1(X1,sK0,X0) = sK0
% 39.48/5.50      | arAF1_k1_partfun1_0_1_2(sK0,X1) != arAF1_k1_partfun1_0_1_2(sK0,sK1) ),
% 39.48/5.50      inference(arg_filter_abstr,[status(unp)],[c_483]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100215,plain,
% 39.48/5.50      ( k2_relset_1(X0,sK0,X1) = sK0
% 39.48/5.50      | arAF1_k1_partfun1_0_1_2(sK0,X0) != arAF1_k1_partfun1_0_1_2(sK0,sK1)
% 39.48/5.50      | v1_funct_2(X1,X0,sK0) != iProver_top
% 39.48/5.50      | v1_funct_2(X2,sK0,X0) != iProver_top
% 39.48/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 39.48/5.50      | v1_funct_1(X2) != iProver_top
% 39.48/5.50      | v1_funct_1(X1) != iProver_top
% 39.48/5.50      | iProver_ARSWP_250 != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_99936]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100589,plain,
% 39.48/5.50      ( k2_relset_1(sK1,sK0,X0) = sK0
% 39.48/5.50      | v1_funct_2(X1,sK0,sK1) != iProver_top
% 39.48/5.50      | v1_funct_2(X0,sK1,sK0) != iProver_top
% 39.48/5.50      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.48/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_funct_1(X1) != iProver_top
% 39.48/5.50      | iProver_ARSWP_250 != iProver_top ),
% 39.48/5.50      inference(equality_resolution,[status(thm)],[c_100215]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100650,plain,
% 39.48/5.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 39.48/5.50      | v1_funct_2(X0,sK0,sK1) != iProver_top
% 39.48/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 39.48/5.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | iProver_ARSWP_250 != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100231,c_100589]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60633,plain,
% 39.48/5.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | m1_subset_1(k1_partfun1(X1,X2,sK1,sK0,X0,sK3),k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 39.48/5.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(sK3) ),
% 39.48/5.50      inference(instantiation,[status(thm)],[c_19]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60714,plain,
% 39.48/5.50      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 39.48/5.50      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 39.48/5.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.48/5.50      | ~ v1_funct_1(sK3)
% 39.48/5.50      | ~ v1_funct_1(sK2) ),
% 39.48/5.50      inference(instantiation,[status(thm)],[c_60633]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_95925,plain,
% 39.48/5.50      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_394,c_34,c_32,c_31,c_29,c_60714]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_10,plain,
% 39.48/5.50      ( r2_relset_1(X0,X1,X2,X2)
% 39.48/5.50      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 39.48/5.50      inference(cnf_transformation,[],[f85]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_350,plain,
% 39.48/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 39.48/5.50      | ~ v1_funct_2(X3,X2,X1)
% 39.48/5.50      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X5,X6)))
% 39.48/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 39.48/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | ~ v1_funct_1(X3)
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | X2 != X6
% 39.48/5.50      | X2 != X5
% 39.48/5.50      | k1_partfun1(X2,X1,X1,X2,X3,X0) != X4
% 39.48/5.50      | k2_relset_1(X1,X2,X0) = X2
% 39.48/5.50      | k6_partfun1(X2) != X4 ),
% 39.48/5.50      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_351,plain,
% 39.48/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 39.48/5.50      | ~ v1_funct_2(X3,X2,X1)
% 39.48/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 39.48/5.50      | ~ m1_subset_1(k1_partfun1(X2,X1,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X2)))
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(X3)
% 39.48/5.50      | k2_relset_1(X1,X2,X0) = X2
% 39.48/5.50      | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
% 39.48/5.50      inference(unflattening,[status(thm)],[c_350]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_373,plain,
% 39.48/5.50      ( ~ v1_funct_2(X0,X1,X2)
% 39.48/5.50      | ~ v1_funct_2(X3,X2,X1)
% 39.48/5.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.48/5.50      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 39.48/5.50      | ~ v1_funct_1(X0)
% 39.48/5.50      | ~ v1_funct_1(X3)
% 39.48/5.50      | k2_relset_1(X1,X2,X0) = X2
% 39.48/5.50      | k6_partfun1(X2) != k1_partfun1(X2,X1,X1,X2,X3,X0) ),
% 39.48/5.50      inference(forward_subsumption_resolution,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_351,c_19]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96009,plain,
% 39.48/5.50      ( k2_relset_1(X0,X1,X2) = X1
% 39.48/5.50      | k6_partfun1(X1) != k1_partfun1(X1,X0,X0,X1,X3,X2)
% 39.48/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.48/5.50      | v1_funct_2(X3,X1,X0) != iProver_top
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.48/5.50      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 39.48/5.50      | v1_funct_1(X3) != iProver_top
% 39.48/5.50      | v1_funct_1(X2) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96301,plain,
% 39.48/5.50      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 39.48/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 39.48/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 39.48/5.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.48/5.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_95925,c_96009]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96015,plain,
% 39.48/5.50      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96022,plain,
% 39.48/5.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96273,plain,
% 39.48/5.50      ( k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_96015,c_96022]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96302,plain,
% 39.48/5.50      ( k2_relat_1(sK3) = sK0
% 39.48/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 39.48/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 39.48/5.50      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 39.48/5.50      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top ),
% 39.48/5.50      inference(demodulation,[status(thm)],[c_96301,c_96273]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_33,negated_conjecture,
% 39.48/5.50      ( v1_funct_2(sK2,sK0,sK1) ),
% 39.48/5.50      inference(cnf_transformation,[],[f68]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_36,plain,
% 39.48/5.50      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96858,plain,
% 39.48/5.50      ( k2_relat_1(sK3) = sK0 ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_96302,c_35,c_36,c_37,c_38,c_39,c_40]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96862,plain,
% 39.48/5.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 39.48/5.50      inference(demodulation,[status(thm)],[c_96858,c_96273]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100682,plain,
% 39.48/5.50      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_100650,c_96862]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100830,plain,
% 39.48/5.50      ( k2_relat_1(sK3) = sK0 ),
% 39.48/5.50      inference(light_normalisation,[status(thm)],[c_100824,c_100682]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_102081,plain,
% 39.48/5.50      ( k5_relat_1(sK2,sK2) != k6_partfun1(sK0)
% 39.48/5.50      | k2_funct_1(sK3) = sK2
% 39.48/5.50      | k1_relat_1(sK3) != sK1
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top
% 39.48/5.50      | iProver_ARSWP_247 != iProver_top ),
% 39.48/5.50      inference(light_normalisation,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_102080,c_100827,c_100830]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96012,plain,
% 39.48/5.50      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96017,plain,
% 39.48/5.50      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 39.48/5.50      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 39.48/5.50      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.48/5.50      | v1_funct_1(X4) != iProver_top
% 39.48/5.50      | v1_funct_1(X5) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96580,plain,
% 39.48/5.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.48/5.50      | v1_funct_1(X2) != iProver_top
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_96015,c_96017]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96650,plain,
% 39.48/5.50      ( v1_funct_1(X2) != iProver_top
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.48/5.50      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_96580,c_38,c_60907]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96651,plain,
% 39.48/5.50      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 39.48/5.50      | v1_funct_1(X2) != iProver_top ),
% 39.48/5.50      inference(renaming,[status(thm)],[c_96650]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96660,plain,
% 39.48/5.50      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_96012,c_96651]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96663,plain,
% 39.48/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top ),
% 39.48/5.50      inference(light_normalisation,[status(thm)],[c_96660,c_95925]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96805,plain,
% 39.48/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_96663,c_35,c_37,c_38,c_40,c_61066,c_61068]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96025,plain,
% 39.48/5.50      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 39.48/5.50      | k2_funct_1(X1) = X0
% 39.48/5.50      | k1_relat_1(X1) != k2_relat_1(X0)
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_funct_1(X1) != iProver_top
% 39.48/5.50      | v1_relat_1(X0) != iProver_top
% 39.48/5.50      | v1_relat_1(X1) != iProver_top
% 39.48/5.50      | v2_funct_1(X1) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96808,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2
% 39.48/5.50      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 39.48/5.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_96805,c_96025]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96274,plain,
% 39.48/5.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_96012,c_96022]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96276,plain,
% 39.48/5.50      ( k2_relat_1(sK2) = sK1 ),
% 39.48/5.50      inference(light_normalisation,[status(thm)],[c_96274,c_28]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96019,plain,
% 39.48/5.50      ( k1_relset_1(X0,X1,X2) = X0
% 39.48/5.50      | k1_xboole_0 = X1
% 39.48/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96363,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.48/5.50      | sK0 = k1_xboole_0
% 39.48/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_96015,c_96019]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96415,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_96363,c_30,c_29,c_25,c_24539]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96023,plain,
% 39.48/5.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96317,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_96015,c_96023]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96418,plain,
% 39.48/5.50      ( k1_relat_1(sK3) = sK1 ),
% 39.48/5.50      inference(demodulation,[status(thm)],[c_96415,c_96317]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96809,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2
% 39.48/5.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.48/5.50      | sK1 != sK1
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(light_normalisation,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_96808,c_96276,c_96418]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_96810,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2
% 39.48/5.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(equality_resolution_simp,[status(thm)],[c_96809]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_61577,plain,
% 39.48/5.50      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_61066,c_35,c_37,c_38,c_40,c_61068]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60522,plain,
% 39.48/5.50      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 39.48/5.50      | k2_funct_1(X1) = X0
% 39.48/5.50      | k1_relat_1(X1) != k2_relat_1(X0)
% 39.48/5.50      | v1_funct_1(X0) != iProver_top
% 39.48/5.50      | v1_funct_1(X1) != iProver_top
% 39.48/5.50      | v1_relat_1(X0) != iProver_top
% 39.48/5.50      | v1_relat_1(X1) != iProver_top
% 39.48/5.50      | v2_funct_1(X1) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_61585,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2
% 39.48/5.50      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 39.48/5.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_61577,c_60522]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60519,plain,
% 39.48/5.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60744,plain,
% 39.48/5.50      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_60510,c_60519]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60746,plain,
% 39.48/5.50      ( k2_relat_1(sK2) = sK1 ),
% 39.48/5.50      inference(light_normalisation,[status(thm)],[c_60744,c_28]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60517,plain,
% 39.48/5.50      ( k1_relset_1(X0,X1,X2) = X0
% 39.48/5.50      | k1_xboole_0 = X1
% 39.48/5.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60859,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 39.48/5.50      | sK0 = k1_xboole_0
% 39.48/5.50      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_60513,c_60517]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_61231,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = sK1 ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_60859,c_30,c_29,c_25,c_24539]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60520,plain,
% 39.48/5.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.48/5.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60830,plain,
% 39.48/5.50      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_60513,c_60520]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_61234,plain,
% 39.48/5.50      ( k1_relat_1(sK3) = sK1 ),
% 39.48/5.50      inference(demodulation,[status(thm)],[c_61231,c_60830]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_61586,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2
% 39.48/5.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.48/5.50      | sK1 != sK1
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(light_normalisation,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_61585,c_60746,c_61234]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_61587,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2
% 39.48/5.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(equality_resolution_simp,[status(thm)],[c_61586]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_62493,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2
% 39.48/5.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_61587,c_35,c_37,c_38,c_40,c_42040,c_60668]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_97133,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2
% 39.48/5.50      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_96810,c_35,c_37,c_38,c_40,c_42040,c_60668,c_61587]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_97137,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2
% 39.48/5.50      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 39.48/5.50      | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(light_normalisation,[status(thm)],[c_97133,c_96858]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_97138,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(equality_resolution_simp,[status(thm)],[c_97137]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_102869,plain,
% 39.48/5.50      ( v2_funct_1(sK3) != iProver_top | k2_funct_1(sK3) = sK2 ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_102081,c_97138]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_102870,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2 | v2_funct_1(sK3) != iProver_top ),
% 39.48/5.50      inference(renaming,[status(thm)],[c_102869]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_131321,plain,
% 39.48/5.50      ( k2_funct_1(sK3) = sK2 ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_131317,c_102870]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_131326,plain,
% 39.48/5.50      ( k5_relat_1(sK3,sK2) = k6_partfun1(sK1) ),
% 39.48/5.50      inference(light_normalisation,[status(thm)],[c_131319,c_131321]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_166437,plain,
% 39.48/5.50      ( k2_funct_1(sK2) = sK3
% 39.48/5.50      | k1_relat_1(sK2) != k2_relat_1(sK3)
% 39.48/5.50      | k6_partfun1(k2_relat_1(sK2)) != k6_partfun1(sK1)
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(sK2) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_131326,c_100243]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101182,plain,
% 39.48/5.50      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 39.48/5.50      | sK1 = k1_xboole_0
% 39.48/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100228,c_100233]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_100859,plain,
% 39.48/5.50      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_100228,c_100241]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_101186,plain,
% 39.48/5.50      ( k1_relat_1(sK2) = sK0
% 39.48/5.50      | sK1 = k1_xboole_0
% 39.48/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 39.48/5.50      inference(demodulation,[status(thm)],[c_101182,c_100859]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60860,plain,
% 39.48/5.50      ( k1_relset_1(sK0,sK1,sK2) = sK0
% 39.48/5.50      | sK1 = k1_xboole_0
% 39.48/5.50      | v1_funct_2(sK2,sK0,sK1) != iProver_top ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_60510,c_60517]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_24,negated_conjecture,
% 39.48/5.50      ( k1_xboole_0 != sK1 ),
% 39.48/5.50      inference(cnf_transformation,[],[f77]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60664,plain,
% 39.48/5.50      ( ~ v1_funct_2(sK2,sK0,sK1)
% 39.48/5.50      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 39.48/5.50      | k1_relset_1(sK0,sK1,sK2) = sK0
% 39.48/5.50      | k1_xboole_0 = sK1 ),
% 39.48/5.50      inference(instantiation,[status(thm)],[c_18]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_61239,plain,
% 39.48/5.50      ( k1_relset_1(sK0,sK1,sK2) = sK0 ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_60860,c_33,c_32,c_24,c_60664]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_60831,plain,
% 39.48/5.50      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 39.48/5.50      inference(superposition,[status(thm)],[c_60510,c_60520]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_61242,plain,
% 39.48/5.50      ( k1_relat_1(sK2) = sK0 ),
% 39.48/5.50      inference(demodulation,[status(thm)],[c_61239,c_60831]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_104268,plain,
% 39.48/5.50      ( k1_relat_1(sK2) = sK0 ),
% 39.48/5.50      inference(global_propositional_subsumption,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_101186,c_61242]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_166438,plain,
% 39.48/5.50      ( k2_funct_1(sK2) = sK3
% 39.48/5.50      | k6_partfun1(sK1) != k6_partfun1(sK1)
% 39.48/5.50      | sK0 != sK0
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(sK2) != iProver_top ),
% 39.48/5.50      inference(light_normalisation,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_166437,c_100827,c_100830,c_104268]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_166439,plain,
% 39.48/5.50      ( k2_funct_1(sK2) = sK3
% 39.48/5.50      | v1_funct_1(sK3) != iProver_top
% 39.48/5.50      | v1_funct_1(sK2) != iProver_top
% 39.48/5.50      | v1_relat_1(sK3) != iProver_top
% 39.48/5.50      | v1_relat_1(sK2) != iProver_top
% 39.48/5.50      | v2_funct_1(sK2) != iProver_top ),
% 39.48/5.50      inference(equality_resolution_simp,[status(thm)],[c_166438]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_23,negated_conjecture,
% 39.48/5.50      ( k2_funct_1(sK2) != sK3 ),
% 39.48/5.50      inference(cnf_transformation,[],[f78]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_26,negated_conjecture,
% 39.48/5.50      ( v2_funct_1(sK2) ),
% 39.48/5.50      inference(cnf_transformation,[],[f75]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(c_42,plain,
% 39.48/5.50      ( v2_funct_1(sK2) = iProver_top ),
% 39.48/5.50      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.48/5.50  
% 39.48/5.50  cnf(contradiction,plain,
% 39.48/5.50      ( $false ),
% 39.48/5.50      inference(minisat,
% 39.48/5.50                [status(thm)],
% 39.48/5.50                [c_166439,c_60668,c_42040,c_23,c_42,c_40,c_38,c_37,c_35]) ).
% 39.48/5.50  
% 39.48/5.50  
% 39.48/5.50  % SZS output end CNFRefutation for theBenchmark.p
% 39.48/5.50  
% 39.48/5.50  ------                               Statistics
% 39.48/5.50  
% 39.48/5.50  ------ Selected
% 39.48/5.50  
% 39.48/5.50  total_time:                             4.575
% 39.48/5.50  
%------------------------------------------------------------------------------
