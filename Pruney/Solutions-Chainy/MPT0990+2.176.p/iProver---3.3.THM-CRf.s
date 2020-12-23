%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:34 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 869 expanded)
%              Number of clauses        :  112 ( 242 expanded)
%              Number of leaves         :   20 ( 232 expanded)
%              Depth                    :   22
%              Number of atoms          :  819 (8114 expanded)
%              Number of equality atoms :  332 (2848 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f43,plain,(
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
     => ( k2_funct_1(X2) != sK8
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & v2_funct_1(X2)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK8),k6_partfun1(X0))
        & k2_relset_1(X0,X1,X2) = X1
        & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(sK8,X1,X0)
        & v1_funct_1(sK8) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
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
          ( k2_funct_1(sK7) != X3
          & k1_xboole_0 != sK6
          & k1_xboole_0 != sK5
          & v2_funct_1(sK7)
          & r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,X3),k6_partfun1(sK5))
          & k2_relset_1(sK5,sK6,sK7) = sK6
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
          & v1_funct_2(X3,sK6,sK5)
          & v1_funct_1(X3) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( k2_funct_1(sK7) != sK8
    & k1_xboole_0 != sK6
    & k1_xboole_0 != sK5
    & v2_funct_1(sK7)
    & r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5))
    & k2_relset_1(sK5,sK6,sK7) = sK6
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    & v1_funct_2(sK8,sK6,sK5)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f28,f43,f42])).

fof(f78,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
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

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f77,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f44])).

fof(f86,plain,(
    k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f44])).

fof(f82,plain,(
    k2_relset_1(sK5,sK6,sK7) = sK6 ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f44])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f21])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f15,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f47,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f8,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f89,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f47,f59])).

fof(f81,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(cnf_transformation,[],[f44])).

fof(f79,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f44])).

fof(f29,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ! [X3] :
          ( ! [X4] :
              ( ! [X5] :
                  ( r2_relset_1(X1,X3,X4,X5)
                  | ~ r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                  | ~ v1_funct_2(X5,X1,X3)
                  | ~ v1_funct_1(X5) )
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
              | ~ v1_funct_2(X4,X1,X3)
              | ~ v1_funct_1(X4) )
          | k1_xboole_0 = X3 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f36,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_relset_1(X1,X3,X4,X5)
                    & r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    & v1_funct_2(X5,X1,X3)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                & v1_funct_2(X4,X1,X3)
                & v1_funct_1(X4) )
            & k1_xboole_0 != X3 ) )
      & ( ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r2_relset_1(X1,X3,X4,X5)
                    | ~ r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    | ~ v1_funct_2(X5,X1,X3)
                    | ~ v1_funct_1(X5) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                | ~ v1_funct_2(X4,X1,X3)
                | ~ v1_funct_1(X4) )
            | k1_xboole_0 = X3 )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ~ r2_relset_1(X0,X3,X4,X5)
                    & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5))
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
                    & v1_funct_2(X5,X0,X3)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
                & v1_funct_2(X4,X0,X3)
                & v1_funct_1(X4) )
            & k1_xboole_0 != X3 ) )
      & ( ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( r2_relset_1(X0,X6,X7,X8)
                    | ~ r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8))
                    | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
                    | ~ v1_funct_2(X8,X0,X6)
                    | ~ v1_funct_1(X8) )
                | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
                | ~ v1_funct_2(X7,X0,X6)
                | ~ v1_funct_1(X7) )
            | k1_xboole_0 = X6 )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f40,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ~ r2_relset_1(X0,X3,X4,X5)
          & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5))
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X5,X0,X3)
          & v1_funct_1(X5) )
     => ( ~ r2_relset_1(X0,X3,X4,sK4(X0,X1,X2))
        & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,sK4(X0,X1,X2)))
        & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_2(sK4(X0,X1,X2),X0,X3)
        & v1_funct_1(sK4(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ? [X5] :
              ( ~ r2_relset_1(X0,X3,X4,X5)
              & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5))
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X5,X0,X3)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
          & v1_funct_2(X4,X0,X3)
          & v1_funct_1(X4) )
     => ( ? [X5] :
            ( ~ r2_relset_1(X0,X3,sK3(X0,X1,X2),X5)
            & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,sK3(X0,X1,X2)),k1_partfun1(X2,X0,X0,X3,X1,X5))
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
            & v1_funct_2(X5,X0,X3)
            & v1_funct_1(X5) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_2(sK3(X0,X1,X2),X0,X3)
        & v1_funct_1(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ~ r2_relset_1(X0,X3,X4,X5)
                  & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5))
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
                  & v1_funct_2(X5,X0,X3)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
              & v1_funct_2(X4,X0,X3)
              & v1_funct_1(X4) )
          & k1_xboole_0 != X3 )
     => ( ? [X4] :
            ( ? [X5] :
                ( ~ r2_relset_1(X0,sK2(X0,X1,X2),X4,X5)
                & r2_relset_1(X2,sK2(X0,X1,X2),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,X4),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,X5))
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2))))
                & v1_funct_2(X5,X0,sK2(X0,X1,X2))
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2))))
            & v1_funct_2(X4,X0,sK2(X0,X1,X2))
            & v1_funct_1(X4) )
        & k1_xboole_0 != sK2(X0,X1,X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r2_relset_1(X0,sK2(X0,X1,X2),sK3(X0,X1,X2),sK4(X0,X1,X2))
          & r2_relset_1(X2,sK2(X0,X1,X2),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,sK3(X0,X1,X2)),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,sK4(X0,X1,X2)))
          & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2))))
          & v1_funct_2(sK4(X0,X1,X2),X0,sK2(X0,X1,X2))
          & v1_funct_1(sK4(X0,X1,X2))
          & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2))))
          & v1_funct_2(sK3(X0,X1,X2),X0,sK2(X0,X1,X2))
          & v1_funct_1(sK3(X0,X1,X2))
          & k1_xboole_0 != sK2(X0,X1,X2) ) )
      & ( ! [X6] :
            ( ! [X7] :
                ( ! [X8] :
                    ( r2_relset_1(X0,X6,X7,X8)
                    | ~ r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8))
                    | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
                    | ~ v1_funct_2(X8,X0,X6)
                    | ~ v1_funct_1(X8) )
                | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
                | ~ v1_funct_2(X7,X0,X6)
                | ~ v1_funct_1(X7) )
            | k1_xboole_0 = X6 )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).

fof(f62,plain,(
    ! [X6,X2,X0,X8,X7,X1] :
      ( r2_relset_1(X0,X6,X7,X8)
      | ~ r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8))
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
      | ~ v1_funct_2(X8,X0,X6)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6)))
      | ~ v1_funct_2(X7,X0,X6)
      | ~ v1_funct_1(X7)
      | k1_xboole_0 = X6
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f80,plain,(
    v1_funct_2(sK8,sK6,sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f85,plain,(
    k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( k1_xboole_0 != X1
       => ( k2_relset_1(X0,X1,X2) = X1
        <=> ! [X3] :
              ( k1_xboole_0 != X3
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    & v1_funct_2(X4,X1,X3)
                    & v1_funct_1(X4) )
                 => ! [X5] :
                      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                        & v1_funct_2(X5,X1,X3)
                        & v1_funct_1(X5) )
                     => ( r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                       => r2_relset_1(X1,X3,X4,X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) = X1
      <=> ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r2_relset_1(X1,X3,X4,X5)
                    | ~ r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    | ~ v1_funct_2(X5,X1,X3)
                    | ~ v1_funct_1(X5) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                | ~ v1_funct_2(X4,X1,X3)
                | ~ v1_funct_1(X4) )
            | k1_xboole_0 = X3 ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_relset_1(X0,X1,X2) = X1
      <=> ! [X3] :
            ( ! [X4] :
                ( ! [X5] :
                    ( r2_relset_1(X1,X3,X4,X5)
                    | ~ r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))
                    | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                    | ~ v1_funct_2(X5,X1,X3)
                    | ~ v1_funct_1(X5) )
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
                | ~ v1_funct_2(X4,X1,X3)
                | ~ v1_funct_1(X4) )
            | k1_xboole_0 = X3 ) )
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f23])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( k2_relset_1(X0,X1,X2) = X1
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f24,f30,f29])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( ( k2_relset_1(X0,X1,X2) = X1
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | k2_relset_1(X0,X1,X2) != X1 ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( k2_relset_1(X0,X2,X1) = X2
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | k2_relset_1(X0,X2,X1) != X2 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f34])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | k2_relset_1(X0,X2,X1) != X2
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f83,plain,(
    r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f17])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f87,plain,(
    k2_funct_1(sK7) != sK8 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2763,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_2782,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_5685,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_2782])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2790,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3971,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2763,c_2790])).

cnf(c_5697,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5685,c_3971])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_43,plain,
    ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_31,negated_conjecture,
    ( k1_xboole_0 != sK6 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2113,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2146,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2113])).

cnf(c_2114,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3131,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_2114])).

cnf(c_3132,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3131])).

cnf(c_7430,plain,
    ( k1_relat_1(sK7) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5697,c_43,c_31,c_2146,c_3132])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(sK5,sK6,sK7) = sK6 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK7) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_538,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_33])).

cnf(c_539,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK7)
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(unflattening,[status(thm)],[c_538])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_543,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK7,X0,X1)
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_41])).

cnf(c_544,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(renaming,[status(thm)],[c_543])).

cnf(c_2758,plain,
    ( k2_relset_1(X0,X1,sK7) != X1
    | v1_funct_2(sK7,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_3548,plain,
    ( v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_2758])).

cnf(c_44,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3088,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k2_relset_1(sK5,sK6,sK7) != sK6 ),
    inference(instantiation,[status(thm)],[c_544])).

cnf(c_3089,plain,
    ( k2_relset_1(sK5,sK6,sK7) != sK6
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3088])).

cnf(c_3693,plain,
    ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3548,c_43,c_44,c_35,c_3089])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2781,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5925,plain,
    ( k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3693,c_2781])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_490,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_33])).

cnf(c_491,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK7))
    | ~ v1_funct_1(sK7)
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_495,plain,
    ( v1_funct_1(k2_funct_1(sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK7,X0,X1)
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_491,c_41])).

cnf(c_496,plain,
    ( ~ v1_funct_2(sK7,X0,X1)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK7))
    | k2_relset_1(X0,X1,sK7) != X1 ),
    inference(renaming,[status(thm)],[c_495])).

cnf(c_3082,plain,
    ( ~ v1_funct_2(sK7,sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_funct_1(k2_funct_1(sK7))
    | k2_relset_1(sK5,sK6,sK7) != sK6 ),
    inference(instantiation,[status(thm)],[c_496])).

cnf(c_3083,plain,
    ( k2_relset_1(sK5,sK6,sK7) != sK6
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(k2_funct_1(sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3082])).

cnf(c_7000,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5925,c_43,c_44,c_35,c_3083])).

cnf(c_7001,plain,
    ( k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7))
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7000])).

cnf(c_7012,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k5_relat_1(sK7,k2_funct_1(sK7))
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_7001])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2792,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3984,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_2792])).

cnf(c_3097,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3445,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_3097])).

cnf(c_3446,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3445])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_3946,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3947,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3946])).

cnf(c_4294,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3984,c_44,c_3446,c_3947])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_562,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_33])).

cnf(c_563,plain,
    ( ~ v1_funct_1(sK7)
    | ~ v1_relat_1(sK7)
    | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7)) ),
    inference(unflattening,[status(thm)],[c_562])).

cnf(c_565,plain,
    ( ~ v1_relat_1(sK7)
    | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_563,c_41])).

cnf(c_2757,plain,
    ( k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7))
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_4299,plain,
    ( k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7)) ),
    inference(superposition,[status(thm)],[c_4294,c_2757])).

cnf(c_7020,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7))
    | v1_funct_1(sK7) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7012,c_4299])).

cnf(c_42,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_7187,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7020,c_42])).

cnf(c_7433,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k6_partfun1(sK5) ),
    inference(demodulation,[status(thm)],[c_7430,c_7187])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2766,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_5923,plain,
    ( k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2766,c_2781])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_45,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6091,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5923,c_45])).

cnf(c_6092,plain,
    ( k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_6091])).

cnf(c_6103,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8)
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_6092])).

cnf(c_3220,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK8)
    | k1_partfun1(X1,X2,X3,X4,X0,sK8) = k5_relat_1(X0,sK8) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_3562,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | k1_partfun1(X2,X3,X0,X1,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_3220])).

cnf(c_4028,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | k1_partfun1(X0,X1,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_3562])).

cnf(c_4114,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8)
    | ~ v1_funct_1(sK7)
    | k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4028])).

cnf(c_6166,plain,
    ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6103,c_41,c_39,c_38,c_36,c_4114])).

cnf(c_25,plain,
    ( r2_relset_1(X0,X1,X2,X3)
    | ~ r2_relset_1(X4,X1,k1_partfun1(X4,X0,X0,X1,X5,X2),k1_partfun1(X4,X0,X0,X1,X5,X3))
    | ~ sP0(X0,X5,X4)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2769,plain,
    ( k1_xboole_0 = X0
    | r2_relset_1(X1,X0,X2,X3) = iProver_top
    | r2_relset_1(X4,X0,k1_partfun1(X4,X1,X1,X0,X5,X2),k1_partfun1(X4,X1,X1,X0,X5,X3)) != iProver_top
    | sP0(X1,X5,X4) != iProver_top
    | v1_funct_2(X2,X1,X0) != iProver_top
    | v1_funct_2(X3,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6171,plain,
    ( sK5 = k1_xboole_0
    | r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
    | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
    | sP0(sK6,sK7,sK5) != iProver_top
    | v1_funct_2(X0,sK6,sK5) != iProver_top
    | v1_funct_2(sK8,sK6,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_6166,c_2769])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK8,sK6,sK5) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_46,plain,
    ( v1_funct_2(sK8,sK6,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_47,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_32,negated_conjecture,
    ( k1_xboole_0 != sK5 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3133,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_2114])).

cnf(c_3134,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3133])).

cnf(c_26,plain,
    ( sP1(X0,X1,X2)
    | ~ v1_funct_2(X1,X0,X2)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
    | ~ v1_funct_1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2768,plain,
    ( k1_xboole_0 = X0
    | sP1(X1,X2,X0) = iProver_top
    | v1_funct_2(X2,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3839,plain,
    ( sK6 = k1_xboole_0
    | sP1(sK5,sK7,sK6) = iProver_top
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2763,c_2768])).

cnf(c_15,plain,
    ( ~ sP1(X0,X1,X2)
    | sP0(X2,X1,X0)
    | k2_relset_1(X0,X2,X1) != X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2779,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | sP1(X0,X2,X1) != iProver_top
    | sP0(X1,X2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_5009,plain,
    ( sP1(sK5,sK7,sK6) != iProver_top
    | sP0(sK6,sK7,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_35,c_2779])).

cnf(c_9285,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_2(X0,sK6,sK5) != iProver_top
    | r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
    | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6171,c_42,c_43,c_45,c_46,c_47,c_32,c_31,c_2146,c_3132,c_3134,c_3839,c_5009])).

cnf(c_9286,plain,
    ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
    | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
    | v1_funct_2(X0,sK6,sK5) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9285])).

cnf(c_9683,plain,
    ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k6_partfun1(sK5)) != iProver_top
    | r2_relset_1(sK6,sK5,sK8,k2_funct_1(sK7)) = iProver_top
    | v1_funct_2(k2_funct_1(sK7),sK6,sK5) != iProver_top
    | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
    | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7433,c_9286])).

cnf(c_34,negated_conjecture,
    ( r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2767,plain,
    ( r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_6169,plain,
    ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k6_partfun1(sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6166,c_2767])).

cnf(c_6,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_2788,plain,
    ( X0 = X1
    | r2_relset_1(X2,X3,X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_5410,plain,
    ( sK8 = X0
    | r2_relset_1(sK6,sK5,sK8,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2766,c_2788])).

cnf(c_5467,plain,
    ( k2_funct_1(sK7) = sK8
    | r2_relset_1(sK6,sK5,sK8,k2_funct_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3693,c_5410])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_514,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK7 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_33])).

cnf(c_515,plain,
    ( v1_funct_2(k2_funct_1(sK7),X0,X1)
    | ~ v1_funct_2(sK7,X1,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK7)
    | k2_relset_1(X1,X0,sK7) != X0 ),
    inference(unflattening,[status(thm)],[c_514])).

cnf(c_519,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK7,X1,X0)
    | v1_funct_2(k2_funct_1(sK7),X0,X1)
    | k2_relset_1(X1,X0,sK7) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_41])).

cnf(c_520,plain,
    ( v1_funct_2(k2_funct_1(sK7),X0,X1)
    | ~ v1_funct_2(sK7,X1,X0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK7) != X0 ),
    inference(renaming,[status(thm)],[c_519])).

cnf(c_3085,plain,
    ( v1_funct_2(k2_funct_1(sK7),sK6,sK5)
    | ~ v1_funct_2(sK7,sK5,sK6)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k2_relset_1(sK5,sK6,sK7) != sK6 ),
    inference(instantiation,[status(thm)],[c_520])).

cnf(c_3086,plain,
    ( k2_relset_1(sK5,sK6,sK7) != sK6
    | v1_funct_2(k2_funct_1(sK7),sK6,sK5) = iProver_top
    | v1_funct_2(sK7,sK5,sK6) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3085])).

cnf(c_30,negated_conjecture,
    ( k2_funct_1(sK7) != sK8 ),
    inference(cnf_transformation,[],[f87])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9683,c_6169,c_5467,c_3089,c_3086,c_3083,c_30,c_35,c_44,c_43])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:06:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.73/1.04  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.04  
% 2.73/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/1.04  
% 2.73/1.04  ------  iProver source info
% 2.73/1.04  
% 2.73/1.04  git: date: 2020-06-30 10:37:57 +0100
% 2.73/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/1.04  git: non_committed_changes: false
% 2.73/1.04  git: last_make_outside_of_git: false
% 2.73/1.04  
% 2.73/1.04  ------ 
% 2.73/1.04  
% 2.73/1.04  ------ Input Options
% 2.73/1.04  
% 2.73/1.04  --out_options                           all
% 2.73/1.04  --tptp_safe_out                         true
% 2.73/1.04  --problem_path                          ""
% 2.73/1.04  --include_path                          ""
% 2.73/1.04  --clausifier                            res/vclausify_rel
% 2.73/1.04  --clausifier_options                    --mode clausify
% 2.73/1.04  --stdin                                 false
% 2.73/1.04  --stats_out                             all
% 2.73/1.04  
% 2.73/1.04  ------ General Options
% 2.73/1.04  
% 2.73/1.04  --fof                                   false
% 2.73/1.04  --time_out_real                         305.
% 2.73/1.04  --time_out_virtual                      -1.
% 2.73/1.04  --symbol_type_check                     false
% 2.73/1.04  --clausify_out                          false
% 2.73/1.04  --sig_cnt_out                           false
% 2.73/1.04  --trig_cnt_out                          false
% 2.73/1.04  --trig_cnt_out_tolerance                1.
% 2.73/1.04  --trig_cnt_out_sk_spl                   false
% 2.73/1.04  --abstr_cl_out                          false
% 2.73/1.04  
% 2.73/1.04  ------ Global Options
% 2.73/1.04  
% 2.73/1.04  --schedule                              default
% 2.73/1.04  --add_important_lit                     false
% 2.73/1.04  --prop_solver_per_cl                    1000
% 2.73/1.04  --min_unsat_core                        false
% 2.73/1.04  --soft_assumptions                      false
% 2.73/1.04  --soft_lemma_size                       3
% 2.73/1.04  --prop_impl_unit_size                   0
% 2.73/1.04  --prop_impl_unit                        []
% 2.73/1.04  --share_sel_clauses                     true
% 2.73/1.04  --reset_solvers                         false
% 2.73/1.04  --bc_imp_inh                            [conj_cone]
% 2.73/1.04  --conj_cone_tolerance                   3.
% 2.73/1.04  --extra_neg_conj                        none
% 2.73/1.04  --large_theory_mode                     true
% 2.73/1.04  --prolific_symb_bound                   200
% 2.73/1.04  --lt_threshold                          2000
% 2.73/1.04  --clause_weak_htbl                      true
% 2.73/1.04  --gc_record_bc_elim                     false
% 2.73/1.04  
% 2.73/1.04  ------ Preprocessing Options
% 2.73/1.04  
% 2.73/1.04  --preprocessing_flag                    true
% 2.73/1.04  --time_out_prep_mult                    0.1
% 2.73/1.04  --splitting_mode                        input
% 2.73/1.04  --splitting_grd                         true
% 2.73/1.04  --splitting_cvd                         false
% 2.73/1.04  --splitting_cvd_svl                     false
% 2.73/1.04  --splitting_nvd                         32
% 2.73/1.04  --sub_typing                            true
% 2.73/1.04  --prep_gs_sim                           true
% 2.73/1.04  --prep_unflatten                        true
% 2.73/1.04  --prep_res_sim                          true
% 2.73/1.04  --prep_upred                            true
% 2.73/1.04  --prep_sem_filter                       exhaustive
% 2.73/1.04  --prep_sem_filter_out                   false
% 2.73/1.04  --pred_elim                             true
% 2.73/1.04  --res_sim_input                         true
% 2.73/1.04  --eq_ax_congr_red                       true
% 2.73/1.04  --pure_diseq_elim                       true
% 2.73/1.04  --brand_transform                       false
% 2.73/1.04  --non_eq_to_eq                          false
% 2.73/1.04  --prep_def_merge                        true
% 2.73/1.04  --prep_def_merge_prop_impl              false
% 2.73/1.04  --prep_def_merge_mbd                    true
% 2.73/1.04  --prep_def_merge_tr_red                 false
% 2.73/1.04  --prep_def_merge_tr_cl                  false
% 2.73/1.04  --smt_preprocessing                     true
% 2.73/1.04  --smt_ac_axioms                         fast
% 2.73/1.04  --preprocessed_out                      false
% 2.73/1.04  --preprocessed_stats                    false
% 2.73/1.04  
% 2.73/1.04  ------ Abstraction refinement Options
% 2.73/1.04  
% 2.73/1.04  --abstr_ref                             []
% 2.73/1.04  --abstr_ref_prep                        false
% 2.73/1.04  --abstr_ref_until_sat                   false
% 2.73/1.04  --abstr_ref_sig_restrict                funpre
% 2.73/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.04  --abstr_ref_under                       []
% 2.73/1.04  
% 2.73/1.04  ------ SAT Options
% 2.73/1.04  
% 2.73/1.04  --sat_mode                              false
% 2.73/1.04  --sat_fm_restart_options                ""
% 2.73/1.04  --sat_gr_def                            false
% 2.73/1.04  --sat_epr_types                         true
% 2.73/1.04  --sat_non_cyclic_types                  false
% 2.73/1.04  --sat_finite_models                     false
% 2.73/1.04  --sat_fm_lemmas                         false
% 2.73/1.04  --sat_fm_prep                           false
% 2.73/1.04  --sat_fm_uc_incr                        true
% 2.73/1.04  --sat_out_model                         small
% 2.73/1.04  --sat_out_clauses                       false
% 2.73/1.04  
% 2.73/1.04  ------ QBF Options
% 2.73/1.04  
% 2.73/1.04  --qbf_mode                              false
% 2.73/1.04  --qbf_elim_univ                         false
% 2.73/1.04  --qbf_dom_inst                          none
% 2.73/1.04  --qbf_dom_pre_inst                      false
% 2.73/1.04  --qbf_sk_in                             false
% 2.73/1.04  --qbf_pred_elim                         true
% 2.73/1.04  --qbf_split                             512
% 2.73/1.04  
% 2.73/1.04  ------ BMC1 Options
% 2.73/1.04  
% 2.73/1.04  --bmc1_incremental                      false
% 2.73/1.04  --bmc1_axioms                           reachable_all
% 2.73/1.04  --bmc1_min_bound                        0
% 2.73/1.04  --bmc1_max_bound                        -1
% 2.73/1.04  --bmc1_max_bound_default                -1
% 2.73/1.04  --bmc1_symbol_reachability              true
% 2.73/1.04  --bmc1_property_lemmas                  false
% 2.73/1.04  --bmc1_k_induction                      false
% 2.73/1.04  --bmc1_non_equiv_states                 false
% 2.73/1.04  --bmc1_deadlock                         false
% 2.73/1.04  --bmc1_ucm                              false
% 2.73/1.04  --bmc1_add_unsat_core                   none
% 2.73/1.04  --bmc1_unsat_core_children              false
% 2.73/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.04  --bmc1_out_stat                         full
% 2.73/1.04  --bmc1_ground_init                      false
% 2.73/1.04  --bmc1_pre_inst_next_state              false
% 2.73/1.04  --bmc1_pre_inst_state                   false
% 2.73/1.04  --bmc1_pre_inst_reach_state             false
% 2.73/1.04  --bmc1_out_unsat_core                   false
% 2.73/1.04  --bmc1_aig_witness_out                  false
% 2.73/1.04  --bmc1_verbose                          false
% 2.73/1.04  --bmc1_dump_clauses_tptp                false
% 2.73/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.04  --bmc1_dump_file                        -
% 2.73/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.04  --bmc1_ucm_extend_mode                  1
% 2.73/1.04  --bmc1_ucm_init_mode                    2
% 2.73/1.04  --bmc1_ucm_cone_mode                    none
% 2.73/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.04  --bmc1_ucm_relax_model                  4
% 2.73/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.04  --bmc1_ucm_layered_model                none
% 2.73/1.04  --bmc1_ucm_max_lemma_size               10
% 2.73/1.04  
% 2.73/1.04  ------ AIG Options
% 2.73/1.04  
% 2.73/1.04  --aig_mode                              false
% 2.73/1.04  
% 2.73/1.04  ------ Instantiation Options
% 2.73/1.04  
% 2.73/1.04  --instantiation_flag                    true
% 2.73/1.04  --inst_sos_flag                         false
% 2.73/1.04  --inst_sos_phase                        true
% 2.73/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.04  --inst_lit_sel_side                     num_symb
% 2.73/1.04  --inst_solver_per_active                1400
% 2.73/1.04  --inst_solver_calls_frac                1.
% 2.73/1.04  --inst_passive_queue_type               priority_queues
% 2.73/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.04  --inst_passive_queues_freq              [25;2]
% 2.73/1.04  --inst_dismatching                      true
% 2.73/1.04  --inst_eager_unprocessed_to_passive     true
% 2.73/1.04  --inst_prop_sim_given                   true
% 2.73/1.04  --inst_prop_sim_new                     false
% 2.73/1.04  --inst_subs_new                         false
% 2.73/1.04  --inst_eq_res_simp                      false
% 2.73/1.04  --inst_subs_given                       false
% 2.73/1.04  --inst_orphan_elimination               true
% 2.73/1.04  --inst_learning_loop_flag               true
% 2.73/1.04  --inst_learning_start                   3000
% 2.73/1.04  --inst_learning_factor                  2
% 2.73/1.04  --inst_start_prop_sim_after_learn       3
% 2.73/1.04  --inst_sel_renew                        solver
% 2.73/1.04  --inst_lit_activity_flag                true
% 2.73/1.04  --inst_restr_to_given                   false
% 2.73/1.04  --inst_activity_threshold               500
% 2.73/1.04  --inst_out_proof                        true
% 2.73/1.04  
% 2.73/1.04  ------ Resolution Options
% 2.73/1.04  
% 2.73/1.04  --resolution_flag                       true
% 2.73/1.04  --res_lit_sel                           adaptive
% 2.73/1.04  --res_lit_sel_side                      none
% 2.73/1.04  --res_ordering                          kbo
% 2.73/1.04  --res_to_prop_solver                    active
% 2.73/1.04  --res_prop_simpl_new                    false
% 2.73/1.04  --res_prop_simpl_given                  true
% 2.73/1.04  --res_passive_queue_type                priority_queues
% 2.73/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.04  --res_passive_queues_freq               [15;5]
% 2.73/1.04  --res_forward_subs                      full
% 2.73/1.04  --res_backward_subs                     full
% 2.73/1.04  --res_forward_subs_resolution           true
% 2.73/1.04  --res_backward_subs_resolution          true
% 2.73/1.04  --res_orphan_elimination                true
% 2.73/1.04  --res_time_limit                        2.
% 2.73/1.04  --res_out_proof                         true
% 2.73/1.04  
% 2.73/1.04  ------ Superposition Options
% 2.73/1.04  
% 2.73/1.04  --superposition_flag                    true
% 2.73/1.04  --sup_passive_queue_type                priority_queues
% 2.73/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.04  --demod_completeness_check              fast
% 2.73/1.04  --demod_use_ground                      true
% 2.73/1.04  --sup_to_prop_solver                    passive
% 2.73/1.04  --sup_prop_simpl_new                    true
% 2.73/1.04  --sup_prop_simpl_given                  true
% 2.73/1.04  --sup_fun_splitting                     false
% 2.73/1.04  --sup_smt_interval                      50000
% 2.73/1.04  
% 2.73/1.04  ------ Superposition Simplification Setup
% 2.73/1.04  
% 2.73/1.04  --sup_indices_passive                   []
% 2.73/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.04  --sup_full_bw                           [BwDemod]
% 2.73/1.04  --sup_immed_triv                        [TrivRules]
% 2.73/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.04  --sup_immed_bw_main                     []
% 2.73/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.04  
% 2.73/1.04  ------ Combination Options
% 2.73/1.04  
% 2.73/1.04  --comb_res_mult                         3
% 2.73/1.04  --comb_sup_mult                         2
% 2.73/1.04  --comb_inst_mult                        10
% 2.73/1.04  
% 2.73/1.04  ------ Debug Options
% 2.73/1.04  
% 2.73/1.04  --dbg_backtrace                         false
% 2.73/1.04  --dbg_dump_prop_clauses                 false
% 2.73/1.04  --dbg_dump_prop_clauses_file            -
% 2.73/1.04  --dbg_out_stat                          false
% 2.73/1.04  ------ Parsing...
% 2.73/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/1.04  
% 2.73/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.73/1.04  
% 2.73/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/1.04  
% 2.73/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/1.04  ------ Proving...
% 2.73/1.04  ------ Problem Properties 
% 2.73/1.04  
% 2.73/1.04  
% 2.73/1.04  clauses                                 41
% 2.73/1.04  conjectures                             11
% 2.73/1.04  EPR                                     6
% 2.73/1.04  Horn                                    28
% 2.73/1.04  unary                                   12
% 2.73/1.04  binary                                  13
% 2.73/1.04  lits                                    104
% 2.73/1.04  lits eq                                 26
% 2.73/1.04  fd_pure                                 0
% 2.73/1.04  fd_pseudo                               0
% 2.73/1.04  fd_cond                                 5
% 2.73/1.04  fd_pseudo_cond                          1
% 2.73/1.04  AC symbols                              0
% 2.73/1.04  
% 2.73/1.04  ------ Schedule dynamic 5 is on 
% 2.73/1.04  
% 2.73/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/1.04  
% 2.73/1.04  
% 2.73/1.04  ------ 
% 2.73/1.04  Current options:
% 2.73/1.04  ------ 
% 2.73/1.04  
% 2.73/1.04  ------ Input Options
% 2.73/1.04  
% 2.73/1.04  --out_options                           all
% 2.73/1.04  --tptp_safe_out                         true
% 2.73/1.04  --problem_path                          ""
% 2.73/1.04  --include_path                          ""
% 2.73/1.04  --clausifier                            res/vclausify_rel
% 2.73/1.04  --clausifier_options                    --mode clausify
% 2.73/1.04  --stdin                                 false
% 2.73/1.04  --stats_out                             all
% 2.73/1.04  
% 2.73/1.04  ------ General Options
% 2.73/1.04  
% 2.73/1.04  --fof                                   false
% 2.73/1.04  --time_out_real                         305.
% 2.73/1.04  --time_out_virtual                      -1.
% 2.73/1.04  --symbol_type_check                     false
% 2.73/1.04  --clausify_out                          false
% 2.73/1.04  --sig_cnt_out                           false
% 2.73/1.04  --trig_cnt_out                          false
% 2.73/1.04  --trig_cnt_out_tolerance                1.
% 2.73/1.04  --trig_cnt_out_sk_spl                   false
% 2.73/1.04  --abstr_cl_out                          false
% 2.73/1.04  
% 2.73/1.04  ------ Global Options
% 2.73/1.04  
% 2.73/1.04  --schedule                              default
% 2.73/1.04  --add_important_lit                     false
% 2.73/1.04  --prop_solver_per_cl                    1000
% 2.73/1.04  --min_unsat_core                        false
% 2.73/1.04  --soft_assumptions                      false
% 2.73/1.04  --soft_lemma_size                       3
% 2.73/1.04  --prop_impl_unit_size                   0
% 2.73/1.04  --prop_impl_unit                        []
% 2.73/1.04  --share_sel_clauses                     true
% 2.73/1.04  --reset_solvers                         false
% 2.73/1.04  --bc_imp_inh                            [conj_cone]
% 2.73/1.04  --conj_cone_tolerance                   3.
% 2.73/1.04  --extra_neg_conj                        none
% 2.73/1.04  --large_theory_mode                     true
% 2.73/1.04  --prolific_symb_bound                   200
% 2.73/1.04  --lt_threshold                          2000
% 2.73/1.04  --clause_weak_htbl                      true
% 2.73/1.04  --gc_record_bc_elim                     false
% 2.73/1.04  
% 2.73/1.04  ------ Preprocessing Options
% 2.73/1.04  
% 2.73/1.04  --preprocessing_flag                    true
% 2.73/1.04  --time_out_prep_mult                    0.1
% 2.73/1.04  --splitting_mode                        input
% 2.73/1.04  --splitting_grd                         true
% 2.73/1.04  --splitting_cvd                         false
% 2.73/1.04  --splitting_cvd_svl                     false
% 2.73/1.04  --splitting_nvd                         32
% 2.73/1.04  --sub_typing                            true
% 2.73/1.04  --prep_gs_sim                           true
% 2.73/1.04  --prep_unflatten                        true
% 2.73/1.04  --prep_res_sim                          true
% 2.73/1.04  --prep_upred                            true
% 2.73/1.04  --prep_sem_filter                       exhaustive
% 2.73/1.04  --prep_sem_filter_out                   false
% 2.73/1.04  --pred_elim                             true
% 2.73/1.04  --res_sim_input                         true
% 2.73/1.04  --eq_ax_congr_red                       true
% 2.73/1.04  --pure_diseq_elim                       true
% 2.73/1.04  --brand_transform                       false
% 2.73/1.04  --non_eq_to_eq                          false
% 2.73/1.04  --prep_def_merge                        true
% 2.73/1.04  --prep_def_merge_prop_impl              false
% 2.73/1.04  --prep_def_merge_mbd                    true
% 2.73/1.04  --prep_def_merge_tr_red                 false
% 2.73/1.04  --prep_def_merge_tr_cl                  false
% 2.73/1.04  --smt_preprocessing                     true
% 2.73/1.04  --smt_ac_axioms                         fast
% 2.73/1.04  --preprocessed_out                      false
% 2.73/1.04  --preprocessed_stats                    false
% 2.73/1.04  
% 2.73/1.04  ------ Abstraction refinement Options
% 2.73/1.04  
% 2.73/1.04  --abstr_ref                             []
% 2.73/1.04  --abstr_ref_prep                        false
% 2.73/1.04  --abstr_ref_until_sat                   false
% 2.73/1.04  --abstr_ref_sig_restrict                funpre
% 2.73/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.04  --abstr_ref_under                       []
% 2.73/1.04  
% 2.73/1.04  ------ SAT Options
% 2.73/1.04  
% 2.73/1.04  --sat_mode                              false
% 2.73/1.04  --sat_fm_restart_options                ""
% 2.73/1.04  --sat_gr_def                            false
% 2.73/1.04  --sat_epr_types                         true
% 2.73/1.04  --sat_non_cyclic_types                  false
% 2.73/1.04  --sat_finite_models                     false
% 2.73/1.04  --sat_fm_lemmas                         false
% 2.73/1.04  --sat_fm_prep                           false
% 2.73/1.04  --sat_fm_uc_incr                        true
% 2.73/1.04  --sat_out_model                         small
% 2.73/1.04  --sat_out_clauses                       false
% 2.73/1.04  
% 2.73/1.04  ------ QBF Options
% 2.73/1.04  
% 2.73/1.04  --qbf_mode                              false
% 2.73/1.04  --qbf_elim_univ                         false
% 2.73/1.04  --qbf_dom_inst                          none
% 2.73/1.04  --qbf_dom_pre_inst                      false
% 2.73/1.04  --qbf_sk_in                             false
% 2.73/1.04  --qbf_pred_elim                         true
% 2.73/1.04  --qbf_split                             512
% 2.73/1.04  
% 2.73/1.04  ------ BMC1 Options
% 2.73/1.04  
% 2.73/1.04  --bmc1_incremental                      false
% 2.73/1.04  --bmc1_axioms                           reachable_all
% 2.73/1.04  --bmc1_min_bound                        0
% 2.73/1.04  --bmc1_max_bound                        -1
% 2.73/1.04  --bmc1_max_bound_default                -1
% 2.73/1.04  --bmc1_symbol_reachability              true
% 2.73/1.04  --bmc1_property_lemmas                  false
% 2.73/1.04  --bmc1_k_induction                      false
% 2.73/1.04  --bmc1_non_equiv_states                 false
% 2.73/1.04  --bmc1_deadlock                         false
% 2.73/1.04  --bmc1_ucm                              false
% 2.73/1.04  --bmc1_add_unsat_core                   none
% 2.73/1.04  --bmc1_unsat_core_children              false
% 2.73/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.04  --bmc1_out_stat                         full
% 2.73/1.04  --bmc1_ground_init                      false
% 2.73/1.04  --bmc1_pre_inst_next_state              false
% 2.73/1.04  --bmc1_pre_inst_state                   false
% 2.73/1.04  --bmc1_pre_inst_reach_state             false
% 2.73/1.04  --bmc1_out_unsat_core                   false
% 2.73/1.04  --bmc1_aig_witness_out                  false
% 2.73/1.04  --bmc1_verbose                          false
% 2.73/1.04  --bmc1_dump_clauses_tptp                false
% 2.73/1.04  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.04  --bmc1_dump_file                        -
% 2.73/1.04  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.04  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.04  --bmc1_ucm_extend_mode                  1
% 2.73/1.04  --bmc1_ucm_init_mode                    2
% 2.73/1.04  --bmc1_ucm_cone_mode                    none
% 2.73/1.04  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.04  --bmc1_ucm_relax_model                  4
% 2.73/1.04  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.04  --bmc1_ucm_layered_model                none
% 2.73/1.04  --bmc1_ucm_max_lemma_size               10
% 2.73/1.04  
% 2.73/1.04  ------ AIG Options
% 2.73/1.04  
% 2.73/1.04  --aig_mode                              false
% 2.73/1.04  
% 2.73/1.04  ------ Instantiation Options
% 2.73/1.04  
% 2.73/1.04  --instantiation_flag                    true
% 2.73/1.04  --inst_sos_flag                         false
% 2.73/1.04  --inst_sos_phase                        true
% 2.73/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.04  --inst_lit_sel_side                     none
% 2.73/1.04  --inst_solver_per_active                1400
% 2.73/1.04  --inst_solver_calls_frac                1.
% 2.73/1.04  --inst_passive_queue_type               priority_queues
% 2.73/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.04  --inst_passive_queues_freq              [25;2]
% 2.73/1.04  --inst_dismatching                      true
% 2.73/1.04  --inst_eager_unprocessed_to_passive     true
% 2.73/1.04  --inst_prop_sim_given                   true
% 2.73/1.04  --inst_prop_sim_new                     false
% 2.73/1.04  --inst_subs_new                         false
% 2.73/1.04  --inst_eq_res_simp                      false
% 2.73/1.04  --inst_subs_given                       false
% 2.73/1.04  --inst_orphan_elimination               true
% 2.73/1.04  --inst_learning_loop_flag               true
% 2.73/1.04  --inst_learning_start                   3000
% 2.73/1.04  --inst_learning_factor                  2
% 2.73/1.04  --inst_start_prop_sim_after_learn       3
% 2.73/1.04  --inst_sel_renew                        solver
% 2.73/1.04  --inst_lit_activity_flag                true
% 2.73/1.04  --inst_restr_to_given                   false
% 2.73/1.04  --inst_activity_threshold               500
% 2.73/1.04  --inst_out_proof                        true
% 2.73/1.04  
% 2.73/1.04  ------ Resolution Options
% 2.73/1.04  
% 2.73/1.04  --resolution_flag                       false
% 2.73/1.04  --res_lit_sel                           adaptive
% 2.73/1.04  --res_lit_sel_side                      none
% 2.73/1.04  --res_ordering                          kbo
% 2.73/1.04  --res_to_prop_solver                    active
% 2.73/1.04  --res_prop_simpl_new                    false
% 2.73/1.04  --res_prop_simpl_given                  true
% 2.73/1.04  --res_passive_queue_type                priority_queues
% 2.73/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.04  --res_passive_queues_freq               [15;5]
% 2.73/1.04  --res_forward_subs                      full
% 2.73/1.04  --res_backward_subs                     full
% 2.73/1.04  --res_forward_subs_resolution           true
% 2.73/1.04  --res_backward_subs_resolution          true
% 2.73/1.04  --res_orphan_elimination                true
% 2.73/1.04  --res_time_limit                        2.
% 2.73/1.04  --res_out_proof                         true
% 2.73/1.04  
% 2.73/1.04  ------ Superposition Options
% 2.73/1.04  
% 2.73/1.04  --superposition_flag                    true
% 2.73/1.04  --sup_passive_queue_type                priority_queues
% 2.73/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.04  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.04  --demod_completeness_check              fast
% 2.73/1.05  --demod_use_ground                      true
% 2.73/1.05  --sup_to_prop_solver                    passive
% 2.73/1.05  --sup_prop_simpl_new                    true
% 2.73/1.05  --sup_prop_simpl_given                  true
% 2.73/1.05  --sup_fun_splitting                     false
% 2.73/1.05  --sup_smt_interval                      50000
% 2.73/1.05  
% 2.73/1.05  ------ Superposition Simplification Setup
% 2.73/1.05  
% 2.73/1.05  --sup_indices_passive                   []
% 2.73/1.05  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.05  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.05  --sup_full_bw                           [BwDemod]
% 2.73/1.05  --sup_immed_triv                        [TrivRules]
% 2.73/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.05  --sup_immed_bw_main                     []
% 2.73/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.05  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.05  
% 2.73/1.05  ------ Combination Options
% 2.73/1.05  
% 2.73/1.05  --comb_res_mult                         3
% 2.73/1.05  --comb_sup_mult                         2
% 2.73/1.05  --comb_inst_mult                        10
% 2.73/1.05  
% 2.73/1.05  ------ Debug Options
% 2.73/1.05  
% 2.73/1.05  --dbg_backtrace                         false
% 2.73/1.05  --dbg_dump_prop_clauses                 false
% 2.73/1.05  --dbg_dump_prop_clauses_file            -
% 2.73/1.05  --dbg_out_stat                          false
% 2.73/1.05  
% 2.73/1.05  
% 2.73/1.05  
% 2.73/1.05  
% 2.73/1.05  ------ Proving...
% 2.73/1.05  
% 2.73/1.05  
% 2.73/1.05  % SZS status Theorem for theBenchmark.p
% 2.73/1.05  
% 2.73/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/1.05  
% 2.73/1.05  fof(f11,conjecture,(
% 2.73/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.73/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.05  
% 2.73/1.05  fof(f12,negated_conjecture,(
% 2.73/1.05    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.73/1.05    inference(negated_conjecture,[],[f11])).
% 2.73/1.05  
% 2.73/1.05  fof(f27,plain,(
% 2.73/1.05    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.73/1.05    inference(ennf_transformation,[],[f12])).
% 2.73/1.05  
% 2.73/1.05  fof(f28,plain,(
% 2.73/1.05    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.73/1.05    inference(flattening,[],[f27])).
% 2.73/1.05  
% 2.73/1.05  fof(f43,plain,(
% 2.73/1.05    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK8 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK8),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK8,X1,X0) & v1_funct_1(sK8))) )),
% 2.73/1.05    introduced(choice_axiom,[])).
% 2.73/1.05  
% 2.73/1.05  fof(f42,plain,(
% 2.73/1.05    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK7) != X3 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & v2_funct_1(sK7) & r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,X3),k6_partfun1(sK5)) & k2_relset_1(sK5,sK6,sK7) = sK6 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) & v1_funct_2(X3,sK6,sK5) & v1_funct_1(X3)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 2.73/1.05    introduced(choice_axiom,[])).
% 2.73/1.05  
% 2.73/1.05  fof(f44,plain,(
% 2.73/1.05    (k2_funct_1(sK7) != sK8 & k1_xboole_0 != sK6 & k1_xboole_0 != sK5 & v2_funct_1(sK7) & r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) & k2_relset_1(sK5,sK6,sK7) = sK6 & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) & v1_funct_2(sK8,sK6,sK5) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 2.73/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f28,f43,f42])).
% 2.73/1.05  
% 2.73/1.05  fof(f78,plain,(
% 2.73/1.05    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  fof(f6,axiom,(
% 2.73/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.73/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.05  
% 2.73/1.05  fof(f19,plain,(
% 2.73/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.05    inference(ennf_transformation,[],[f6])).
% 2.73/1.05  
% 2.73/1.05  fof(f20,plain,(
% 2.73/1.05    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.05    inference(flattening,[],[f19])).
% 2.73/1.05  
% 2.73/1.05  fof(f33,plain,(
% 2.73/1.05    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.05    inference(nnf_transformation,[],[f20])).
% 2.73/1.05  
% 2.73/1.05  fof(f52,plain,(
% 2.73/1.05    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/1.05    inference(cnf_transformation,[],[f33])).
% 2.73/1.05  
% 2.73/1.05  fof(f4,axiom,(
% 2.73/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.73/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.05  
% 2.73/1.05  fof(f16,plain,(
% 2.73/1.05    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.05    inference(ennf_transformation,[],[f4])).
% 2.73/1.05  
% 2.73/1.05  fof(f49,plain,(
% 2.73/1.05    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/1.05    inference(cnf_transformation,[],[f16])).
% 2.73/1.05  
% 2.73/1.05  fof(f77,plain,(
% 2.73/1.05    v1_funct_2(sK7,sK5,sK6)),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  fof(f86,plain,(
% 2.73/1.05    k1_xboole_0 != sK6),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  fof(f82,plain,(
% 2.73/1.05    k2_relset_1(sK5,sK6,sK7) = sK6),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  fof(f10,axiom,(
% 2.73/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.73/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.05  
% 2.73/1.05  fof(f25,plain,(
% 2.73/1.05    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.73/1.05    inference(ennf_transformation,[],[f10])).
% 2.73/1.05  
% 2.73/1.05  fof(f26,plain,(
% 2.73/1.05    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.73/1.05    inference(flattening,[],[f25])).
% 2.73/1.05  
% 2.73/1.05  fof(f75,plain,(
% 2.73/1.05    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.73/1.05    inference(cnf_transformation,[],[f26])).
% 2.73/1.05  
% 2.73/1.05  fof(f84,plain,(
% 2.73/1.05    v2_funct_1(sK7)),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  fof(f76,plain,(
% 2.73/1.05    v1_funct_1(sK7)),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  fof(f7,axiom,(
% 2.73/1.05    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 2.73/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.05  
% 2.73/1.05  fof(f21,plain,(
% 2.73/1.05    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.73/1.05    inference(ennf_transformation,[],[f7])).
% 2.73/1.05  
% 2.73/1.05  fof(f22,plain,(
% 2.73/1.05    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.73/1.05    inference(flattening,[],[f21])).
% 2.73/1.05  
% 2.73/1.05  fof(f58,plain,(
% 2.73/1.05    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.73/1.05    inference(cnf_transformation,[],[f22])).
% 2.73/1.05  
% 2.73/1.05  fof(f73,plain,(
% 2.73/1.05    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.73/1.05    inference(cnf_transformation,[],[f26])).
% 2.73/1.05  
% 2.73/1.05  fof(f1,axiom,(
% 2.73/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.73/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.05  
% 2.73/1.05  fof(f13,plain,(
% 2.73/1.05    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.73/1.05    inference(ennf_transformation,[],[f1])).
% 2.73/1.05  
% 2.73/1.05  fof(f45,plain,(
% 2.73/1.05    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.73/1.05    inference(cnf_transformation,[],[f13])).
% 2.73/1.05  
% 2.73/1.05  fof(f2,axiom,(
% 2.73/1.05    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.73/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.05  
% 2.73/1.05  fof(f46,plain,(
% 2.73/1.05    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.73/1.05    inference(cnf_transformation,[],[f2])).
% 2.73/1.05  
% 2.73/1.05  fof(f3,axiom,(
% 2.73/1.05    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.73/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.05  
% 2.73/1.05  fof(f14,plain,(
% 2.73/1.05    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.73/1.05    inference(ennf_transformation,[],[f3])).
% 2.73/1.05  
% 2.73/1.05  fof(f15,plain,(
% 2.73/1.05    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.73/1.05    inference(flattening,[],[f14])).
% 2.73/1.05  
% 2.73/1.05  fof(f47,plain,(
% 2.73/1.05    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/1.05    inference(cnf_transformation,[],[f15])).
% 2.73/1.05  
% 2.73/1.05  fof(f8,axiom,(
% 2.73/1.05    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.73/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.05  
% 2.73/1.05  fof(f59,plain,(
% 2.73/1.05    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.73/1.05    inference(cnf_transformation,[],[f8])).
% 2.73/1.05  
% 2.73/1.05  fof(f89,plain,(
% 2.73/1.05    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/1.05    inference(definition_unfolding,[],[f47,f59])).
% 2.73/1.05  
% 2.73/1.05  fof(f81,plain,(
% 2.73/1.05    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  fof(f79,plain,(
% 2.73/1.05    v1_funct_1(sK8)),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  fof(f29,plain,(
% 2.73/1.05    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ! [X3] : (! [X4] : (! [X5] : (r2_relset_1(X1,X3,X4,X5) | ~r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X5,X1,X3) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X4,X1,X3) | ~v1_funct_1(X4)) | k1_xboole_0 = X3))),
% 2.73/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.73/1.05  
% 2.73/1.05  fof(f36,plain,(
% 2.73/1.05    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ? [X3] : (? [X4] : (? [X5] : (~r2_relset_1(X1,X3,X4,X5) & r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X5,X1,X3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X4,X1,X3) & v1_funct_1(X4)) & k1_xboole_0 != X3)) & (! [X3] : (! [X4] : (! [X5] : (r2_relset_1(X1,X3,X4,X5) | ~r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X5,X1,X3) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X4,X1,X3) | ~v1_funct_1(X4)) | k1_xboole_0 = X3) | ~sP0(X1,X2,X0)))),
% 2.73/1.05    inference(nnf_transformation,[],[f29])).
% 2.73/1.05  
% 2.73/1.05  fof(f37,plain,(
% 2.73/1.05    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (? [X4] : (? [X5] : (~r2_relset_1(X0,X3,X4,X5) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X5,X0,X3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & k1_xboole_0 != X3)) & (! [X6] : (! [X7] : (! [X8] : (r2_relset_1(X0,X6,X7,X8) | ~r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X8,X0,X6) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X7,X0,X6) | ~v1_funct_1(X7)) | k1_xboole_0 = X6) | ~sP0(X0,X1,X2)))),
% 2.73/1.05    inference(rectify,[],[f36])).
% 2.73/1.05  
% 2.73/1.05  fof(f40,plain,(
% 2.73/1.05    ( ! [X4,X3] : (! [X2,X1,X0] : (? [X5] : (~r2_relset_1(X0,X3,X4,X5) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X5,X0,X3) & v1_funct_1(X5)) => (~r2_relset_1(X0,X3,X4,sK4(X0,X1,X2)) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,sK4(X0,X1,X2))) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK4(X0,X1,X2),X0,X3) & v1_funct_1(sK4(X0,X1,X2))))) )),
% 2.73/1.05    introduced(choice_axiom,[])).
% 2.73/1.05  
% 2.73/1.05  fof(f39,plain,(
% 2.73/1.05    ( ! [X3] : (! [X2,X1,X0] : (? [X4] : (? [X5] : (~r2_relset_1(X0,X3,X4,X5) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X5,X0,X3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) => (? [X5] : (~r2_relset_1(X0,X3,sK3(X0,X1,X2),X5) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,sK3(X0,X1,X2)),k1_partfun1(X2,X0,X0,X3,X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X5,X0,X3) & v1_funct_1(X5)) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(sK3(X0,X1,X2),X0,X3) & v1_funct_1(sK3(X0,X1,X2))))) )),
% 2.73/1.05    introduced(choice_axiom,[])).
% 2.73/1.05  
% 2.73/1.05  fof(f38,plain,(
% 2.73/1.05    ! [X2,X1,X0] : (? [X3] : (? [X4] : (? [X5] : (~r2_relset_1(X0,X3,X4,X5) & r2_relset_1(X2,X3,k1_partfun1(X2,X0,X0,X3,X1,X4),k1_partfun1(X2,X0,X0,X3,X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X5,X0,X3) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_2(X4,X0,X3) & v1_funct_1(X4)) & k1_xboole_0 != X3) => (? [X4] : (? [X5] : (~r2_relset_1(X0,sK2(X0,X1,X2),X4,X5) & r2_relset_1(X2,sK2(X0,X1,X2),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,X4),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,X5)) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2)))) & v1_funct_2(X5,X0,sK2(X0,X1,X2)) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2)))) & v1_funct_2(X4,X0,sK2(X0,X1,X2)) & v1_funct_1(X4)) & k1_xboole_0 != sK2(X0,X1,X2)))),
% 2.73/1.05    introduced(choice_axiom,[])).
% 2.73/1.05  
% 2.73/1.05  fof(f41,plain,(
% 2.73/1.05    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_relset_1(X0,sK2(X0,X1,X2),sK3(X0,X1,X2),sK4(X0,X1,X2)) & r2_relset_1(X2,sK2(X0,X1,X2),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,sK3(X0,X1,X2)),k1_partfun1(X2,X0,X0,sK2(X0,X1,X2),X1,sK4(X0,X1,X2))) & m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2)))) & v1_funct_2(sK4(X0,X1,X2),X0,sK2(X0,X1,X2)) & v1_funct_1(sK4(X0,X1,X2))) & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,sK2(X0,X1,X2)))) & v1_funct_2(sK3(X0,X1,X2),X0,sK2(X0,X1,X2)) & v1_funct_1(sK3(X0,X1,X2))) & k1_xboole_0 != sK2(X0,X1,X2))) & (! [X6] : (! [X7] : (! [X8] : (r2_relset_1(X0,X6,X7,X8) | ~r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X8,X0,X6) | ~v1_funct_1(X8)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X7,X0,X6) | ~v1_funct_1(X7)) | k1_xboole_0 = X6) | ~sP0(X0,X1,X2)))),
% 2.73/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f40,f39,f38])).
% 2.73/1.05  
% 2.73/1.05  fof(f62,plain,(
% 2.73/1.05    ( ! [X6,X2,X0,X8,X7,X1] : (r2_relset_1(X0,X6,X7,X8) | ~r2_relset_1(X2,X6,k1_partfun1(X2,X0,X0,X6,X1,X7),k1_partfun1(X2,X0,X0,X6,X1,X8)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X8,X0,X6) | ~v1_funct_1(X8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(X0,X6))) | ~v1_funct_2(X7,X0,X6) | ~v1_funct_1(X7) | k1_xboole_0 = X6 | ~sP0(X0,X1,X2)) )),
% 2.73/1.05    inference(cnf_transformation,[],[f41])).
% 2.73/1.05  
% 2.73/1.05  fof(f80,plain,(
% 2.73/1.05    v1_funct_2(sK8,sK6,sK5)),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  fof(f85,plain,(
% 2.73/1.05    k1_xboole_0 != sK5),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  fof(f9,axiom,(
% 2.73/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k1_xboole_0 != X1 => (k2_relset_1(X0,X1,X2) = X1 <=> ! [X3] : (k1_xboole_0 != X3 => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X4,X1,X3) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) & v1_funct_2(X5,X1,X3) & v1_funct_1(X5)) => (r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) => r2_relset_1(X1,X3,X4,X5))))))))),
% 2.73/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.05  
% 2.73/1.05  fof(f23,plain,(
% 2.73/1.05    ! [X0,X1,X2] : (((k2_relset_1(X0,X1,X2) = X1 <=> ! [X3] : (! [X4] : (! [X5] : ((r2_relset_1(X1,X3,X4,X5) | ~r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X5,X1,X3) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X4,X1,X3) | ~v1_funct_1(X4))) | k1_xboole_0 = X3)) | k1_xboole_0 = X1) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.73/1.05    inference(ennf_transformation,[],[f9])).
% 2.73/1.05  
% 2.73/1.05  fof(f24,plain,(
% 2.73/1.05    ! [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) = X1 <=> ! [X3] : (! [X4] : (! [X5] : (r2_relset_1(X1,X3,X4,X5) | ~r2_relset_1(X0,X3,k1_partfun1(X0,X1,X1,X3,X2,X4),k1_partfun1(X0,X1,X1,X3,X2,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X5,X1,X3) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) | ~v1_funct_2(X4,X1,X3) | ~v1_funct_1(X4)) | k1_xboole_0 = X3)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.73/1.05    inference(flattening,[],[f23])).
% 2.73/1.05  
% 2.73/1.05  fof(f30,plain,(
% 2.73/1.05    ! [X0,X2,X1] : ((k2_relset_1(X0,X1,X2) = X1 <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 2.73/1.05    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.73/1.05  
% 2.73/1.05  fof(f31,plain,(
% 2.73/1.05    ! [X0,X1,X2] : (sP1(X0,X2,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.73/1.05    inference(definition_folding,[],[f24,f30,f29])).
% 2.73/1.05  
% 2.73/1.05  fof(f72,plain,(
% 2.73/1.05    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.73/1.05    inference(cnf_transformation,[],[f31])).
% 2.73/1.05  
% 2.73/1.05  fof(f34,plain,(
% 2.73/1.05    ! [X0,X2,X1] : (((k2_relset_1(X0,X1,X2) = X1 | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | k2_relset_1(X0,X1,X2) != X1)) | ~sP1(X0,X2,X1))),
% 2.73/1.05    inference(nnf_transformation,[],[f30])).
% 2.73/1.05  
% 2.73/1.05  fof(f35,plain,(
% 2.73/1.05    ! [X0,X1,X2] : (((k2_relset_1(X0,X2,X1) = X2 | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | k2_relset_1(X0,X2,X1) != X2)) | ~sP1(X0,X1,X2))),
% 2.73/1.05    inference(rectify,[],[f34])).
% 2.73/1.05  
% 2.73/1.05  fof(f60,plain,(
% 2.73/1.05    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | k2_relset_1(X0,X2,X1) != X2 | ~sP1(X0,X1,X2)) )),
% 2.73/1.05    inference(cnf_transformation,[],[f35])).
% 2.73/1.05  
% 2.73/1.05  fof(f83,plain,(
% 2.73/1.05    r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5))),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  fof(f5,axiom,(
% 2.73/1.05    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.73/1.05    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.05  
% 2.73/1.05  fof(f17,plain,(
% 2.73/1.05    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.73/1.05    inference(ennf_transformation,[],[f5])).
% 2.73/1.05  
% 2.73/1.05  fof(f18,plain,(
% 2.73/1.05    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.05    inference(flattening,[],[f17])).
% 2.73/1.05  
% 2.73/1.05  fof(f32,plain,(
% 2.73/1.05    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.05    inference(nnf_transformation,[],[f18])).
% 2.73/1.05  
% 2.73/1.05  fof(f50,plain,(
% 2.73/1.05    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/1.05    inference(cnf_transformation,[],[f32])).
% 2.73/1.05  
% 2.73/1.05  fof(f74,plain,(
% 2.73/1.05    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.73/1.05    inference(cnf_transformation,[],[f26])).
% 2.73/1.05  
% 2.73/1.05  fof(f87,plain,(
% 2.73/1.05    k2_funct_1(sK7) != sK8),
% 2.73/1.05    inference(cnf_transformation,[],[f44])).
% 2.73/1.05  
% 2.73/1.05  cnf(c_39,negated_conjecture,
% 2.73/1.05      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 2.73/1.05      inference(cnf_transformation,[],[f78]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2763,plain,
% 2.73/1.05      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_12,plain,
% 2.73/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.05      | k1_relset_1(X1,X2,X0) = X1
% 2.73/1.05      | k1_xboole_0 = X2 ),
% 2.73/1.05      inference(cnf_transformation,[],[f52]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2782,plain,
% 2.73/1.05      ( k1_relset_1(X0,X1,X2) = X0
% 2.73/1.05      | k1_xboole_0 = X1
% 2.73/1.05      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.73/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_5685,plain,
% 2.73/1.05      ( k1_relset_1(sK5,sK6,sK7) = sK5
% 2.73/1.05      | sK6 = k1_xboole_0
% 2.73/1.05      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_2763,c_2782]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_4,plain,
% 2.73/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.05      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.73/1.05      inference(cnf_transformation,[],[f49]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2790,plain,
% 2.73/1.05      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.73/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3971,plain,
% 2.73/1.05      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_2763,c_2790]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_5697,plain,
% 2.73/1.05      ( k1_relat_1(sK7) = sK5
% 2.73/1.05      | sK6 = k1_xboole_0
% 2.73/1.05      | v1_funct_2(sK7,sK5,sK6) != iProver_top ),
% 2.73/1.05      inference(demodulation,[status(thm)],[c_5685,c_3971]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_40,negated_conjecture,
% 2.73/1.05      ( v1_funct_2(sK7,sK5,sK6) ),
% 2.73/1.05      inference(cnf_transformation,[],[f77]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_43,plain,
% 2.73/1.05      ( v1_funct_2(sK7,sK5,sK6) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_31,negated_conjecture,
% 2.73/1.05      ( k1_xboole_0 != sK6 ),
% 2.73/1.05      inference(cnf_transformation,[],[f86]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2113,plain,( X0 = X0 ),theory(equality) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2146,plain,
% 2.73/1.05      ( k1_xboole_0 = k1_xboole_0 ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_2113]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2114,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3131,plain,
% 2.73/1.05      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_2114]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3132,plain,
% 2.73/1.05      ( sK6 != k1_xboole_0
% 2.73/1.05      | k1_xboole_0 = sK6
% 2.73/1.05      | k1_xboole_0 != k1_xboole_0 ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_3131]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_7430,plain,
% 2.73/1.05      ( k1_relat_1(sK7) = sK5 ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_5697,c_43,c_31,c_2146,c_3132]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_35,negated_conjecture,
% 2.73/1.05      ( k2_relset_1(sK5,sK6,sK7) = sK6 ),
% 2.73/1.05      inference(cnf_transformation,[],[f82]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_27,plain,
% 2.73/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.05      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.73/1.05      | ~ v1_funct_1(X0)
% 2.73/1.05      | ~ v2_funct_1(X0)
% 2.73/1.05      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.73/1.05      inference(cnf_transformation,[],[f75]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_33,negated_conjecture,
% 2.73/1.05      ( v2_funct_1(sK7) ),
% 2.73/1.05      inference(cnf_transformation,[],[f84]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_538,plain,
% 2.73/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.05      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.73/1.05      | ~ v1_funct_1(X0)
% 2.73/1.05      | k2_relset_1(X1,X2,X0) != X2
% 2.73/1.05      | sK7 != X0 ),
% 2.73/1.05      inference(resolution_lifted,[status(thm)],[c_27,c_33]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_539,plain,
% 2.73/1.05      ( ~ v1_funct_2(sK7,X0,X1)
% 2.73/1.05      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | ~ v1_funct_1(sK7)
% 2.73/1.05      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.73/1.05      inference(unflattening,[status(thm)],[c_538]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_41,negated_conjecture,
% 2.73/1.05      ( v1_funct_1(sK7) ),
% 2.73/1.05      inference(cnf_transformation,[],[f76]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_543,plain,
% 2.73/1.05      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.73/1.05      | ~ v1_funct_2(sK7,X0,X1)
% 2.73/1.05      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_539,c_41]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_544,plain,
% 2.73/1.05      ( ~ v1_funct_2(sK7,X0,X1)
% 2.73/1.05      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.73/1.05      inference(renaming,[status(thm)],[c_543]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2758,plain,
% 2.73/1.05      ( k2_relset_1(X0,X1,sK7) != X1
% 2.73/1.05      | v1_funct_2(sK7,X0,X1) != iProver_top
% 2.73/1.05      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.73/1.05      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3548,plain,
% 2.73/1.05      ( v1_funct_2(sK7,sK5,sK6) != iProver_top
% 2.73/1.05      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top
% 2.73/1.05      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_35,c_2758]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_44,plain,
% 2.73/1.05      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3088,plain,
% 2.73/1.05      ( ~ v1_funct_2(sK7,sK5,sK6)
% 2.73/1.05      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.73/1.05      | k2_relset_1(sK5,sK6,sK7) != sK6 ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_544]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3089,plain,
% 2.73/1.05      ( k2_relset_1(sK5,sK6,sK7) != sK6
% 2.73/1.05      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 2.73/1.05      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top
% 2.73/1.05      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_3088]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3693,plain,
% 2.73/1.05      ( m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_3548,c_43,c_44,c_35,c_3089]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_13,plain,
% 2.73/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.73/1.05      | ~ v1_funct_1(X0)
% 2.73/1.05      | ~ v1_funct_1(X3)
% 2.73/1.05      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 2.73/1.05      inference(cnf_transformation,[],[f58]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2781,plain,
% 2.73/1.05      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 2.73/1.05      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.73/1.05      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.73/1.05      | v1_funct_1(X5) != iProver_top
% 2.73/1.05      | v1_funct_1(X4) != iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_5925,plain,
% 2.73/1.05      ( k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7))
% 2.73/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.73/1.05      | v1_funct_1(X2) != iProver_top
% 2.73/1.05      | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_3693,c_2781]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_29,plain,
% 2.73/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.05      | ~ v1_funct_1(X0)
% 2.73/1.05      | v1_funct_1(k2_funct_1(X0))
% 2.73/1.05      | ~ v2_funct_1(X0)
% 2.73/1.05      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.73/1.05      inference(cnf_transformation,[],[f73]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_490,plain,
% 2.73/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.05      | ~ v1_funct_1(X0)
% 2.73/1.05      | v1_funct_1(k2_funct_1(X0))
% 2.73/1.05      | k2_relset_1(X1,X2,X0) != X2
% 2.73/1.05      | sK7 != X0 ),
% 2.73/1.05      inference(resolution_lifted,[status(thm)],[c_29,c_33]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_491,plain,
% 2.73/1.05      ( ~ v1_funct_2(sK7,X0,X1)
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | v1_funct_1(k2_funct_1(sK7))
% 2.73/1.05      | ~ v1_funct_1(sK7)
% 2.73/1.05      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.73/1.05      inference(unflattening,[status(thm)],[c_490]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_495,plain,
% 2.73/1.05      ( v1_funct_1(k2_funct_1(sK7))
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | ~ v1_funct_2(sK7,X0,X1)
% 2.73/1.05      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_491,c_41]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_496,plain,
% 2.73/1.05      ( ~ v1_funct_2(sK7,X0,X1)
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | v1_funct_1(k2_funct_1(sK7))
% 2.73/1.05      | k2_relset_1(X0,X1,sK7) != X1 ),
% 2.73/1.05      inference(renaming,[status(thm)],[c_495]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3082,plain,
% 2.73/1.05      ( ~ v1_funct_2(sK7,sK5,sK6)
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.73/1.05      | v1_funct_1(k2_funct_1(sK7))
% 2.73/1.05      | k2_relset_1(sK5,sK6,sK7) != sK6 ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_496]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3083,plain,
% 2.73/1.05      ( k2_relset_1(sK5,sK6,sK7) != sK6
% 2.73/1.05      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 2.73/1.05      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 2.73/1.05      | v1_funct_1(k2_funct_1(sK7)) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_3082]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_7000,plain,
% 2.73/1.05      ( v1_funct_1(X2) != iProver_top
% 2.73/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.73/1.05      | k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7)) ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_5925,c_43,c_44,c_35,c_3083]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_7001,plain,
% 2.73/1.05      ( k1_partfun1(X0,X1,sK6,sK5,X2,k2_funct_1(sK7)) = k5_relat_1(X2,k2_funct_1(sK7))
% 2.73/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.73/1.05      | v1_funct_1(X2) != iProver_top ),
% 2.73/1.05      inference(renaming,[status(thm)],[c_7000]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_7012,plain,
% 2.73/1.05      ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k5_relat_1(sK7,k2_funct_1(sK7))
% 2.73/1.05      | v1_funct_1(sK7) != iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_2763,c_7001]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_0,plain,
% 2.73/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.73/1.05      | ~ v1_relat_1(X1)
% 2.73/1.05      | v1_relat_1(X0) ),
% 2.73/1.05      inference(cnf_transformation,[],[f45]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2792,plain,
% 2.73/1.05      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.73/1.05      | v1_relat_1(X1) != iProver_top
% 2.73/1.05      | v1_relat_1(X0) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3984,plain,
% 2.73/1.05      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 2.73/1.05      | v1_relat_1(sK7) = iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_2763,c_2792]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3097,plain,
% 2.73/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.05      | v1_relat_1(X0)
% 2.73/1.05      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_0]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3445,plain,
% 2.73/1.05      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.73/1.05      | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
% 2.73/1.05      | v1_relat_1(sK7) ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_3097]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3446,plain,
% 2.73/1.05      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 2.73/1.05      | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 2.73/1.05      | v1_relat_1(sK7) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_3445]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_1,plain,
% 2.73/1.05      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.73/1.05      inference(cnf_transformation,[],[f46]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3946,plain,
% 2.73/1.05      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_1]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3947,plain,
% 2.73/1.05      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_3946]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_4294,plain,
% 2.73/1.05      ( v1_relat_1(sK7) = iProver_top ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_3984,c_44,c_3446,c_3947]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3,plain,
% 2.73/1.05      ( ~ v1_funct_1(X0)
% 2.73/1.05      | ~ v2_funct_1(X0)
% 2.73/1.05      | ~ v1_relat_1(X0)
% 2.73/1.05      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0)) ),
% 2.73/1.05      inference(cnf_transformation,[],[f89]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_562,plain,
% 2.73/1.05      ( ~ v1_funct_1(X0)
% 2.73/1.05      | ~ v1_relat_1(X0)
% 2.73/1.05      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(k1_relat_1(X0))
% 2.73/1.05      | sK7 != X0 ),
% 2.73/1.05      inference(resolution_lifted,[status(thm)],[c_3,c_33]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_563,plain,
% 2.73/1.05      ( ~ v1_funct_1(sK7)
% 2.73/1.05      | ~ v1_relat_1(sK7)
% 2.73/1.05      | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7)) ),
% 2.73/1.05      inference(unflattening,[status(thm)],[c_562]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_565,plain,
% 2.73/1.05      ( ~ v1_relat_1(sK7)
% 2.73/1.05      | k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7)) ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_563,c_41]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2757,plain,
% 2.73/1.05      ( k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7))
% 2.73/1.05      | v1_relat_1(sK7) != iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_4299,plain,
% 2.73/1.05      ( k5_relat_1(sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7)) ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_4294,c_2757]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_7020,plain,
% 2.73/1.05      ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7))
% 2.73/1.05      | v1_funct_1(sK7) != iProver_top ),
% 2.73/1.05      inference(light_normalisation,[status(thm)],[c_7012,c_4299]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_42,plain,
% 2.73/1.05      ( v1_funct_1(sK7) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_7187,plain,
% 2.73/1.05      ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k6_partfun1(k1_relat_1(sK7)) ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_7020,c_42]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_7433,plain,
% 2.73/1.05      ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,k2_funct_1(sK7)) = k6_partfun1(sK5) ),
% 2.73/1.05      inference(demodulation,[status(thm)],[c_7430,c_7187]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_36,negated_conjecture,
% 2.73/1.05      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) ),
% 2.73/1.05      inference(cnf_transformation,[],[f81]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2766,plain,
% 2.73/1.05      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_5923,plain,
% 2.73/1.05      ( k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8)
% 2.73/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.73/1.05      | v1_funct_1(X2) != iProver_top
% 2.73/1.05      | v1_funct_1(sK8) != iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_2766,c_2781]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_38,negated_conjecture,
% 2.73/1.05      ( v1_funct_1(sK8) ),
% 2.73/1.05      inference(cnf_transformation,[],[f79]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_45,plain,
% 2.73/1.05      ( v1_funct_1(sK8) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_6091,plain,
% 2.73/1.05      ( v1_funct_1(X2) != iProver_top
% 2.73/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.73/1.05      | k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8) ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_5923,c_45]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_6092,plain,
% 2.73/1.05      ( k1_partfun1(X0,X1,sK6,sK5,X2,sK8) = k5_relat_1(X2,sK8)
% 2.73/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.73/1.05      | v1_funct_1(X2) != iProver_top ),
% 2.73/1.05      inference(renaming,[status(thm)],[c_6091]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_6103,plain,
% 2.73/1.05      ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8)
% 2.73/1.05      | v1_funct_1(sK7) != iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_2763,c_6092]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3220,plain,
% 2.73/1.05      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.05      | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
% 2.73/1.05      | ~ v1_funct_1(X0)
% 2.73/1.05      | ~ v1_funct_1(sK8)
% 2.73/1.05      | k1_partfun1(X1,X2,X3,X4,X0,sK8) = k5_relat_1(X0,sK8) ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_13]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3562,plain,
% 2.73/1.05      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 2.73/1.05      | ~ v1_funct_1(sK8)
% 2.73/1.05      | ~ v1_funct_1(sK7)
% 2.73/1.05      | k1_partfun1(X2,X3,X0,X1,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_3220]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_4028,plain,
% 2.73/1.05      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | ~ v1_funct_1(sK8)
% 2.73/1.05      | ~ v1_funct_1(sK7)
% 2.73/1.05      | k1_partfun1(X0,X1,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_3562]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_4114,plain,
% 2.73/1.05      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5)))
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.73/1.05      | ~ v1_funct_1(sK8)
% 2.73/1.05      | ~ v1_funct_1(sK7)
% 2.73/1.05      | k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_4028]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_6166,plain,
% 2.73/1.05      ( k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8) = k5_relat_1(sK7,sK8) ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_6103,c_41,c_39,c_38,c_36,c_4114]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_25,plain,
% 2.73/1.05      ( r2_relset_1(X0,X1,X2,X3)
% 2.73/1.05      | ~ r2_relset_1(X4,X1,k1_partfun1(X4,X0,X0,X1,X5,X2),k1_partfun1(X4,X0,X0,X1,X5,X3))
% 2.73/1.05      | ~ sP0(X0,X5,X4)
% 2.73/1.05      | ~ v1_funct_2(X3,X0,X1)
% 2.73/1.05      | ~ v1_funct_2(X2,X0,X1)
% 2.73/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | ~ v1_funct_1(X3)
% 2.73/1.05      | ~ v1_funct_1(X2)
% 2.73/1.05      | k1_xboole_0 = X1 ),
% 2.73/1.05      inference(cnf_transformation,[],[f62]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2769,plain,
% 2.73/1.05      ( k1_xboole_0 = X0
% 2.73/1.05      | r2_relset_1(X1,X0,X2,X3) = iProver_top
% 2.73/1.05      | r2_relset_1(X4,X0,k1_partfun1(X4,X1,X1,X0,X5,X2),k1_partfun1(X4,X1,X1,X0,X5,X3)) != iProver_top
% 2.73/1.05      | sP0(X1,X5,X4) != iProver_top
% 2.73/1.05      | v1_funct_2(X2,X1,X0) != iProver_top
% 2.73/1.05      | v1_funct_2(X3,X1,X0) != iProver_top
% 2.73/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 2.73/1.05      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 2.73/1.05      | v1_funct_1(X2) != iProver_top
% 2.73/1.05      | v1_funct_1(X3) != iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_6171,plain,
% 2.73/1.05      ( sK5 = k1_xboole_0
% 2.73/1.05      | r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
% 2.73/1.05      | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
% 2.73/1.05      | sP0(sK6,sK7,sK5) != iProver_top
% 2.73/1.05      | v1_funct_2(X0,sK6,sK5) != iProver_top
% 2.73/1.05      | v1_funct_2(sK8,sK6,sK5) != iProver_top
% 2.73/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.73/1.05      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.73/1.05      | v1_funct_1(X0) != iProver_top
% 2.73/1.05      | v1_funct_1(sK8) != iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_6166,c_2769]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_37,negated_conjecture,
% 2.73/1.05      ( v1_funct_2(sK8,sK6,sK5) ),
% 2.73/1.05      inference(cnf_transformation,[],[f80]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_46,plain,
% 2.73/1.05      ( v1_funct_2(sK8,sK6,sK5) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_47,plain,
% 2.73/1.05      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_32,negated_conjecture,
% 2.73/1.05      ( k1_xboole_0 != sK5 ),
% 2.73/1.05      inference(cnf_transformation,[],[f85]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3133,plain,
% 2.73/1.05      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_2114]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3134,plain,
% 2.73/1.05      ( sK5 != k1_xboole_0
% 2.73/1.05      | k1_xboole_0 = sK5
% 2.73/1.05      | k1_xboole_0 != k1_xboole_0 ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_3133]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_26,plain,
% 2.73/1.05      ( sP1(X0,X1,X2)
% 2.73/1.05      | ~ v1_funct_2(X1,X0,X2)
% 2.73/1.05      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
% 2.73/1.05      | ~ v1_funct_1(X1)
% 2.73/1.05      | k1_xboole_0 = X2 ),
% 2.73/1.05      inference(cnf_transformation,[],[f72]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2768,plain,
% 2.73/1.05      ( k1_xboole_0 = X0
% 2.73/1.05      | sP1(X1,X2,X0) = iProver_top
% 2.73/1.05      | v1_funct_2(X2,X1,X0) != iProver_top
% 2.73/1.05      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 2.73/1.05      | v1_funct_1(X2) != iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3839,plain,
% 2.73/1.05      ( sK6 = k1_xboole_0
% 2.73/1.05      | sP1(sK5,sK7,sK6) = iProver_top
% 2.73/1.05      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 2.73/1.05      | v1_funct_1(sK7) != iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_2763,c_2768]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_15,plain,
% 2.73/1.05      ( ~ sP1(X0,X1,X2) | sP0(X2,X1,X0) | k2_relset_1(X0,X2,X1) != X2 ),
% 2.73/1.05      inference(cnf_transformation,[],[f60]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2779,plain,
% 2.73/1.05      ( k2_relset_1(X0,X1,X2) != X1
% 2.73/1.05      | sP1(X0,X2,X1) != iProver_top
% 2.73/1.05      | sP0(X1,X2,X0) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_5009,plain,
% 2.73/1.05      ( sP1(sK5,sK7,sK6) != iProver_top
% 2.73/1.05      | sP0(sK6,sK7,sK5) = iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_35,c_2779]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_9285,plain,
% 2.73/1.05      ( v1_funct_1(X0) != iProver_top
% 2.73/1.05      | v1_funct_2(X0,sK6,sK5) != iProver_top
% 2.73/1.05      | r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
% 2.73/1.05      | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
% 2.73/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_6171,c_42,c_43,c_45,c_46,c_47,c_32,c_31,c_2146,c_3132,
% 2.73/1.05                 c_3134,c_3839,c_5009]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_9286,plain,
% 2.73/1.05      ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k1_partfun1(sK5,sK6,sK6,sK5,sK7,X0)) != iProver_top
% 2.73/1.05      | r2_relset_1(sK6,sK5,sK8,X0) = iProver_top
% 2.73/1.05      | v1_funct_2(X0,sK6,sK5) != iProver_top
% 2.73/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.73/1.05      | v1_funct_1(X0) != iProver_top ),
% 2.73/1.05      inference(renaming,[status(thm)],[c_9285]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_9683,plain,
% 2.73/1.05      ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k6_partfun1(sK5)) != iProver_top
% 2.73/1.05      | r2_relset_1(sK6,sK5,sK8,k2_funct_1(sK7)) = iProver_top
% 2.73/1.05      | v1_funct_2(k2_funct_1(sK7),sK6,sK5) != iProver_top
% 2.73/1.05      | m1_subset_1(k2_funct_1(sK7),k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top
% 2.73/1.05      | v1_funct_1(k2_funct_1(sK7)) != iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_7433,c_9286]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_34,negated_conjecture,
% 2.73/1.05      ( r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) ),
% 2.73/1.05      inference(cnf_transformation,[],[f83]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2767,plain,
% 2.73/1.05      ( r2_relset_1(sK5,sK5,k1_partfun1(sK5,sK6,sK6,sK5,sK7,sK8),k6_partfun1(sK5)) = iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_6169,plain,
% 2.73/1.05      ( r2_relset_1(sK5,sK5,k5_relat_1(sK7,sK8),k6_partfun1(sK5)) = iProver_top ),
% 2.73/1.05      inference(demodulation,[status(thm)],[c_6166,c_2767]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_6,plain,
% 2.73/1.05      ( ~ r2_relset_1(X0,X1,X2,X3)
% 2.73/1.05      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.05      | X3 = X2 ),
% 2.73/1.05      inference(cnf_transformation,[],[f50]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_2788,plain,
% 2.73/1.05      ( X0 = X1
% 2.73/1.05      | r2_relset_1(X2,X3,X1,X0) != iProver_top
% 2.73/1.05      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 2.73/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_5410,plain,
% 2.73/1.05      ( sK8 = X0
% 2.73/1.05      | r2_relset_1(sK6,sK5,sK8,X0) != iProver_top
% 2.73/1.05      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK6,sK5))) != iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_2766,c_2788]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_5467,plain,
% 2.73/1.05      ( k2_funct_1(sK7) = sK8
% 2.73/1.05      | r2_relset_1(sK6,sK5,sK8,k2_funct_1(sK7)) != iProver_top ),
% 2.73/1.05      inference(superposition,[status(thm)],[c_3693,c_5410]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_28,plain,
% 2.73/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.05      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.73/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.05      | ~ v1_funct_1(X0)
% 2.73/1.05      | ~ v2_funct_1(X0)
% 2.73/1.05      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.73/1.05      inference(cnf_transformation,[],[f74]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_514,plain,
% 2.73/1.05      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.05      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.73/1.05      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.05      | ~ v1_funct_1(X0)
% 2.73/1.05      | k2_relset_1(X1,X2,X0) != X2
% 2.73/1.05      | sK7 != X0 ),
% 2.73/1.05      inference(resolution_lifted,[status(thm)],[c_28,c_33]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_515,plain,
% 2.73/1.05      ( v1_funct_2(k2_funct_1(sK7),X0,X1)
% 2.73/1.05      | ~ v1_funct_2(sK7,X1,X0)
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.73/1.05      | ~ v1_funct_1(sK7)
% 2.73/1.05      | k2_relset_1(X1,X0,sK7) != X0 ),
% 2.73/1.05      inference(unflattening,[status(thm)],[c_514]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_519,plain,
% 2.73/1.05      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.73/1.05      | ~ v1_funct_2(sK7,X1,X0)
% 2.73/1.05      | v1_funct_2(k2_funct_1(sK7),X0,X1)
% 2.73/1.05      | k2_relset_1(X1,X0,sK7) != X0 ),
% 2.73/1.05      inference(global_propositional_subsumption,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_515,c_41]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_520,plain,
% 2.73/1.05      ( v1_funct_2(k2_funct_1(sK7),X0,X1)
% 2.73/1.05      | ~ v1_funct_2(sK7,X1,X0)
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.73/1.05      | k2_relset_1(X1,X0,sK7) != X0 ),
% 2.73/1.05      inference(renaming,[status(thm)],[c_519]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3085,plain,
% 2.73/1.05      ( v1_funct_2(k2_funct_1(sK7),sK6,sK5)
% 2.73/1.05      | ~ v1_funct_2(sK7,sK5,sK6)
% 2.73/1.05      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.73/1.05      | k2_relset_1(sK5,sK6,sK7) != sK6 ),
% 2.73/1.05      inference(instantiation,[status(thm)],[c_520]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_3086,plain,
% 2.73/1.05      ( k2_relset_1(sK5,sK6,sK7) != sK6
% 2.73/1.05      | v1_funct_2(k2_funct_1(sK7),sK6,sK5) = iProver_top
% 2.73/1.05      | v1_funct_2(sK7,sK5,sK6) != iProver_top
% 2.73/1.05      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top ),
% 2.73/1.05      inference(predicate_to_equality,[status(thm)],[c_3085]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(c_30,negated_conjecture,
% 2.73/1.05      ( k2_funct_1(sK7) != sK8 ),
% 2.73/1.05      inference(cnf_transformation,[],[f87]) ).
% 2.73/1.05  
% 2.73/1.05  cnf(contradiction,plain,
% 2.73/1.05      ( $false ),
% 2.73/1.05      inference(minisat,
% 2.73/1.05                [status(thm)],
% 2.73/1.05                [c_9683,c_6169,c_5467,c_3089,c_3086,c_3083,c_30,c_35,
% 2.73/1.05                 c_44,c_43]) ).
% 2.73/1.05  
% 2.73/1.05  
% 2.73/1.05  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/1.05  
% 2.73/1.05  ------                               Statistics
% 2.73/1.05  
% 2.73/1.05  ------ General
% 2.73/1.05  
% 2.73/1.05  abstr_ref_over_cycles:                  0
% 2.73/1.05  abstr_ref_under_cycles:                 0
% 2.73/1.05  gc_basic_clause_elim:                   0
% 2.73/1.05  forced_gc_time:                         0
% 2.73/1.05  parsing_time:                           0.011
% 2.73/1.05  unif_index_cands_time:                  0.
% 2.73/1.05  unif_index_add_time:                    0.
% 2.73/1.05  orderings_time:                         0.
% 2.73/1.05  out_proof_time:                         0.014
% 2.73/1.05  total_time:                             0.398
% 2.73/1.05  num_of_symbols:                         57
% 2.73/1.05  num_of_terms:                           10027
% 2.73/1.05  
% 2.73/1.05  ------ Preprocessing
% 2.73/1.05  
% 2.73/1.05  num_of_splits:                          0
% 2.73/1.05  num_of_split_atoms:                     0
% 2.73/1.05  num_of_reused_defs:                     0
% 2.73/1.05  num_eq_ax_congr_red:                    53
% 2.73/1.05  num_of_sem_filtered_clauses:            1
% 2.73/1.05  num_of_subtypes:                        0
% 2.73/1.05  monotx_restored_types:                  0
% 2.73/1.05  sat_num_of_epr_types:                   0
% 2.73/1.05  sat_num_of_non_cyclic_types:            0
% 2.73/1.05  sat_guarded_non_collapsed_types:        0
% 2.73/1.05  num_pure_diseq_elim:                    0
% 2.73/1.05  simp_replaced_by:                       0
% 2.73/1.05  res_preprocessed:                       200
% 2.73/1.05  prep_upred:                             0
% 2.73/1.05  prep_unflattend:                        119
% 2.73/1.05  smt_new_axioms:                         0
% 2.73/1.05  pred_elim_cands:                        7
% 2.73/1.05  pred_elim:                              1
% 2.73/1.05  pred_elim_cl:                           1
% 2.73/1.05  pred_elim_cycles:                       5
% 2.73/1.05  merged_defs:                            0
% 2.73/1.05  merged_defs_ncl:                        0
% 2.73/1.05  bin_hyper_res:                          0
% 2.73/1.05  prep_cycles:                            4
% 2.73/1.05  pred_elim_time:                         0.036
% 2.73/1.05  splitting_time:                         0.
% 2.73/1.05  sem_filter_time:                        0.
% 2.73/1.05  monotx_time:                            0.
% 2.73/1.05  subtype_inf_time:                       0.
% 2.73/1.05  
% 2.73/1.05  ------ Problem properties
% 2.73/1.05  
% 2.73/1.05  clauses:                                41
% 2.73/1.05  conjectures:                            11
% 2.73/1.05  epr:                                    6
% 2.73/1.05  horn:                                   28
% 2.73/1.05  ground:                                 13
% 2.73/1.05  unary:                                  12
% 2.73/1.05  binary:                                 13
% 2.73/1.05  lits:                                   104
% 2.73/1.05  lits_eq:                                26
% 2.73/1.05  fd_pure:                                0
% 2.73/1.05  fd_pseudo:                              0
% 2.73/1.05  fd_cond:                                5
% 2.73/1.05  fd_pseudo_cond:                         1
% 2.73/1.05  ac_symbols:                             0
% 2.73/1.05  
% 2.73/1.05  ------ Propositional Solver
% 2.73/1.05  
% 2.73/1.05  prop_solver_calls:                      29
% 2.73/1.05  prop_fast_solver_calls:                 1768
% 2.73/1.05  smt_solver_calls:                       0
% 2.73/1.05  smt_fast_solver_calls:                  0
% 2.73/1.05  prop_num_of_clauses:                    2905
% 2.73/1.05  prop_preprocess_simplified:             8593
% 2.73/1.05  prop_fo_subsumed:                       77
% 2.73/1.05  prop_solver_time:                       0.
% 2.73/1.05  smt_solver_time:                        0.
% 2.73/1.05  smt_fast_solver_time:                   0.
% 2.73/1.05  prop_fast_solver_time:                  0.
% 2.73/1.05  prop_unsat_core_time:                   0.
% 2.73/1.05  
% 2.73/1.05  ------ QBF
% 2.73/1.05  
% 2.73/1.05  qbf_q_res:                              0
% 2.73/1.05  qbf_num_tautologies:                    0
% 2.73/1.05  qbf_prep_cycles:                        0
% 2.73/1.05  
% 2.73/1.05  ------ BMC1
% 2.73/1.05  
% 2.73/1.05  bmc1_current_bound:                     -1
% 2.73/1.05  bmc1_last_solved_bound:                 -1
% 2.73/1.05  bmc1_unsat_core_size:                   -1
% 2.73/1.05  bmc1_unsat_core_parents_size:           -1
% 2.73/1.05  bmc1_merge_next_fun:                    0
% 2.73/1.05  bmc1_unsat_core_clauses_time:           0.
% 2.73/1.05  
% 2.73/1.05  ------ Instantiation
% 2.73/1.05  
% 2.73/1.05  inst_num_of_clauses:                    839
% 2.73/1.05  inst_num_in_passive:                    230
% 2.73/1.05  inst_num_in_active:                     541
% 2.73/1.05  inst_num_in_unprocessed:                68
% 2.73/1.05  inst_num_of_loops:                      550
% 2.73/1.05  inst_num_of_learning_restarts:          0
% 2.73/1.05  inst_num_moves_active_passive:          5
% 2.73/1.05  inst_lit_activity:                      0
% 2.73/1.05  inst_lit_activity_moves:                0
% 2.73/1.05  inst_num_tautologies:                   0
% 2.73/1.05  inst_num_prop_implied:                  0
% 2.73/1.05  inst_num_existing_simplified:           0
% 2.73/1.05  inst_num_eq_res_simplified:             0
% 2.73/1.05  inst_num_child_elim:                    0
% 2.73/1.05  inst_num_of_dismatching_blockings:      100
% 2.73/1.05  inst_num_of_non_proper_insts:           857
% 2.73/1.05  inst_num_of_duplicates:                 0
% 2.73/1.05  inst_inst_num_from_inst_to_res:         0
% 2.73/1.05  inst_dismatching_checking_time:         0.
% 2.73/1.05  
% 2.73/1.05  ------ Resolution
% 2.73/1.05  
% 2.73/1.05  res_num_of_clauses:                     0
% 2.73/1.05  res_num_in_passive:                     0
% 2.73/1.05  res_num_in_active:                      0
% 2.73/1.05  res_num_of_loops:                       204
% 2.73/1.05  res_forward_subset_subsumed:            131
% 2.73/1.05  res_backward_subset_subsumed:           0
% 2.73/1.05  res_forward_subsumed:                   0
% 2.73/1.05  res_backward_subsumed:                  0
% 2.73/1.05  res_forward_subsumption_resolution:     0
% 2.73/1.05  res_backward_subsumption_resolution:    0
% 2.73/1.05  res_clause_to_clause_subsumption:       654
% 2.73/1.05  res_orphan_elimination:                 0
% 2.73/1.05  res_tautology_del:                      37
% 2.73/1.05  res_num_eq_res_simplified:              0
% 2.73/1.05  res_num_sel_changes:                    0
% 2.73/1.05  res_moves_from_active_to_pass:          0
% 2.73/1.05  
% 2.73/1.05  ------ Superposition
% 2.73/1.05  
% 2.73/1.05  sup_time_total:                         0.
% 2.73/1.05  sup_time_generating:                    0.
% 2.73/1.05  sup_time_sim_full:                      0.
% 2.73/1.05  sup_time_sim_immed:                     0.
% 2.73/1.05  
% 2.73/1.05  sup_num_of_clauses:                     152
% 2.73/1.05  sup_num_in_active:                      101
% 2.73/1.05  sup_num_in_passive:                     51
% 2.73/1.05  sup_num_of_loops:                       108
% 2.73/1.05  sup_fw_superposition:                   76
% 2.73/1.05  sup_bw_superposition:                   50
% 2.73/1.05  sup_immediate_simplified:               14
% 2.73/1.05  sup_given_eliminated:                   0
% 2.73/1.05  comparisons_done:                       0
% 2.73/1.05  comparisons_avoided:                    0
% 2.73/1.05  
% 2.73/1.05  ------ Simplifications
% 2.73/1.05  
% 2.73/1.05  
% 2.73/1.05  sim_fw_subset_subsumed:                 9
% 2.73/1.05  sim_bw_subset_subsumed:                 2
% 2.73/1.05  sim_fw_subsumed:                        0
% 2.73/1.05  sim_bw_subsumed:                        0
% 2.73/1.05  sim_fw_subsumption_res:                 4
% 2.73/1.05  sim_bw_subsumption_res:                 0
% 2.73/1.05  sim_tautology_del:                      0
% 2.73/1.05  sim_eq_tautology_del:                   3
% 2.73/1.05  sim_eq_res_simp:                        0
% 2.73/1.05  sim_fw_demodulated:                     3
% 2.73/1.05  sim_bw_demodulated:                     6
% 2.73/1.05  sim_light_normalised:                   2
% 2.73/1.05  sim_joinable_taut:                      0
% 2.73/1.05  sim_joinable_simp:                      0
% 2.73/1.05  sim_ac_normalised:                      0
% 2.73/1.05  sim_smt_subsumption:                    0
% 2.73/1.05  
%------------------------------------------------------------------------------
