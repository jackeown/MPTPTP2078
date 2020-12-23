%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:27 EST 2020

% Result     : Theorem 51.14s
% Output     : CNFRefutation 51.14s
% Verified   : 
% Statistics : Number of formulae       :  298 (8696 expanded)
%              Number of clauses        :  190 (2827 expanded)
%              Number of leaves         :   29 (2113 expanded)
%              Depth                    :   24
%              Number of atoms          : 1064 (65565 expanded)
%              Number of equality atoms :  565 (23640 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,conjecture,(
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

fof(f28,negated_conjecture,(
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
    inference(negated_conjecture,[],[f27])).

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f28])).

fof(f65,plain,(
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
    inference(flattening,[],[f64])).

fof(f69,plain,(
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

fof(f68,plain,
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

fof(f70,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f65,f69,f68])).

fof(f116,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f80,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f124,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f70])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f118,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f70])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f122,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f70])).

fof(f25,axiom,(
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

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f60])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f82,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f92,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f26,axiom,(
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

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f62])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f117,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f70])).

fof(f126,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f70])).

fof(f81,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f87,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k4_relat_1(k4_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f74,plain,(
    ! [X0] :
      ( k4_relat_1(k4_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f90,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f24,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f110,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f129,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f76,f110])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f72,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f121,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f70])).

fof(f20,axiom,(
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

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f67,plain,(
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
    inference(nnf_transformation,[],[f55])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f120,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f70])).

fof(f125,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f70])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f59,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f58])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f52])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f53])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f123,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f70])).

fof(f22,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f108,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f57,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f56])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f84,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f132,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f84,f110])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f136,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f96,f110])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f130,plain,(
    ! [X0] : k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(definition_unfolding,[],[f78,f110,f110])).

fof(f91,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f127,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_55,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1567,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1604,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5688,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1604])).

cnf(c_47,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_63,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1608,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_53,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1569,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_53])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1610,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3517,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1610])).

cnf(c_3789,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1608,c_3517])).

cnf(c_6286,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5688,c_63,c_3789])).

cnf(c_49,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_41,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1576,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(X2)) = iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_4119,plain,
    ( v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_49,c_1576])).

cnf(c_56,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_3143,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3144,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3143])).

cnf(c_4950,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4119,c_56,c_3144,c_3789])).

cnf(c_6289,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6286,c_4950])).

cnf(c_22,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1593,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_8633,plain,
    ( k1_relat_1(k5_relat_1(k4_relat_1(sK2),k2_funct_1(k4_relat_1(sK2)))) = k1_relat_1(k4_relat_1(sK2))
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6289,c_1593])).

cnf(c_42,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1575,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_3405,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_49,c_1575])).

cnf(c_54,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_45,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f126])).

cnf(c_1675,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_42])).

cnf(c_1851,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_1963,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1851])).

cnf(c_3685,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3405,c_55,c_54,c_53,c_49,c_47,c_45,c_1963])).

cnf(c_6290,plain,
    ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(demodulation,[status(thm)],[c_6286,c_3685])).

cnf(c_5689,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4950,c_1604])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_3289,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3290,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3289])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4928,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_4929,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4928])).

cnf(c_8243,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5689,c_56,c_63,c_3290,c_3789,c_4929])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k4_relat_1(k4_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1607,plain,
    ( k4_relat_1(k4_relat_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3892,plain,
    ( k4_relat_1(k4_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_3789,c_1607])).

cnf(c_8245,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_8243,c_3892,c_6286])).

cnf(c_20,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1595,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7624,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1595])).

cnf(c_7626,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7624,c_6286])).

cnf(c_8528,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7626,c_63,c_3789])).

cnf(c_8634,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8633,c_6290,c_8245,c_8528])).

cnf(c_6,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_8635,plain,
    ( k2_relat_1(sK2) = sK1
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8634,c_6])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_4699,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_4711,plain,
    ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4699])).

cnf(c_1599,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_6295,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_6286,c_1599])).

cnf(c_8768,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8635,c_56,c_63,c_3789,c_4711,c_6295])).

cnf(c_50,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1572,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1583,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9237,plain,
    ( k1_relset_1(sK1,sK0,sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1583])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1589,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3120,plain,
    ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1572,c_1589])).

cnf(c_9241,plain,
    ( k1_relat_1(sK3) = sK1
    | sK0 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9237,c_3120])).

cnf(c_51,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_60,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_46,negated_conjecture,
    ( k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_867,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_902,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_867])).

cnf(c_868,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1723,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_868])).

cnf(c_1724,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1723])).

cnf(c_12864,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9241,c_60,c_46,c_902,c_1724])).

cnf(c_17,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1598,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12877,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12864,c_1598])).

cnf(c_52,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_59,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_61,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_1743,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2073,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1743])).

cnf(c_2651,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2073])).

cnf(c_2652,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2651])).

cnf(c_2959,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2960,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2959])).

cnf(c_160971,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12877,c_59,c_61,c_2652,c_2960])).

cnf(c_160972,plain,
    ( k2_relat_1(X0) != sK1
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_160971])).

cnf(c_160978,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_8768,c_160972])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1579,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_8585,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1579])).

cnf(c_8908,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8585,c_59])).

cnf(c_8909,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_8908])).

cnf(c_8916,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_8909])).

cnf(c_28,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_48,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_556,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_48])).

cnf(c_557,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_556])).

cnf(c_37,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_565,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_557,c_37])).

cnf(c_1566,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_35,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2030,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_2136,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1566,c_55,c_53,c_52,c_50,c_565,c_2030])).

cnf(c_8918,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8916,c_2136])).

cnf(c_9352,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8918,c_56])).

cnf(c_160980,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_160978,c_9352])).

cnf(c_12,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_8620,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_8621,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8620])).

cnf(c_161567,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_160980,c_56,c_3789,c_8621])).

cnf(c_1570,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_5687,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_1604])).

cnf(c_6281,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5687,c_61,c_2652,c_2960])).

cnf(c_6282,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_6281])).

cnf(c_161580,plain,
    ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_161567,c_6282])).

cnf(c_25,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1590,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_9913,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != k2_relat_1(sK2)
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9352,c_1590])).

cnf(c_9922,plain,
    ( k2_funct_1(sK3) = sK2
    | k1_relat_1(sK3) != sK1
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9913,c_8768])).

cnf(c_70708,plain,
    ( k2_funct_1(sK3) = sK2
    | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | v2_funct_1(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9922,c_56,c_59,c_60,c_61,c_46,c_902,c_1724,c_2652,c_2960,c_3789,c_9241])).

cnf(c_161690,plain,
    ( k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
    | k4_relat_1(sK3) = sK2
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_161580,c_70708])).

cnf(c_3516,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1572,c_1610])).

cnf(c_3777,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3516,c_61,c_2652,c_2960])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1606,plain,
    ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_4178,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK3))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3777,c_1606])).

cnf(c_5150,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,sK3)) ),
    inference(superposition,[status(thm)],[c_3789,c_4178])).

cnf(c_9354,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) ),
    inference(demodulation,[status(thm)],[c_9352,c_5150])).

cnf(c_7,plain,
    ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_9355,plain,
    ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_9354,c_7])).

cnf(c_9914,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
    | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
    | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k6_partfun1(sK0)
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9355,c_1590])).

cnf(c_8770,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_8768,c_8528])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1596,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7636,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1596])).

cnf(c_7638,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7636,c_6286])).

cnf(c_9437,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7638,c_63,c_3789])).

cnf(c_8632,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1567,c_1593])).

cnf(c_43,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1574,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_2648,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_49,c_1574])).

cnf(c_1676,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_1995,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1676])).

cnf(c_2322,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1995])).

cnf(c_3188,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2648,c_55,c_54,c_53,c_49,c_47,c_45,c_2322])).

cnf(c_6291,plain,
    ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
    inference(demodulation,[status(thm)],[c_6286,c_3188])).

cnf(c_8636,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8632,c_6286,c_6291])).

cnf(c_8637,plain,
    ( k1_relat_1(sK2) = sK0
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8636,c_6])).

cnf(c_8645,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8637,c_63,c_3789])).

cnf(c_9439,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_9437,c_8645])).

cnf(c_9920,plain,
    ( k2_relat_1(k4_relat_1(sK3)) != sK1
    | k6_partfun1(sK0) != k6_partfun1(sK0)
    | k4_relat_1(sK3) = sK2
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9914,c_8245,c_8770,c_9439])).

cnf(c_9921,plain,
    ( k2_relat_1(k4_relat_1(sK3)) != sK1
    | k4_relat_1(sK3) = sK2
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK3)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_9920])).

cnf(c_5046,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5054,plain,
    ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5046])).

cnf(c_68693,plain,
    ( k2_relat_1(k4_relat_1(sK3)) != sK1
    | k4_relat_1(sK3) = sK2
    | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9921,c_56,c_61,c_63,c_2652,c_2960,c_3789,c_4711,c_5054,c_6289,c_6295])).

cnf(c_7635,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_1596])).

cnf(c_8174,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7635,c_61,c_2652,c_2960])).

cnf(c_8175,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_8174])).

cnf(c_12869,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK1
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_12864,c_8175])).

cnf(c_161577,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK1 ),
    inference(superposition,[status(thm)],[c_161567,c_12869])).

cnf(c_161583,plain,
    ( k2_relat_1(k4_relat_1(sK3)) = sK1 ),
    inference(demodulation,[status(thm)],[c_161577,c_161580])).

cnf(c_1603,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_161980,plain,
    ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_161580,c_1603])).

cnf(c_163474,plain,
    ( k4_relat_1(sK3) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_161690,c_59,c_61,c_2652,c_2960,c_68693,c_161583,c_161980])).

cnf(c_5686,plain,
    ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1603,c_1604])).

cnf(c_158,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_23021,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5686,c_158])).

cnf(c_23022,plain,
    ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_23021])).

cnf(c_23027,plain,
    ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1599,c_23022])).

cnf(c_138298,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3))
    | v2_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1570,c_23027])).

cnf(c_138510,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_138298,c_61,c_2652,c_2960])).

cnf(c_138511,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3))
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_138510])).

cnf(c_161573,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_161567,c_138511])).

cnf(c_161589,plain,
    ( k2_funct_1(k4_relat_1(sK3)) = k4_relat_1(k4_relat_1(sK3)) ),
    inference(demodulation,[status(thm)],[c_161573,c_161580])).

cnf(c_3785,plain,
    ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
    inference(superposition,[status(thm)],[c_3777,c_1607])).

cnf(c_161590,plain,
    ( k2_funct_1(k4_relat_1(sK3)) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_161589,c_3785])).

cnf(c_163486,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(demodulation,[status(thm)],[c_163474,c_161590])).

cnf(c_44,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f127])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_163486,c_44])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n001.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 14:33:00 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 51.14/6.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 51.14/6.98  
% 51.14/6.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 51.14/6.98  
% 51.14/6.98  ------  iProver source info
% 51.14/6.98  
% 51.14/6.98  git: date: 2020-06-30 10:37:57 +0100
% 51.14/6.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 51.14/6.98  git: non_committed_changes: false
% 51.14/6.98  git: last_make_outside_of_git: false
% 51.14/6.98  
% 51.14/6.98  ------ 
% 51.14/6.98  
% 51.14/6.98  ------ Input Options
% 51.14/6.98  
% 51.14/6.98  --out_options                           all
% 51.14/6.98  --tptp_safe_out                         true
% 51.14/6.98  --problem_path                          ""
% 51.14/6.98  --include_path                          ""
% 51.14/6.98  --clausifier                            res/vclausify_rel
% 51.14/6.98  --clausifier_options                    ""
% 51.14/6.98  --stdin                                 false
% 51.14/6.98  --stats_out                             all
% 51.14/6.98  
% 51.14/6.98  ------ General Options
% 51.14/6.98  
% 51.14/6.98  --fof                                   false
% 51.14/6.98  --time_out_real                         305.
% 51.14/6.98  --time_out_virtual                      -1.
% 51.14/6.98  --symbol_type_check                     false
% 51.14/6.98  --clausify_out                          false
% 51.14/6.98  --sig_cnt_out                           false
% 51.14/6.98  --trig_cnt_out                          false
% 51.14/6.98  --trig_cnt_out_tolerance                1.
% 51.14/6.98  --trig_cnt_out_sk_spl                   false
% 51.14/6.98  --abstr_cl_out                          false
% 51.14/6.98  
% 51.14/6.98  ------ Global Options
% 51.14/6.98  
% 51.14/6.98  --schedule                              default
% 51.14/6.98  --add_important_lit                     false
% 51.14/6.98  --prop_solver_per_cl                    1000
% 51.14/6.98  --min_unsat_core                        false
% 51.14/6.98  --soft_assumptions                      false
% 51.14/6.98  --soft_lemma_size                       3
% 51.14/6.98  --prop_impl_unit_size                   0
% 51.14/6.98  --prop_impl_unit                        []
% 51.14/6.98  --share_sel_clauses                     true
% 51.14/6.98  --reset_solvers                         false
% 51.14/6.98  --bc_imp_inh                            [conj_cone]
% 51.14/6.98  --conj_cone_tolerance                   3.
% 51.14/6.98  --extra_neg_conj                        none
% 51.14/6.98  --large_theory_mode                     true
% 51.14/6.98  --prolific_symb_bound                   200
% 51.14/6.98  --lt_threshold                          2000
% 51.14/6.98  --clause_weak_htbl                      true
% 51.14/6.98  --gc_record_bc_elim                     false
% 51.14/6.98  
% 51.14/6.98  ------ Preprocessing Options
% 51.14/6.98  
% 51.14/6.98  --preprocessing_flag                    true
% 51.14/6.98  --time_out_prep_mult                    0.1
% 51.14/6.98  --splitting_mode                        input
% 51.14/6.98  --splitting_grd                         true
% 51.14/6.98  --splitting_cvd                         false
% 51.14/6.98  --splitting_cvd_svl                     false
% 51.14/6.98  --splitting_nvd                         32
% 51.14/6.98  --sub_typing                            true
% 51.14/6.98  --prep_gs_sim                           true
% 51.14/6.98  --prep_unflatten                        true
% 51.14/6.98  --prep_res_sim                          true
% 51.14/6.98  --prep_upred                            true
% 51.14/6.98  --prep_sem_filter                       exhaustive
% 51.14/6.98  --prep_sem_filter_out                   false
% 51.14/6.98  --pred_elim                             true
% 51.14/6.98  --res_sim_input                         true
% 51.14/6.98  --eq_ax_congr_red                       true
% 51.14/6.98  --pure_diseq_elim                       true
% 51.14/6.98  --brand_transform                       false
% 51.14/6.98  --non_eq_to_eq                          false
% 51.14/6.98  --prep_def_merge                        true
% 51.14/6.98  --prep_def_merge_prop_impl              false
% 51.14/6.98  --prep_def_merge_mbd                    true
% 51.14/6.98  --prep_def_merge_tr_red                 false
% 51.14/6.98  --prep_def_merge_tr_cl                  false
% 51.14/6.98  --smt_preprocessing                     true
% 51.14/6.98  --smt_ac_axioms                         fast
% 51.14/6.98  --preprocessed_out                      false
% 51.14/6.98  --preprocessed_stats                    false
% 51.14/6.98  
% 51.14/6.98  ------ Abstraction refinement Options
% 51.14/6.98  
% 51.14/6.98  --abstr_ref                             []
% 51.14/6.98  --abstr_ref_prep                        false
% 51.14/6.98  --abstr_ref_until_sat                   false
% 51.14/6.98  --abstr_ref_sig_restrict                funpre
% 51.14/6.98  --abstr_ref_af_restrict_to_split_sk     false
% 51.14/6.98  --abstr_ref_under                       []
% 51.14/6.98  
% 51.14/6.98  ------ SAT Options
% 51.14/6.98  
% 51.14/6.98  --sat_mode                              false
% 51.14/6.98  --sat_fm_restart_options                ""
% 51.14/6.98  --sat_gr_def                            false
% 51.14/6.98  --sat_epr_types                         true
% 51.14/6.98  --sat_non_cyclic_types                  false
% 51.14/6.98  --sat_finite_models                     false
% 51.14/6.98  --sat_fm_lemmas                         false
% 51.14/6.98  --sat_fm_prep                           false
% 51.14/6.98  --sat_fm_uc_incr                        true
% 51.14/6.98  --sat_out_model                         small
% 51.14/6.98  --sat_out_clauses                       false
% 51.14/6.98  
% 51.14/6.98  ------ QBF Options
% 51.14/6.98  
% 51.14/6.98  --qbf_mode                              false
% 51.14/6.98  --qbf_elim_univ                         false
% 51.14/6.98  --qbf_dom_inst                          none
% 51.14/6.98  --qbf_dom_pre_inst                      false
% 51.14/6.98  --qbf_sk_in                             false
% 51.14/6.98  --qbf_pred_elim                         true
% 51.14/6.98  --qbf_split                             512
% 51.14/6.98  
% 51.14/6.98  ------ BMC1 Options
% 51.14/6.98  
% 51.14/6.98  --bmc1_incremental                      false
% 51.14/6.98  --bmc1_axioms                           reachable_all
% 51.14/6.98  --bmc1_min_bound                        0
% 51.14/6.98  --bmc1_max_bound                        -1
% 51.14/6.98  --bmc1_max_bound_default                -1
% 51.14/6.98  --bmc1_symbol_reachability              true
% 51.14/6.98  --bmc1_property_lemmas                  false
% 51.14/6.98  --bmc1_k_induction                      false
% 51.14/6.98  --bmc1_non_equiv_states                 false
% 51.14/6.98  --bmc1_deadlock                         false
% 51.14/6.98  --bmc1_ucm                              false
% 51.14/6.98  --bmc1_add_unsat_core                   none
% 51.14/6.98  --bmc1_unsat_core_children              false
% 51.14/6.98  --bmc1_unsat_core_extrapolate_axioms    false
% 51.14/6.98  --bmc1_out_stat                         full
% 51.14/6.98  --bmc1_ground_init                      false
% 51.14/6.98  --bmc1_pre_inst_next_state              false
% 51.14/6.98  --bmc1_pre_inst_state                   false
% 51.14/6.98  --bmc1_pre_inst_reach_state             false
% 51.14/6.98  --bmc1_out_unsat_core                   false
% 51.14/6.98  --bmc1_aig_witness_out                  false
% 51.14/6.98  --bmc1_verbose                          false
% 51.14/6.98  --bmc1_dump_clauses_tptp                false
% 51.14/6.98  --bmc1_dump_unsat_core_tptp             false
% 51.14/6.98  --bmc1_dump_file                        -
% 51.14/6.98  --bmc1_ucm_expand_uc_limit              128
% 51.14/6.98  --bmc1_ucm_n_expand_iterations          6
% 51.14/6.98  --bmc1_ucm_extend_mode                  1
% 51.14/6.98  --bmc1_ucm_init_mode                    2
% 51.14/6.98  --bmc1_ucm_cone_mode                    none
% 51.14/6.98  --bmc1_ucm_reduced_relation_type        0
% 51.14/6.98  --bmc1_ucm_relax_model                  4
% 51.14/6.98  --bmc1_ucm_full_tr_after_sat            true
% 51.14/6.98  --bmc1_ucm_expand_neg_assumptions       false
% 51.14/6.98  --bmc1_ucm_layered_model                none
% 51.14/6.98  --bmc1_ucm_max_lemma_size               10
% 51.14/6.98  
% 51.14/6.98  ------ AIG Options
% 51.14/6.98  
% 51.14/6.98  --aig_mode                              false
% 51.14/6.98  
% 51.14/6.98  ------ Instantiation Options
% 51.14/6.98  
% 51.14/6.98  --instantiation_flag                    true
% 51.14/6.98  --inst_sos_flag                         true
% 51.14/6.98  --inst_sos_phase                        true
% 51.14/6.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.14/6.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.14/6.98  --inst_lit_sel_side                     num_symb
% 51.14/6.98  --inst_solver_per_active                1400
% 51.14/6.98  --inst_solver_calls_frac                1.
% 51.14/6.98  --inst_passive_queue_type               priority_queues
% 51.14/6.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.14/6.98  --inst_passive_queues_freq              [25;2]
% 51.14/6.98  --inst_dismatching                      true
% 51.14/6.98  --inst_eager_unprocessed_to_passive     true
% 51.14/6.98  --inst_prop_sim_given                   true
% 51.14/6.98  --inst_prop_sim_new                     false
% 51.14/6.98  --inst_subs_new                         false
% 51.14/6.98  --inst_eq_res_simp                      false
% 51.14/6.98  --inst_subs_given                       false
% 51.14/6.98  --inst_orphan_elimination               true
% 51.14/6.98  --inst_learning_loop_flag               true
% 51.14/6.98  --inst_learning_start                   3000
% 51.14/6.98  --inst_learning_factor                  2
% 51.14/6.98  --inst_start_prop_sim_after_learn       3
% 51.14/6.98  --inst_sel_renew                        solver
% 51.14/6.98  --inst_lit_activity_flag                true
% 51.14/6.98  --inst_restr_to_given                   false
% 51.14/6.98  --inst_activity_threshold               500
% 51.14/6.98  --inst_out_proof                        true
% 51.14/6.98  
% 51.14/6.98  ------ Resolution Options
% 51.14/6.98  
% 51.14/6.98  --resolution_flag                       true
% 51.14/6.98  --res_lit_sel                           adaptive
% 51.14/6.98  --res_lit_sel_side                      none
% 51.14/6.98  --res_ordering                          kbo
% 51.14/6.98  --res_to_prop_solver                    active
% 51.14/6.98  --res_prop_simpl_new                    false
% 51.14/6.98  --res_prop_simpl_given                  true
% 51.14/6.98  --res_passive_queue_type                priority_queues
% 51.14/6.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.14/6.98  --res_passive_queues_freq               [15;5]
% 51.14/6.98  --res_forward_subs                      full
% 51.14/6.98  --res_backward_subs                     full
% 51.14/6.98  --res_forward_subs_resolution           true
% 51.14/6.98  --res_backward_subs_resolution          true
% 51.14/6.98  --res_orphan_elimination                true
% 51.14/6.98  --res_time_limit                        2.
% 51.14/6.98  --res_out_proof                         true
% 51.14/6.98  
% 51.14/6.98  ------ Superposition Options
% 51.14/6.98  
% 51.14/6.98  --superposition_flag                    true
% 51.14/6.98  --sup_passive_queue_type                priority_queues
% 51.14/6.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.14/6.98  --sup_passive_queues_freq               [8;1;4]
% 51.14/6.98  --demod_completeness_check              fast
% 51.14/6.98  --demod_use_ground                      true
% 51.14/6.98  --sup_to_prop_solver                    passive
% 51.14/6.98  --sup_prop_simpl_new                    true
% 51.14/6.98  --sup_prop_simpl_given                  true
% 51.14/6.98  --sup_fun_splitting                     true
% 51.14/6.98  --sup_smt_interval                      50000
% 51.14/6.98  
% 51.14/6.98  ------ Superposition Simplification Setup
% 51.14/6.98  
% 51.14/6.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.14/6.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.14/6.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.14/6.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.14/6.98  --sup_full_triv                         [TrivRules;PropSubs]
% 51.14/6.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.14/6.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.14/6.98  --sup_immed_triv                        [TrivRules]
% 51.14/6.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.14/6.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.14/6.98  --sup_immed_bw_main                     []
% 51.14/6.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.14/6.98  --sup_input_triv                        [Unflattening;TrivRules]
% 51.14/6.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.14/6.98  --sup_input_bw                          []
% 51.14/6.98  
% 51.14/6.98  ------ Combination Options
% 51.14/6.98  
% 51.14/6.98  --comb_res_mult                         3
% 51.14/6.98  --comb_sup_mult                         2
% 51.14/6.98  --comb_inst_mult                        10
% 51.14/6.98  
% 51.14/6.98  ------ Debug Options
% 51.14/6.98  
% 51.14/6.98  --dbg_backtrace                         false
% 51.14/6.98  --dbg_dump_prop_clauses                 false
% 51.14/6.98  --dbg_dump_prop_clauses_file            -
% 51.14/6.98  --dbg_out_stat                          false
% 51.14/6.98  ------ Parsing...
% 51.14/6.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 51.14/6.98  
% 51.14/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 51.14/6.98  
% 51.14/6.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 51.14/6.98  
% 51.14/6.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 51.14/6.98  ------ Proving...
% 51.14/6.98  ------ Problem Properties 
% 51.14/6.98  
% 51.14/6.98  
% 51.14/6.98  clauses                                 52
% 51.14/6.98  conjectures                             11
% 51.14/6.98  EPR                                     7
% 51.14/6.98  Horn                                    46
% 51.14/6.98  unary                                   18
% 51.14/6.98  binary                                  5
% 51.14/6.98  lits                                    162
% 51.14/6.98  lits eq                                 43
% 51.14/6.98  fd_pure                                 0
% 51.14/6.98  fd_pseudo                               0
% 51.14/6.98  fd_cond                                 5
% 51.14/6.98  fd_pseudo_cond                          1
% 51.14/6.98  AC symbols                              0
% 51.14/6.98  
% 51.14/6.98  ------ Schedule dynamic 5 is on 
% 51.14/6.98  
% 51.14/6.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 51.14/6.98  
% 51.14/6.98  
% 51.14/6.98  ------ 
% 51.14/6.98  Current options:
% 51.14/6.98  ------ 
% 51.14/6.98  
% 51.14/6.98  ------ Input Options
% 51.14/6.98  
% 51.14/6.98  --out_options                           all
% 51.14/6.98  --tptp_safe_out                         true
% 51.14/6.98  --problem_path                          ""
% 51.14/6.98  --include_path                          ""
% 51.14/6.98  --clausifier                            res/vclausify_rel
% 51.14/6.98  --clausifier_options                    ""
% 51.14/6.98  --stdin                                 false
% 51.14/6.98  --stats_out                             all
% 51.14/6.98  
% 51.14/6.98  ------ General Options
% 51.14/6.98  
% 51.14/6.98  --fof                                   false
% 51.14/6.98  --time_out_real                         305.
% 51.14/6.98  --time_out_virtual                      -1.
% 51.14/6.98  --symbol_type_check                     false
% 51.14/6.98  --clausify_out                          false
% 51.14/6.98  --sig_cnt_out                           false
% 51.14/6.98  --trig_cnt_out                          false
% 51.14/6.98  --trig_cnt_out_tolerance                1.
% 51.14/6.98  --trig_cnt_out_sk_spl                   false
% 51.14/6.98  --abstr_cl_out                          false
% 51.14/6.98  
% 51.14/6.98  ------ Global Options
% 51.14/6.98  
% 51.14/6.98  --schedule                              default
% 51.14/6.98  --add_important_lit                     false
% 51.14/6.98  --prop_solver_per_cl                    1000
% 51.14/6.98  --min_unsat_core                        false
% 51.14/6.98  --soft_assumptions                      false
% 51.14/6.98  --soft_lemma_size                       3
% 51.14/6.98  --prop_impl_unit_size                   0
% 51.14/6.98  --prop_impl_unit                        []
% 51.14/6.98  --share_sel_clauses                     true
% 51.14/6.98  --reset_solvers                         false
% 51.14/6.98  --bc_imp_inh                            [conj_cone]
% 51.14/6.98  --conj_cone_tolerance                   3.
% 51.14/6.98  --extra_neg_conj                        none
% 51.14/6.98  --large_theory_mode                     true
% 51.14/6.98  --prolific_symb_bound                   200
% 51.14/6.98  --lt_threshold                          2000
% 51.14/6.98  --clause_weak_htbl                      true
% 51.14/6.98  --gc_record_bc_elim                     false
% 51.14/6.98  
% 51.14/6.98  ------ Preprocessing Options
% 51.14/6.98  
% 51.14/6.98  --preprocessing_flag                    true
% 51.14/6.98  --time_out_prep_mult                    0.1
% 51.14/6.98  --splitting_mode                        input
% 51.14/6.98  --splitting_grd                         true
% 51.14/6.98  --splitting_cvd                         false
% 51.14/6.98  --splitting_cvd_svl                     false
% 51.14/6.98  --splitting_nvd                         32
% 51.14/6.98  --sub_typing                            true
% 51.14/6.98  --prep_gs_sim                           true
% 51.14/6.98  --prep_unflatten                        true
% 51.14/6.98  --prep_res_sim                          true
% 51.14/6.98  --prep_upred                            true
% 51.14/6.98  --prep_sem_filter                       exhaustive
% 51.14/6.98  --prep_sem_filter_out                   false
% 51.14/6.98  --pred_elim                             true
% 51.14/6.98  --res_sim_input                         true
% 51.14/6.98  --eq_ax_congr_red                       true
% 51.14/6.98  --pure_diseq_elim                       true
% 51.14/6.98  --brand_transform                       false
% 51.14/6.98  --non_eq_to_eq                          false
% 51.14/6.98  --prep_def_merge                        true
% 51.14/6.98  --prep_def_merge_prop_impl              false
% 51.14/6.98  --prep_def_merge_mbd                    true
% 51.14/6.98  --prep_def_merge_tr_red                 false
% 51.14/6.98  --prep_def_merge_tr_cl                  false
% 51.14/6.98  --smt_preprocessing                     true
% 51.14/6.98  --smt_ac_axioms                         fast
% 51.14/6.98  --preprocessed_out                      false
% 51.14/6.98  --preprocessed_stats                    false
% 51.14/6.98  
% 51.14/6.98  ------ Abstraction refinement Options
% 51.14/6.98  
% 51.14/6.98  --abstr_ref                             []
% 51.14/6.98  --abstr_ref_prep                        false
% 51.14/6.98  --abstr_ref_until_sat                   false
% 51.14/6.98  --abstr_ref_sig_restrict                funpre
% 51.14/6.98  --abstr_ref_af_restrict_to_split_sk     false
% 51.14/6.98  --abstr_ref_under                       []
% 51.14/6.98  
% 51.14/6.98  ------ SAT Options
% 51.14/6.98  
% 51.14/6.98  --sat_mode                              false
% 51.14/6.98  --sat_fm_restart_options                ""
% 51.14/6.98  --sat_gr_def                            false
% 51.14/6.98  --sat_epr_types                         true
% 51.14/6.98  --sat_non_cyclic_types                  false
% 51.14/6.98  --sat_finite_models                     false
% 51.14/6.98  --sat_fm_lemmas                         false
% 51.14/6.98  --sat_fm_prep                           false
% 51.14/6.98  --sat_fm_uc_incr                        true
% 51.14/6.98  --sat_out_model                         small
% 51.14/6.98  --sat_out_clauses                       false
% 51.14/6.98  
% 51.14/6.98  ------ QBF Options
% 51.14/6.98  
% 51.14/6.98  --qbf_mode                              false
% 51.14/6.98  --qbf_elim_univ                         false
% 51.14/6.98  --qbf_dom_inst                          none
% 51.14/6.98  --qbf_dom_pre_inst                      false
% 51.14/6.98  --qbf_sk_in                             false
% 51.14/6.98  --qbf_pred_elim                         true
% 51.14/6.98  --qbf_split                             512
% 51.14/6.98  
% 51.14/6.98  ------ BMC1 Options
% 51.14/6.98  
% 51.14/6.98  --bmc1_incremental                      false
% 51.14/6.98  --bmc1_axioms                           reachable_all
% 51.14/6.98  --bmc1_min_bound                        0
% 51.14/6.98  --bmc1_max_bound                        -1
% 51.14/6.98  --bmc1_max_bound_default                -1
% 51.14/6.98  --bmc1_symbol_reachability              true
% 51.14/6.98  --bmc1_property_lemmas                  false
% 51.14/6.98  --bmc1_k_induction                      false
% 51.14/6.98  --bmc1_non_equiv_states                 false
% 51.14/6.98  --bmc1_deadlock                         false
% 51.14/6.98  --bmc1_ucm                              false
% 51.14/6.98  --bmc1_add_unsat_core                   none
% 51.14/6.98  --bmc1_unsat_core_children              false
% 51.14/6.98  --bmc1_unsat_core_extrapolate_axioms    false
% 51.14/6.98  --bmc1_out_stat                         full
% 51.14/6.98  --bmc1_ground_init                      false
% 51.14/6.98  --bmc1_pre_inst_next_state              false
% 51.14/6.98  --bmc1_pre_inst_state                   false
% 51.14/6.98  --bmc1_pre_inst_reach_state             false
% 51.14/6.98  --bmc1_out_unsat_core                   false
% 51.14/6.98  --bmc1_aig_witness_out                  false
% 51.14/6.98  --bmc1_verbose                          false
% 51.14/6.98  --bmc1_dump_clauses_tptp                false
% 51.14/6.98  --bmc1_dump_unsat_core_tptp             false
% 51.14/6.98  --bmc1_dump_file                        -
% 51.14/6.98  --bmc1_ucm_expand_uc_limit              128
% 51.14/6.98  --bmc1_ucm_n_expand_iterations          6
% 51.14/6.98  --bmc1_ucm_extend_mode                  1
% 51.14/6.98  --bmc1_ucm_init_mode                    2
% 51.14/6.98  --bmc1_ucm_cone_mode                    none
% 51.14/6.98  --bmc1_ucm_reduced_relation_type        0
% 51.14/6.98  --bmc1_ucm_relax_model                  4
% 51.14/6.98  --bmc1_ucm_full_tr_after_sat            true
% 51.14/6.98  --bmc1_ucm_expand_neg_assumptions       false
% 51.14/6.98  --bmc1_ucm_layered_model                none
% 51.14/6.98  --bmc1_ucm_max_lemma_size               10
% 51.14/6.98  
% 51.14/6.98  ------ AIG Options
% 51.14/6.98  
% 51.14/6.98  --aig_mode                              false
% 51.14/6.98  
% 51.14/6.98  ------ Instantiation Options
% 51.14/6.98  
% 51.14/6.98  --instantiation_flag                    true
% 51.14/6.98  --inst_sos_flag                         true
% 51.14/6.98  --inst_sos_phase                        true
% 51.14/6.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 51.14/6.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 51.14/6.98  --inst_lit_sel_side                     none
% 51.14/6.98  --inst_solver_per_active                1400
% 51.14/6.98  --inst_solver_calls_frac                1.
% 51.14/6.98  --inst_passive_queue_type               priority_queues
% 51.14/6.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 51.14/6.98  --inst_passive_queues_freq              [25;2]
% 51.14/6.98  --inst_dismatching                      true
% 51.14/6.98  --inst_eager_unprocessed_to_passive     true
% 51.14/6.98  --inst_prop_sim_given                   true
% 51.14/6.98  --inst_prop_sim_new                     false
% 51.14/6.98  --inst_subs_new                         false
% 51.14/6.98  --inst_eq_res_simp                      false
% 51.14/6.98  --inst_subs_given                       false
% 51.14/6.98  --inst_orphan_elimination               true
% 51.14/6.98  --inst_learning_loop_flag               true
% 51.14/6.98  --inst_learning_start                   3000
% 51.14/6.98  --inst_learning_factor                  2
% 51.14/6.98  --inst_start_prop_sim_after_learn       3
% 51.14/6.98  --inst_sel_renew                        solver
% 51.14/6.98  --inst_lit_activity_flag                true
% 51.14/6.98  --inst_restr_to_given                   false
% 51.14/6.98  --inst_activity_threshold               500
% 51.14/6.98  --inst_out_proof                        true
% 51.14/6.98  
% 51.14/6.98  ------ Resolution Options
% 51.14/6.98  
% 51.14/6.98  --resolution_flag                       false
% 51.14/6.98  --res_lit_sel                           adaptive
% 51.14/6.98  --res_lit_sel_side                      none
% 51.14/6.98  --res_ordering                          kbo
% 51.14/6.98  --res_to_prop_solver                    active
% 51.14/6.98  --res_prop_simpl_new                    false
% 51.14/6.98  --res_prop_simpl_given                  true
% 51.14/6.98  --res_passive_queue_type                priority_queues
% 51.14/6.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 51.14/6.98  --res_passive_queues_freq               [15;5]
% 51.14/6.98  --res_forward_subs                      full
% 51.14/6.98  --res_backward_subs                     full
% 51.14/6.98  --res_forward_subs_resolution           true
% 51.14/6.98  --res_backward_subs_resolution          true
% 51.14/6.98  --res_orphan_elimination                true
% 51.14/6.98  --res_time_limit                        2.
% 51.14/6.98  --res_out_proof                         true
% 51.14/6.98  
% 51.14/6.98  ------ Superposition Options
% 51.14/6.98  
% 51.14/6.98  --superposition_flag                    true
% 51.14/6.98  --sup_passive_queue_type                priority_queues
% 51.14/6.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 51.14/6.98  --sup_passive_queues_freq               [8;1;4]
% 51.14/6.98  --demod_completeness_check              fast
% 51.14/6.98  --demod_use_ground                      true
% 51.14/6.98  --sup_to_prop_solver                    passive
% 51.14/6.98  --sup_prop_simpl_new                    true
% 51.14/6.98  --sup_prop_simpl_given                  true
% 51.14/6.98  --sup_fun_splitting                     true
% 51.14/6.98  --sup_smt_interval                      50000
% 51.14/6.98  
% 51.14/6.98  ------ Superposition Simplification Setup
% 51.14/6.98  
% 51.14/6.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 51.14/6.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 51.14/6.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 51.14/6.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 51.14/6.98  --sup_full_triv                         [TrivRules;PropSubs]
% 51.14/6.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 51.14/6.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 51.14/6.98  --sup_immed_triv                        [TrivRules]
% 51.14/6.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 51.14/6.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.14/6.98  --sup_immed_bw_main                     []
% 51.14/6.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 51.14/6.98  --sup_input_triv                        [Unflattening;TrivRules]
% 51.14/6.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 51.14/6.98  --sup_input_bw                          []
% 51.14/6.98  
% 51.14/6.98  ------ Combination Options
% 51.14/6.98  
% 51.14/6.98  --comb_res_mult                         3
% 51.14/6.98  --comb_sup_mult                         2
% 51.14/6.98  --comb_inst_mult                        10
% 51.14/6.98  
% 51.14/6.98  ------ Debug Options
% 51.14/6.98  
% 51.14/6.98  --dbg_backtrace                         false
% 51.14/6.98  --dbg_dump_prop_clauses                 false
% 51.14/6.98  --dbg_dump_prop_clauses_file            -
% 51.14/6.98  --dbg_out_stat                          false
% 51.14/6.98  
% 51.14/6.98  
% 51.14/6.98  
% 51.14/6.98  
% 51.14/6.98  ------ Proving...
% 51.14/6.98  
% 51.14/6.98  
% 51.14/6.98  % SZS status Theorem for theBenchmark.p
% 51.14/6.98  
% 51.14/6.98  % SZS output start CNFRefutation for theBenchmark.p
% 51.14/6.98  
% 51.14/6.98  fof(f27,conjecture,(
% 51.14/6.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f28,negated_conjecture,(
% 51.14/6.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 51.14/6.98    inference(negated_conjecture,[],[f27])).
% 51.14/6.98  
% 51.14/6.98  fof(f64,plain,(
% 51.14/6.98    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 51.14/6.98    inference(ennf_transformation,[],[f28])).
% 51.14/6.98  
% 51.14/6.98  fof(f65,plain,(
% 51.14/6.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 51.14/6.98    inference(flattening,[],[f64])).
% 51.14/6.98  
% 51.14/6.98  fof(f69,plain,(
% 51.14/6.98    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 51.14/6.98    introduced(choice_axiom,[])).
% 51.14/6.98  
% 51.14/6.98  fof(f68,plain,(
% 51.14/6.98    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 51.14/6.98    introduced(choice_axiom,[])).
% 51.14/6.98  
% 51.14/6.98  fof(f70,plain,(
% 51.14/6.98    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 51.14/6.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f65,f69,f68])).
% 51.14/6.98  
% 51.14/6.98  fof(f116,plain,(
% 51.14/6.98    v1_funct_1(sK2)),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  fof(f9,axiom,(
% 51.14/6.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f35,plain,(
% 51.14/6.98    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.14/6.98    inference(ennf_transformation,[],[f9])).
% 51.14/6.98  
% 51.14/6.98  fof(f36,plain,(
% 51.14/6.98    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.14/6.98    inference(flattening,[],[f35])).
% 51.14/6.98  
% 51.14/6.98  fof(f80,plain,(
% 51.14/6.98    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f36])).
% 51.14/6.98  
% 51.14/6.98  fof(f124,plain,(
% 51.14/6.98    v2_funct_1(sK2)),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  fof(f3,axiom,(
% 51.14/6.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f73,plain,(
% 51.14/6.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 51.14/6.98    inference(cnf_transformation,[],[f3])).
% 51.14/6.98  
% 51.14/6.98  fof(f118,plain,(
% 51.14/6.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  fof(f1,axiom,(
% 51.14/6.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f30,plain,(
% 51.14/6.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 51.14/6.98    inference(ennf_transformation,[],[f1])).
% 51.14/6.98  
% 51.14/6.98  fof(f71,plain,(
% 51.14/6.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f30])).
% 51.14/6.98  
% 51.14/6.98  fof(f122,plain,(
% 51.14/6.98    k2_relset_1(sK0,sK1,sK2) = sK1),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  fof(f25,axiom,(
% 51.14/6.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f60,plain,(
% 51.14/6.98    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 51.14/6.98    inference(ennf_transformation,[],[f25])).
% 51.14/6.98  
% 51.14/6.98  fof(f61,plain,(
% 51.14/6.98    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 51.14/6.98    inference(flattening,[],[f60])).
% 51.14/6.98  
% 51.14/6.98  fof(f111,plain,(
% 51.14/6.98    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f61])).
% 51.14/6.98  
% 51.14/6.98  fof(f10,axiom,(
% 51.14/6.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f37,plain,(
% 51.14/6.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.14/6.98    inference(ennf_transformation,[],[f10])).
% 51.14/6.98  
% 51.14/6.98  fof(f38,plain,(
% 51.14/6.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.14/6.98    inference(flattening,[],[f37])).
% 51.14/6.98  
% 51.14/6.98  fof(f82,plain,(
% 51.14/6.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f38])).
% 51.14/6.98  
% 51.14/6.98  fof(f15,axiom,(
% 51.14/6.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f45,plain,(
% 51.14/6.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.14/6.98    inference(ennf_transformation,[],[f15])).
% 51.14/6.98  
% 51.14/6.98  fof(f46,plain,(
% 51.14/6.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.14/6.98    inference(flattening,[],[f45])).
% 51.14/6.98  
% 51.14/6.98  fof(f92,plain,(
% 51.14/6.98    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f46])).
% 51.14/6.98  
% 51.14/6.98  fof(f26,axiom,(
% 51.14/6.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f62,plain,(
% 51.14/6.98    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 51.14/6.98    inference(ennf_transformation,[],[f26])).
% 51.14/6.98  
% 51.14/6.98  fof(f63,plain,(
% 51.14/6.98    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 51.14/6.98    inference(flattening,[],[f62])).
% 51.14/6.98  
% 51.14/6.98  fof(f115,plain,(
% 51.14/6.98    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f63])).
% 51.14/6.98  
% 51.14/6.98  fof(f117,plain,(
% 51.14/6.98    v1_funct_2(sK2,sK0,sK1)),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  fof(f126,plain,(
% 51.14/6.98    k1_xboole_0 != sK1),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  fof(f81,plain,(
% 51.14/6.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f38])).
% 51.14/6.98  
% 51.14/6.98  fof(f12,axiom,(
% 51.14/6.98    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f39,plain,(
% 51.14/6.98    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.14/6.98    inference(ennf_transformation,[],[f12])).
% 51.14/6.98  
% 51.14/6.98  fof(f40,plain,(
% 51.14/6.98    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.14/6.98    inference(flattening,[],[f39])).
% 51.14/6.98  
% 51.14/6.98  fof(f87,plain,(
% 51.14/6.98    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f40])).
% 51.14/6.98  
% 51.14/6.98  fof(f4,axiom,(
% 51.14/6.98    ! [X0] : (v1_relat_1(X0) => k4_relat_1(k4_relat_1(X0)) = X0)),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f32,plain,(
% 51.14/6.98    ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 51.14/6.98    inference(ennf_transformation,[],[f4])).
% 51.14/6.98  
% 51.14/6.98  fof(f74,plain,(
% 51.14/6.98    ( ! [X0] : (k4_relat_1(k4_relat_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f32])).
% 51.14/6.98  
% 51.14/6.98  fof(f14,axiom,(
% 51.14/6.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f43,plain,(
% 51.14/6.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.14/6.98    inference(ennf_transformation,[],[f14])).
% 51.14/6.98  
% 51.14/6.98  fof(f44,plain,(
% 51.14/6.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.14/6.98    inference(flattening,[],[f43])).
% 51.14/6.98  
% 51.14/6.98  fof(f90,plain,(
% 51.14/6.98    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f44])).
% 51.14/6.98  
% 51.14/6.98  fof(f6,axiom,(
% 51.14/6.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f76,plain,(
% 51.14/6.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 51.14/6.98    inference(cnf_transformation,[],[f6])).
% 51.14/6.98  
% 51.14/6.98  fof(f24,axiom,(
% 51.14/6.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f110,plain,(
% 51.14/6.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f24])).
% 51.14/6.98  
% 51.14/6.98  fof(f129,plain,(
% 51.14/6.98    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 51.14/6.98    inference(definition_unfolding,[],[f76,f110])).
% 51.14/6.98  
% 51.14/6.98  fof(f2,axiom,(
% 51.14/6.98    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f31,plain,(
% 51.14/6.98    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 51.14/6.98    inference(ennf_transformation,[],[f2])).
% 51.14/6.98  
% 51.14/6.98  fof(f72,plain,(
% 51.14/6.98    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f31])).
% 51.14/6.98  
% 51.14/6.98  fof(f121,plain,(
% 51.14/6.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  fof(f20,axiom,(
% 51.14/6.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f54,plain,(
% 51.14/6.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.14/6.98    inference(ennf_transformation,[],[f20])).
% 51.14/6.98  
% 51.14/6.98  fof(f55,plain,(
% 51.14/6.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.14/6.98    inference(flattening,[],[f54])).
% 51.14/6.98  
% 51.14/6.98  fof(f67,plain,(
% 51.14/6.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.14/6.98    inference(nnf_transformation,[],[f55])).
% 51.14/6.98  
% 51.14/6.98  fof(f100,plain,(
% 51.14/6.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.14/6.98    inference(cnf_transformation,[],[f67])).
% 51.14/6.98  
% 51.14/6.98  fof(f18,axiom,(
% 51.14/6.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f51,plain,(
% 51.14/6.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.14/6.98    inference(ennf_transformation,[],[f18])).
% 51.14/6.98  
% 51.14/6.98  fof(f97,plain,(
% 51.14/6.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.14/6.98    inference(cnf_transformation,[],[f51])).
% 51.14/6.98  
% 51.14/6.98  fof(f120,plain,(
% 51.14/6.98    v1_funct_2(sK3,sK1,sK0)),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  fof(f125,plain,(
% 51.14/6.98    k1_xboole_0 != sK0),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  fof(f13,axiom,(
% 51.14/6.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f41,plain,(
% 51.14/6.98    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.14/6.98    inference(ennf_transformation,[],[f13])).
% 51.14/6.98  
% 51.14/6.98  fof(f42,plain,(
% 51.14/6.98    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.14/6.98    inference(flattening,[],[f41])).
% 51.14/6.98  
% 51.14/6.98  fof(f89,plain,(
% 51.14/6.98    ( ! [X0,X1] : (v2_funct_1(X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f42])).
% 51.14/6.98  
% 51.14/6.98  fof(f119,plain,(
% 51.14/6.98    v1_funct_1(sK3)),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  fof(f23,axiom,(
% 51.14/6.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f58,plain,(
% 51.14/6.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 51.14/6.98    inference(ennf_transformation,[],[f23])).
% 51.14/6.98  
% 51.14/6.98  fof(f59,plain,(
% 51.14/6.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 51.14/6.98    inference(flattening,[],[f58])).
% 51.14/6.98  
% 51.14/6.98  fof(f109,plain,(
% 51.14/6.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f59])).
% 51.14/6.98  
% 51.14/6.98  fof(f19,axiom,(
% 51.14/6.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f52,plain,(
% 51.14/6.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 51.14/6.98    inference(ennf_transformation,[],[f19])).
% 51.14/6.98  
% 51.14/6.98  fof(f53,plain,(
% 51.14/6.98    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.14/6.98    inference(flattening,[],[f52])).
% 51.14/6.98  
% 51.14/6.98  fof(f66,plain,(
% 51.14/6.98    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 51.14/6.98    inference(nnf_transformation,[],[f53])).
% 51.14/6.98  
% 51.14/6.98  fof(f98,plain,(
% 51.14/6.98    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 51.14/6.98    inference(cnf_transformation,[],[f66])).
% 51.14/6.98  
% 51.14/6.98  fof(f123,plain,(
% 51.14/6.98    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  fof(f22,axiom,(
% 51.14/6.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f29,plain,(
% 51.14/6.98    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 51.14/6.98    inference(pure_predicate_removal,[],[f22])).
% 51.14/6.98  
% 51.14/6.98  fof(f108,plain,(
% 51.14/6.98    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 51.14/6.98    inference(cnf_transformation,[],[f29])).
% 51.14/6.98  
% 51.14/6.98  fof(f21,axiom,(
% 51.14/6.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f56,plain,(
% 51.14/6.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 51.14/6.98    inference(ennf_transformation,[],[f21])).
% 51.14/6.98  
% 51.14/6.98  fof(f57,plain,(
% 51.14/6.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 51.14/6.98    inference(flattening,[],[f56])).
% 51.14/6.98  
% 51.14/6.98  fof(f107,plain,(
% 51.14/6.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f57])).
% 51.14/6.98  
% 51.14/6.98  fof(f11,axiom,(
% 51.14/6.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f84,plain,(
% 51.14/6.98    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 51.14/6.98    inference(cnf_transformation,[],[f11])).
% 51.14/6.98  
% 51.14/6.98  fof(f132,plain,(
% 51.14/6.98    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 51.14/6.98    inference(definition_unfolding,[],[f84,f110])).
% 51.14/6.98  
% 51.14/6.98  fof(f17,axiom,(
% 51.14/6.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f49,plain,(
% 51.14/6.98    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 51.14/6.98    inference(ennf_transformation,[],[f17])).
% 51.14/6.98  
% 51.14/6.98  fof(f50,plain,(
% 51.14/6.98    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 51.14/6.98    inference(flattening,[],[f49])).
% 51.14/6.98  
% 51.14/6.98  fof(f96,plain,(
% 51.14/6.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f50])).
% 51.14/6.98  
% 51.14/6.98  fof(f136,plain,(
% 51.14/6.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(definition_unfolding,[],[f96,f110])).
% 51.14/6.98  
% 51.14/6.98  fof(f5,axiom,(
% 51.14/6.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f33,plain,(
% 51.14/6.98    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 51.14/6.98    inference(ennf_transformation,[],[f5])).
% 51.14/6.98  
% 51.14/6.98  fof(f75,plain,(
% 51.14/6.98    ( ! [X0,X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f33])).
% 51.14/6.98  
% 51.14/6.98  fof(f7,axiom,(
% 51.14/6.98    ! [X0] : k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)),
% 51.14/6.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 51.14/6.98  
% 51.14/6.98  fof(f78,plain,(
% 51.14/6.98    ( ! [X0] : (k4_relat_1(k6_relat_1(X0)) = k6_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f7])).
% 51.14/6.98  
% 51.14/6.98  fof(f130,plain,(
% 51.14/6.98    ( ! [X0] : (k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0)) )),
% 51.14/6.98    inference(definition_unfolding,[],[f78,f110,f110])).
% 51.14/6.98  
% 51.14/6.98  fof(f91,plain,(
% 51.14/6.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f44])).
% 51.14/6.98  
% 51.14/6.98  fof(f114,plain,(
% 51.14/6.98    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 51.14/6.98    inference(cnf_transformation,[],[f63])).
% 51.14/6.98  
% 51.14/6.98  fof(f127,plain,(
% 51.14/6.98    k2_funct_1(sK2) != sK3),
% 51.14/6.98    inference(cnf_transformation,[],[f70])).
% 51.14/6.98  
% 51.14/6.98  cnf(c_55,negated_conjecture,
% 51.14/6.98      ( v1_funct_1(sK2) ),
% 51.14/6.98      inference(cnf_transformation,[],[f116]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1567,plain,
% 51.14/6.98      ( v1_funct_1(sK2) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9,plain,
% 51.14/6.98      ( ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v2_funct_1(X0)
% 51.14/6.98      | ~ v1_relat_1(X0)
% 51.14/6.98      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 51.14/6.98      inference(cnf_transformation,[],[f80]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1604,plain,
% 51.14/6.98      ( k2_funct_1(X0) = k4_relat_1(X0)
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(X0) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_5688,plain,
% 51.14/6.98      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1567,c_1604]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_47,negated_conjecture,
% 51.14/6.98      ( v2_funct_1(sK2) ),
% 51.14/6.98      inference(cnf_transformation,[],[f124]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_63,plain,
% 51.14/6.98      ( v2_funct_1(sK2) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_2,plain,
% 51.14/6.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 51.14/6.98      inference(cnf_transformation,[],[f73]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1608,plain,
% 51.14/6.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_53,negated_conjecture,
% 51.14/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 51.14/6.98      inference(cnf_transformation,[],[f118]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1569,plain,
% 51.14/6.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_53]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_0,plain,
% 51.14/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 51.14/6.98      | ~ v1_relat_1(X1)
% 51.14/6.98      | v1_relat_1(X0) ),
% 51.14/6.98      inference(cnf_transformation,[],[f71]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1610,plain,
% 51.14/6.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 51.14/6.98      | v1_relat_1(X1) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3517,plain,
% 51.14/6.98      ( v1_relat_1(k2_zfmisc_1(sK0,sK1)) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) = iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1569,c_1610]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3789,plain,
% 51.14/6.98      ( v1_relat_1(sK2) = iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1608,c_3517]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_6286,plain,
% 51.14/6.98      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_5688,c_63,c_3789]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_49,negated_conjecture,
% 51.14/6.98      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 51.14/6.98      inference(cnf_transformation,[],[f122]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_41,plain,
% 51.14/6.98      ( ~ v1_funct_2(X0,X1,X2)
% 51.14/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.14/6.98      | ~ v1_funct_1(X0)
% 51.14/6.98      | v1_funct_1(k2_funct_1(X0))
% 51.14/6.98      | ~ v2_funct_1(X0)
% 51.14/6.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 51.14/6.98      inference(cnf_transformation,[],[f111]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1576,plain,
% 51.14/6.98      ( k2_relset_1(X0,X1,X2) != X1
% 51.14/6.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 51.14/6.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.14/6.98      | v1_funct_1(X2) != iProver_top
% 51.14/6.98      | v1_funct_1(k2_funct_1(X2)) = iProver_top
% 51.14/6.98      | v2_funct_1(X2) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_4119,plain,
% 51.14/6.98      ( v1_funct_2(sK2,sK0,sK1) != iProver_top
% 51.14/6.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 51.14/6.98      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 51.14/6.98      | v1_funct_1(sK2) != iProver_top
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_49,c_1576]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_56,plain,
% 51.14/6.98      ( v1_funct_1(sK2) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_10,plain,
% 51.14/6.98      ( ~ v1_funct_1(X0)
% 51.14/6.98      | v1_funct_1(k2_funct_1(X0))
% 51.14/6.98      | ~ v1_relat_1(X0) ),
% 51.14/6.98      inference(cnf_transformation,[],[f82]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3143,plain,
% 51.14/6.98      ( v1_funct_1(k2_funct_1(sK2))
% 51.14/6.98      | ~ v1_funct_1(sK2)
% 51.14/6.98      | ~ v1_relat_1(sK2) ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_10]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3144,plain,
% 51.14/6.98      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 51.14/6.98      | v1_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_3143]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_4950,plain,
% 51.14/6.98      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_4119,c_56,c_3144,c_3789]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_6289,plain,
% 51.14/6.98      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_6286,c_4950]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_22,plain,
% 51.14/6.98      ( ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v2_funct_1(X0)
% 51.14/6.98      | ~ v1_relat_1(X0)
% 51.14/6.98      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 51.14/6.98      inference(cnf_transformation,[],[f92]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1593,plain,
% 51.14/6.98      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(X0) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8633,plain,
% 51.14/6.98      ( k1_relat_1(k5_relat_1(k4_relat_1(sK2),k2_funct_1(k4_relat_1(sK2)))) = k1_relat_1(k4_relat_1(sK2))
% 51.14/6.98      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 51.14/6.98      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_6289,c_1593]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_42,plain,
% 51.14/6.98      ( ~ v1_funct_2(X0,X1,X2)
% 51.14/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.14/6.98      | ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v2_funct_1(X0)
% 51.14/6.98      | k2_relset_1(X1,X2,X0) != X2
% 51.14/6.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 51.14/6.98      | k1_xboole_0 = X2 ),
% 51.14/6.98      inference(cnf_transformation,[],[f115]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1575,plain,
% 51.14/6.98      ( k2_relset_1(X0,X1,X2) != X1
% 51.14/6.98      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 51.14/6.98      | k1_xboole_0 = X1
% 51.14/6.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 51.14/6.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.14/6.98      | v1_funct_1(X2) != iProver_top
% 51.14/6.98      | v2_funct_1(X2) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3405,plain,
% 51.14/6.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 51.14/6.98      | sK1 = k1_xboole_0
% 51.14/6.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 51.14/6.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 51.14/6.98      | v1_funct_1(sK2) != iProver_top
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_49,c_1575]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_54,negated_conjecture,
% 51.14/6.98      ( v1_funct_2(sK2,sK0,sK1) ),
% 51.14/6.98      inference(cnf_transformation,[],[f117]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_45,negated_conjecture,
% 51.14/6.98      ( k1_xboole_0 != sK1 ),
% 51.14/6.98      inference(cnf_transformation,[],[f126]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1675,plain,
% 51.14/6.98      ( ~ v1_funct_2(X0,X1,sK1)
% 51.14/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 51.14/6.98      | ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v2_funct_1(X0)
% 51.14/6.98      | k2_relset_1(X1,sK1,X0) != sK1
% 51.14/6.98      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 51.14/6.98      | k1_xboole_0 = sK1 ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_42]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1851,plain,
% 51.14/6.98      ( ~ v1_funct_2(sK2,X0,sK1)
% 51.14/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 51.14/6.98      | ~ v1_funct_1(sK2)
% 51.14/6.98      | ~ v2_funct_1(sK2)
% 51.14/6.98      | k2_relset_1(X0,sK1,sK2) != sK1
% 51.14/6.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 51.14/6.98      | k1_xboole_0 = sK1 ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_1675]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1963,plain,
% 51.14/6.98      ( ~ v1_funct_2(sK2,sK0,sK1)
% 51.14/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 51.14/6.98      | ~ v1_funct_1(sK2)
% 51.14/6.98      | ~ v2_funct_1(sK2)
% 51.14/6.98      | k2_relset_1(sK0,sK1,sK2) != sK1
% 51.14/6.98      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 51.14/6.98      | k1_xboole_0 = sK1 ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_1851]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3685,plain,
% 51.14/6.98      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_3405,c_55,c_54,c_53,c_49,c_47,c_45,c_1963]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_6290,plain,
% 51.14/6.98      ( k5_relat_1(k4_relat_1(sK2),sK2) = k6_partfun1(sK1) ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_6286,c_3685]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_5689,plain,
% 51.14/6.98      ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2))
% 51.14/6.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 51.14/6.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_4950,c_1604]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_11,plain,
% 51.14/6.98      ( ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v1_relat_1(X0)
% 51.14/6.98      | v1_relat_1(k2_funct_1(X0)) ),
% 51.14/6.98      inference(cnf_transformation,[],[f81]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3289,plain,
% 51.14/6.98      ( ~ v1_funct_1(sK2)
% 51.14/6.98      | v1_relat_1(k2_funct_1(sK2))
% 51.14/6.98      | ~ v1_relat_1(sK2) ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_11]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3290,plain,
% 51.14/6.98      ( v1_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_3289]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_14,plain,
% 51.14/6.98      ( ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v2_funct_1(X0)
% 51.14/6.98      | v2_funct_1(k2_funct_1(X0))
% 51.14/6.98      | ~ v1_relat_1(X0) ),
% 51.14/6.98      inference(cnf_transformation,[],[f87]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_4928,plain,
% 51.14/6.98      ( ~ v1_funct_1(sK2)
% 51.14/6.98      | v2_funct_1(k2_funct_1(sK2))
% 51.14/6.98      | ~ v2_funct_1(sK2)
% 51.14/6.98      | ~ v1_relat_1(sK2) ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_14]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_4929,plain,
% 51.14/6.98      ( v1_funct_1(sK2) != iProver_top
% 51.14/6.98      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_4928]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8243,plain,
% 51.14/6.98      ( k2_funct_1(k2_funct_1(sK2)) = k4_relat_1(k2_funct_1(sK2)) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_5689,c_56,c_63,c_3290,c_3789,c_4929]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3,plain,
% 51.14/6.98      ( ~ v1_relat_1(X0) | k4_relat_1(k4_relat_1(X0)) = X0 ),
% 51.14/6.98      inference(cnf_transformation,[],[f74]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1607,plain,
% 51.14/6.98      ( k4_relat_1(k4_relat_1(X0)) = X0 | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3892,plain,
% 51.14/6.98      ( k4_relat_1(k4_relat_1(sK2)) = sK2 ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_3789,c_1607]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8245,plain,
% 51.14/6.98      ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
% 51.14/6.98      inference(light_normalisation,[status(thm)],[c_8243,c_3892,c_6286]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_20,plain,
% 51.14/6.98      ( ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v2_funct_1(X0)
% 51.14/6.98      | ~ v1_relat_1(X0)
% 51.14/6.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 51.14/6.98      inference(cnf_transformation,[],[f90]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1595,plain,
% 51.14/6.98      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(X0) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_7624,plain,
% 51.14/6.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1567,c_1595]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_7626,plain,
% 51.14/6.98      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2)
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(light_normalisation,[status(thm)],[c_7624,c_6286]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8528,plain,
% 51.14/6.98      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_7626,c_63,c_3789]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8634,plain,
% 51.14/6.98      ( k1_relat_1(k6_partfun1(sK1)) = k2_relat_1(sK2)
% 51.14/6.98      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 51.14/6.98      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 51.14/6.98      inference(light_normalisation,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_8633,c_6290,c_8245,c_8528]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_6,plain,
% 51.14/6.98      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 51.14/6.98      inference(cnf_transformation,[],[f129]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8635,plain,
% 51.14/6.98      ( k2_relat_1(sK2) = sK1
% 51.14/6.98      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 51.14/6.98      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_8634,c_6]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1,plain,
% 51.14/6.98      ( ~ v1_relat_1(X0) | v1_relat_1(k4_relat_1(X0)) ),
% 51.14/6.98      inference(cnf_transformation,[],[f72]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_4699,plain,
% 51.14/6.98      ( v1_relat_1(k4_relat_1(sK2)) | ~ v1_relat_1(sK2) ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_1]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_4711,plain,
% 51.14/6.98      ( v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_4699]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1599,plain,
% 51.14/6.98      ( v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(k2_funct_1(X0)) = iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_6295,plain,
% 51.14/6.98      ( v1_funct_1(sK2) != iProver_top
% 51.14/6.98      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_6286,c_1599]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8768,plain,
% 51.14/6.98      ( k2_relat_1(sK2) = sK1 ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_8635,c_56,c_63,c_3789,c_4711,c_6295]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_50,negated_conjecture,
% 51.14/6.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 51.14/6.98      inference(cnf_transformation,[],[f121]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1572,plain,
% 51.14/6.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_34,plain,
% 51.14/6.98      ( ~ v1_funct_2(X0,X1,X2)
% 51.14/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.14/6.98      | k1_relset_1(X1,X2,X0) = X1
% 51.14/6.98      | k1_xboole_0 = X2 ),
% 51.14/6.98      inference(cnf_transformation,[],[f100]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1583,plain,
% 51.14/6.98      ( k1_relset_1(X0,X1,X2) = X0
% 51.14/6.98      | k1_xboole_0 = X1
% 51.14/6.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 51.14/6.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9237,plain,
% 51.14/6.98      ( k1_relset_1(sK1,sK0,sK3) = sK1
% 51.14/6.98      | sK0 = k1_xboole_0
% 51.14/6.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1572,c_1583]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_26,plain,
% 51.14/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.14/6.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 51.14/6.98      inference(cnf_transformation,[],[f97]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1589,plain,
% 51.14/6.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 51.14/6.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3120,plain,
% 51.14/6.98      ( k1_relset_1(sK1,sK0,sK3) = k1_relat_1(sK3) ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1572,c_1589]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9241,plain,
% 51.14/6.98      ( k1_relat_1(sK3) = sK1
% 51.14/6.98      | sK0 = k1_xboole_0
% 51.14/6.98      | v1_funct_2(sK3,sK1,sK0) != iProver_top ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_9237,c_3120]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_51,negated_conjecture,
% 51.14/6.98      ( v1_funct_2(sK3,sK1,sK0) ),
% 51.14/6.98      inference(cnf_transformation,[],[f120]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_60,plain,
% 51.14/6.98      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_46,negated_conjecture,
% 51.14/6.98      ( k1_xboole_0 != sK0 ),
% 51.14/6.98      inference(cnf_transformation,[],[f125]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_867,plain,( X0 = X0 ),theory(equality) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_902,plain,
% 51.14/6.98      ( k1_xboole_0 = k1_xboole_0 ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_867]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_868,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1723,plain,
% 51.14/6.98      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_868]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1724,plain,
% 51.14/6.98      ( sK0 != k1_xboole_0
% 51.14/6.98      | k1_xboole_0 = sK0
% 51.14/6.98      | k1_xboole_0 != k1_xboole_0 ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_1723]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_12864,plain,
% 51.14/6.98      ( k1_relat_1(sK3) = sK1 ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_9241,c_60,c_46,c_902,c_1724]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_17,plain,
% 51.14/6.98      ( ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v1_funct_1(X1)
% 51.14/6.98      | v2_funct_1(X0)
% 51.14/6.98      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 51.14/6.98      | ~ v1_relat_1(X0)
% 51.14/6.98      | ~ v1_relat_1(X1)
% 51.14/6.98      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 51.14/6.98      inference(cnf_transformation,[],[f89]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1598,plain,
% 51.14/6.98      ( k1_relat_1(X0) != k2_relat_1(X1)
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v1_funct_1(X1) != iProver_top
% 51.14/6.98      | v2_funct_1(X0) = iProver_top
% 51.14/6.98      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top
% 51.14/6.98      | v1_relat_1(X1) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_12877,plain,
% 51.14/6.98      ( k2_relat_1(X0) != sK1
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v1_funct_1(sK3) != iProver_top
% 51.14/6.98      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 51.14/6.98      | v2_funct_1(sK3) = iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top
% 51.14/6.98      | v1_relat_1(sK3) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_12864,c_1598]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_52,negated_conjecture,
% 51.14/6.98      ( v1_funct_1(sK3) ),
% 51.14/6.98      inference(cnf_transformation,[],[f119]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_59,plain,
% 51.14/6.98      ( v1_funct_1(sK3) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_61,plain,
% 51.14/6.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1743,plain,
% 51.14/6.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
% 51.14/6.98      | ~ v1_relat_1(X0)
% 51.14/6.98      | v1_relat_1(sK3) ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_0]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_2073,plain,
% 51.14/6.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.14/6.98      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 51.14/6.98      | v1_relat_1(sK3) ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_1743]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_2651,plain,
% 51.14/6.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 51.14/6.98      | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
% 51.14/6.98      | v1_relat_1(sK3) ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_2073]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_2652,plain,
% 51.14/6.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 51.14/6.98      | v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 51.14/6.98      | v1_relat_1(sK3) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_2651]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_2959,plain,
% 51.14/6.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_2]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_2960,plain,
% 51.14/6.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_2959]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_160971,plain,
% 51.14/6.98      ( v1_relat_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(sK3) = iProver_top
% 51.14/6.98      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 51.14/6.98      | k2_relat_1(X0) != sK1
% 51.14/6.98      | v1_funct_1(X0) != iProver_top ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_12877,c_59,c_61,c_2652,c_2960]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_160972,plain,
% 51.14/6.98      ( k2_relat_1(X0) != sK1
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(k5_relat_1(X0,sK3)) != iProver_top
% 51.14/6.98      | v2_funct_1(sK3) = iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(renaming,[status(thm)],[c_160971]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_160978,plain,
% 51.14/6.98      ( v1_funct_1(sK2) != iProver_top
% 51.14/6.98      | v2_funct_1(k5_relat_1(sK2,sK3)) != iProver_top
% 51.14/6.98      | v2_funct_1(sK3) = iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_8768,c_160972]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_38,plain,
% 51.14/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.14/6.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 51.14/6.98      | ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v1_funct_1(X3)
% 51.14/6.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 51.14/6.98      inference(cnf_transformation,[],[f109]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1579,plain,
% 51.14/6.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 51.14/6.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 51.14/6.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.14/6.98      | v1_funct_1(X5) != iProver_top
% 51.14/6.98      | v1_funct_1(X4) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8585,plain,
% 51.14/6.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 51.14/6.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.14/6.98      | v1_funct_1(X2) != iProver_top
% 51.14/6.98      | v1_funct_1(sK3) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1572,c_1579]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8908,plain,
% 51.14/6.98      ( v1_funct_1(X2) != iProver_top
% 51.14/6.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.14/6.98      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_8585,c_59]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8909,plain,
% 51.14/6.98      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 51.14/6.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.14/6.98      | v1_funct_1(X2) != iProver_top ),
% 51.14/6.98      inference(renaming,[status(thm)],[c_8908]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8916,plain,
% 51.14/6.98      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 51.14/6.98      | v1_funct_1(sK2) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1569,c_8909]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_28,plain,
% 51.14/6.98      ( ~ r2_relset_1(X0,X1,X2,X3)
% 51.14/6.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.14/6.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 51.14/6.98      | X3 = X2 ),
% 51.14/6.98      inference(cnf_transformation,[],[f98]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_48,negated_conjecture,
% 51.14/6.98      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 51.14/6.98      inference(cnf_transformation,[],[f123]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_556,plain,
% 51.14/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.14/6.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.14/6.98      | X3 = X0
% 51.14/6.98      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 51.14/6.98      | k6_partfun1(sK0) != X3
% 51.14/6.98      | sK0 != X2
% 51.14/6.98      | sK0 != X1 ),
% 51.14/6.98      inference(resolution_lifted,[status(thm)],[c_28,c_48]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_557,plain,
% 51.14/6.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.14/6.98      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.14/6.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 51.14/6.98      inference(unflattening,[status(thm)],[c_556]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_37,plain,
% 51.14/6.98      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 51.14/6.98      inference(cnf_transformation,[],[f108]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_565,plain,
% 51.14/6.98      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.14/6.98      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 51.14/6.98      inference(forward_subsumption_resolution,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_557,c_37]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1566,plain,
% 51.14/6.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 51.14/6.98      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_35,plain,
% 51.14/6.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.14/6.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 51.14/6.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 51.14/6.98      | ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v1_funct_1(X3) ),
% 51.14/6.98      inference(cnf_transformation,[],[f107]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_2030,plain,
% 51.14/6.98      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 51.14/6.98      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 51.14/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 51.14/6.98      | ~ v1_funct_1(sK3)
% 51.14/6.98      | ~ v1_funct_1(sK2) ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_35]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_2136,plain,
% 51.14/6.98      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_1566,c_55,c_53,c_52,c_50,c_565,c_2030]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8918,plain,
% 51.14/6.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 51.14/6.98      | v1_funct_1(sK2) != iProver_top ),
% 51.14/6.98      inference(light_normalisation,[status(thm)],[c_8916,c_2136]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9352,plain,
% 51.14/6.98      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_8918,c_56]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_160980,plain,
% 51.14/6.98      ( v1_funct_1(sK2) != iProver_top
% 51.14/6.98      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 51.14/6.98      | v2_funct_1(sK3) = iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(light_normalisation,[status(thm)],[c_160978,c_9352]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_12,plain,
% 51.14/6.98      ( v2_funct_1(k6_partfun1(X0)) ),
% 51.14/6.98      inference(cnf_transformation,[],[f132]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8620,plain,
% 51.14/6.98      ( v2_funct_1(k6_partfun1(sK0)) ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_12]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8621,plain,
% 51.14/6.98      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_8620]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_161567,plain,
% 51.14/6.98      ( v2_funct_1(sK3) = iProver_top ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_160980,c_56,c_3789,c_8621]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1570,plain,
% 51.14/6.98      ( v1_funct_1(sK3) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_5687,plain,
% 51.14/6.98      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 51.14/6.98      | v2_funct_1(sK3) != iProver_top
% 51.14/6.98      | v1_relat_1(sK3) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1570,c_1604]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_6281,plain,
% 51.14/6.98      ( v2_funct_1(sK3) != iProver_top
% 51.14/6.98      | k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_5687,c_61,c_2652,c_2960]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_6282,plain,
% 51.14/6.98      ( k2_funct_1(sK3) = k4_relat_1(sK3)
% 51.14/6.98      | v2_funct_1(sK3) != iProver_top ),
% 51.14/6.98      inference(renaming,[status(thm)],[c_6281]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_161580,plain,
% 51.14/6.98      ( k2_funct_1(sK3) = k4_relat_1(sK3) ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_161567,c_6282]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_25,plain,
% 51.14/6.98      ( ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v1_funct_1(X1)
% 51.14/6.98      | ~ v2_funct_1(X0)
% 51.14/6.98      | ~ v1_relat_1(X0)
% 51.14/6.98      | ~ v1_relat_1(X1)
% 51.14/6.98      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 51.14/6.98      | k2_funct_1(X0) = X1
% 51.14/6.98      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 51.14/6.98      inference(cnf_transformation,[],[f136]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1590,plain,
% 51.14/6.98      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 51.14/6.98      | k2_funct_1(X1) = X0
% 51.14/6.98      | k1_relat_1(X1) != k2_relat_1(X0)
% 51.14/6.98      | v1_funct_1(X1) != iProver_top
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(X1) != iProver_top
% 51.14/6.98      | v1_relat_1(X1) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9913,plain,
% 51.14/6.98      ( k2_funct_1(sK3) = sK2
% 51.14/6.98      | k1_relat_1(sK3) != k2_relat_1(sK2)
% 51.14/6.98      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 51.14/6.98      | v1_funct_1(sK3) != iProver_top
% 51.14/6.98      | v1_funct_1(sK2) != iProver_top
% 51.14/6.98      | v2_funct_1(sK3) != iProver_top
% 51.14/6.98      | v1_relat_1(sK3) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_9352,c_1590]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9922,plain,
% 51.14/6.98      ( k2_funct_1(sK3) = sK2
% 51.14/6.98      | k1_relat_1(sK3) != sK1
% 51.14/6.98      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 51.14/6.98      | v1_funct_1(sK3) != iProver_top
% 51.14/6.98      | v1_funct_1(sK2) != iProver_top
% 51.14/6.98      | v2_funct_1(sK3) != iProver_top
% 51.14/6.98      | v1_relat_1(sK3) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(light_normalisation,[status(thm)],[c_9913,c_8768]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_70708,plain,
% 51.14/6.98      ( k2_funct_1(sK3) = sK2
% 51.14/6.98      | k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 51.14/6.98      | v2_funct_1(sK3) != iProver_top ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_9922,c_56,c_59,c_60,c_61,c_46,c_902,c_1724,c_2652,
% 51.14/6.98                 c_2960,c_3789,c_9241]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_161690,plain,
% 51.14/6.98      ( k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(sK0)
% 51.14/6.98      | k4_relat_1(sK3) = sK2
% 51.14/6.98      | v2_funct_1(sK3) != iProver_top ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_161580,c_70708]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3516,plain,
% 51.14/6.98      ( v1_relat_1(k2_zfmisc_1(sK1,sK0)) != iProver_top
% 51.14/6.98      | v1_relat_1(sK3) = iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1572,c_1610]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3777,plain,
% 51.14/6.98      ( v1_relat_1(sK3) = iProver_top ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_3516,c_61,c_2652,c_2960]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_4,plain,
% 51.14/6.98      ( ~ v1_relat_1(X0)
% 51.14/6.98      | ~ v1_relat_1(X1)
% 51.14/6.98      | k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,X1)) ),
% 51.14/6.98      inference(cnf_transformation,[],[f75]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1606,plain,
% 51.14/6.98      ( k5_relat_1(k4_relat_1(X0),k4_relat_1(X1)) = k4_relat_1(k5_relat_1(X1,X0))
% 51.14/6.98      | v1_relat_1(X1) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_4178,plain,
% 51.14/6.98      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(X0)) = k4_relat_1(k5_relat_1(X0,sK3))
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_3777,c_1606]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_5150,plain,
% 51.14/6.98      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k5_relat_1(sK2,sK3)) ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_3789,c_4178]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9354,plain,
% 51.14/6.98      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k4_relat_1(k6_partfun1(sK0)) ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_9352,c_5150]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_7,plain,
% 51.14/6.98      ( k4_relat_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 51.14/6.98      inference(cnf_transformation,[],[f130]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9355,plain,
% 51.14/6.98      ( k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) = k6_partfun1(sK0) ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_9354,c_7]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9914,plain,
% 51.14/6.98      ( k2_funct_1(k4_relat_1(sK2)) = k4_relat_1(sK3)
% 51.14/6.98      | k1_relat_1(k4_relat_1(sK2)) != k2_relat_1(k4_relat_1(sK3))
% 51.14/6.98      | k6_partfun1(k2_relat_1(k4_relat_1(sK2))) != k6_partfun1(sK0)
% 51.14/6.98      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 51.14/6.98      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 51.14/6.98      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 51.14/6.98      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 51.14/6.98      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_9355,c_1590]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8770,plain,
% 51.14/6.98      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_8768,c_8528]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_19,plain,
% 51.14/6.98      ( ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v2_funct_1(X0)
% 51.14/6.98      | ~ v1_relat_1(X0)
% 51.14/6.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 51.14/6.98      inference(cnf_transformation,[],[f91]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1596,plain,
% 51.14/6.98      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(X0) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_7636,plain,
% 51.14/6.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1567,c_1596]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_7638,plain,
% 51.14/6.98      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2)
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(light_normalisation,[status(thm)],[c_7636,c_6286]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9437,plain,
% 51.14/6.98      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_7638,c_63,c_3789]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8632,plain,
% 51.14/6.98      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1567,c_1593]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_43,plain,
% 51.14/6.98      ( ~ v1_funct_2(X0,X1,X2)
% 51.14/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 51.14/6.98      | ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v2_funct_1(X0)
% 51.14/6.98      | k2_relset_1(X1,X2,X0) != X2
% 51.14/6.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 51.14/6.98      | k1_xboole_0 = X2 ),
% 51.14/6.98      inference(cnf_transformation,[],[f114]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1574,plain,
% 51.14/6.98      ( k2_relset_1(X0,X1,X2) != X1
% 51.14/6.98      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 51.14/6.98      | k1_xboole_0 = X1
% 51.14/6.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 51.14/6.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 51.14/6.98      | v1_funct_1(X2) != iProver_top
% 51.14/6.98      | v2_funct_1(X2) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_2648,plain,
% 51.14/6.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 51.14/6.98      | sK1 = k1_xboole_0
% 51.14/6.98      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 51.14/6.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 51.14/6.98      | v1_funct_1(sK2) != iProver_top
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_49,c_1574]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1676,plain,
% 51.14/6.98      ( ~ v1_funct_2(X0,X1,sK1)
% 51.14/6.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 51.14/6.98      | ~ v1_funct_1(X0)
% 51.14/6.98      | ~ v2_funct_1(X0)
% 51.14/6.98      | k2_relset_1(X1,sK1,X0) != sK1
% 51.14/6.98      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 51.14/6.98      | k1_xboole_0 = sK1 ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_43]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1995,plain,
% 51.14/6.98      ( ~ v1_funct_2(sK2,X0,sK1)
% 51.14/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 51.14/6.98      | ~ v1_funct_1(sK2)
% 51.14/6.98      | ~ v2_funct_1(sK2)
% 51.14/6.98      | k2_relset_1(X0,sK1,sK2) != sK1
% 51.14/6.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 51.14/6.98      | k1_xboole_0 = sK1 ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_1676]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_2322,plain,
% 51.14/6.98      ( ~ v1_funct_2(sK2,sK0,sK1)
% 51.14/6.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 51.14/6.98      | ~ v1_funct_1(sK2)
% 51.14/6.98      | ~ v2_funct_1(sK2)
% 51.14/6.98      | k2_relset_1(sK0,sK1,sK2) != sK1
% 51.14/6.98      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 51.14/6.98      | k1_xboole_0 = sK1 ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_1995]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3188,plain,
% 51.14/6.98      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_2648,c_55,c_54,c_53,c_49,c_47,c_45,c_2322]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_6291,plain,
% 51.14/6.98      ( k5_relat_1(sK2,k4_relat_1(sK2)) = k6_partfun1(sK0) ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_6286,c_3188]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8636,plain,
% 51.14/6.98      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(light_normalisation,[status(thm)],[c_8632,c_6286,c_6291]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8637,plain,
% 51.14/6.98      ( k1_relat_1(sK2) = sK0
% 51.14/6.98      | v2_funct_1(sK2) != iProver_top
% 51.14/6.98      | v1_relat_1(sK2) != iProver_top ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_8636,c_6]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8645,plain,
% 51.14/6.98      ( k1_relat_1(sK2) = sK0 ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_8637,c_63,c_3789]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9439,plain,
% 51.14/6.98      ( k2_relat_1(k4_relat_1(sK2)) = sK0 ),
% 51.14/6.98      inference(light_normalisation,[status(thm)],[c_9437,c_8645]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9920,plain,
% 51.14/6.98      ( k2_relat_1(k4_relat_1(sK3)) != sK1
% 51.14/6.98      | k6_partfun1(sK0) != k6_partfun1(sK0)
% 51.14/6.98      | k4_relat_1(sK3) = sK2
% 51.14/6.98      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 51.14/6.98      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 51.14/6.98      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 51.14/6.98      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 51.14/6.98      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 51.14/6.98      inference(light_normalisation,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_9914,c_8245,c_8770,c_9439]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_9921,plain,
% 51.14/6.98      ( k2_relat_1(k4_relat_1(sK3)) != sK1
% 51.14/6.98      | k4_relat_1(sK3) = sK2
% 51.14/6.98      | v1_funct_1(k4_relat_1(sK3)) != iProver_top
% 51.14/6.98      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 51.14/6.98      | v2_funct_1(k4_relat_1(sK2)) != iProver_top
% 51.14/6.98      | v1_relat_1(k4_relat_1(sK3)) != iProver_top
% 51.14/6.98      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 51.14/6.98      inference(equality_resolution_simp,[status(thm)],[c_9920]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_5046,plain,
% 51.14/6.98      ( v1_relat_1(k4_relat_1(sK3)) | ~ v1_relat_1(sK3) ),
% 51.14/6.98      inference(instantiation,[status(thm)],[c_1]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_5054,plain,
% 51.14/6.98      ( v1_relat_1(k4_relat_1(sK3)) = iProver_top
% 51.14/6.98      | v1_relat_1(sK3) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_5046]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_68693,plain,
% 51.14/6.98      ( k2_relat_1(k4_relat_1(sK3)) != sK1
% 51.14/6.98      | k4_relat_1(sK3) = sK2
% 51.14/6.98      | v1_funct_1(k4_relat_1(sK3)) != iProver_top ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_9921,c_56,c_61,c_63,c_2652,c_2960,c_3789,c_4711,
% 51.14/6.98                 c_5054,c_6289,c_6295]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_7635,plain,
% 51.14/6.98      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 51.14/6.98      | v2_funct_1(sK3) != iProver_top
% 51.14/6.98      | v1_relat_1(sK3) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1570,c_1596]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8174,plain,
% 51.14/6.98      ( v2_funct_1(sK3) != iProver_top
% 51.14/6.98      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_7635,c_61,c_2652,c_2960]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_8175,plain,
% 51.14/6.98      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 51.14/6.98      | v2_funct_1(sK3) != iProver_top ),
% 51.14/6.98      inference(renaming,[status(thm)],[c_8174]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_12869,plain,
% 51.14/6.98      ( k2_relat_1(k2_funct_1(sK3)) = sK1
% 51.14/6.98      | v2_funct_1(sK3) != iProver_top ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_12864,c_8175]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_161577,plain,
% 51.14/6.98      ( k2_relat_1(k2_funct_1(sK3)) = sK1 ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_161567,c_12869]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_161583,plain,
% 51.14/6.98      ( k2_relat_1(k4_relat_1(sK3)) = sK1 ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_161577,c_161580]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_1603,plain,
% 51.14/6.98      ( v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_161980,plain,
% 51.14/6.98      ( v1_funct_1(k4_relat_1(sK3)) = iProver_top
% 51.14/6.98      | v1_funct_1(sK3) != iProver_top
% 51.14/6.98      | v1_relat_1(sK3) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_161580,c_1603]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_163474,plain,
% 51.14/6.98      ( k4_relat_1(sK3) = sK2 ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_161690,c_59,c_61,c_2652,c_2960,c_68693,c_161583,
% 51.14/6.98                 c_161980]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_5686,plain,
% 51.14/6.98      ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(k2_funct_1(X0)) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top
% 51.14/6.98      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1603,c_1604]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_158,plain,
% 51.14/6.98      ( v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top
% 51.14/6.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 51.14/6.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_23021,plain,
% 51.14/6.98      ( v1_relat_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(k2_funct_1(X0)) != iProver_top
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0)) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_5686,c_158]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_23022,plain,
% 51.14/6.98      ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(k2_funct_1(X0)) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(renaming,[status(thm)],[c_23021]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_23027,plain,
% 51.14/6.98      ( k2_funct_1(k2_funct_1(X0)) = k4_relat_1(k2_funct_1(X0))
% 51.14/6.98      | v1_funct_1(X0) != iProver_top
% 51.14/6.98      | v2_funct_1(X0) != iProver_top
% 51.14/6.98      | v1_relat_1(X0) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1599,c_23022]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_138298,plain,
% 51.14/6.98      ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3))
% 51.14/6.98      | v2_funct_1(sK3) != iProver_top
% 51.14/6.98      | v1_relat_1(sK3) != iProver_top ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_1570,c_23027]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_138510,plain,
% 51.14/6.98      ( v2_funct_1(sK3) != iProver_top
% 51.14/6.98      | k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3)) ),
% 51.14/6.98      inference(global_propositional_subsumption,
% 51.14/6.98                [status(thm)],
% 51.14/6.98                [c_138298,c_61,c_2652,c_2960]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_138511,plain,
% 51.14/6.98      ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3))
% 51.14/6.98      | v2_funct_1(sK3) != iProver_top ),
% 51.14/6.98      inference(renaming,[status(thm)],[c_138510]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_161573,plain,
% 51.14/6.98      ( k2_funct_1(k2_funct_1(sK3)) = k4_relat_1(k2_funct_1(sK3)) ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_161567,c_138511]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_161589,plain,
% 51.14/6.98      ( k2_funct_1(k4_relat_1(sK3)) = k4_relat_1(k4_relat_1(sK3)) ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_161573,c_161580]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_3785,plain,
% 51.14/6.98      ( k4_relat_1(k4_relat_1(sK3)) = sK3 ),
% 51.14/6.98      inference(superposition,[status(thm)],[c_3777,c_1607]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_161590,plain,
% 51.14/6.98      ( k2_funct_1(k4_relat_1(sK3)) = sK3 ),
% 51.14/6.98      inference(light_normalisation,[status(thm)],[c_161589,c_3785]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_163486,plain,
% 51.14/6.98      ( k2_funct_1(sK2) = sK3 ),
% 51.14/6.98      inference(demodulation,[status(thm)],[c_163474,c_161590]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(c_44,negated_conjecture,
% 51.14/6.98      ( k2_funct_1(sK2) != sK3 ),
% 51.14/6.98      inference(cnf_transformation,[],[f127]) ).
% 51.14/6.98  
% 51.14/6.98  cnf(contradiction,plain,
% 51.14/6.98      ( $false ),
% 51.14/6.98      inference(minisat,[status(thm)],[c_163486,c_44]) ).
% 51.14/6.98  
% 51.14/6.98  
% 51.14/6.98  % SZS output end CNFRefutation for theBenchmark.p
% 51.14/6.98  
% 51.14/6.98  ------                               Statistics
% 51.14/6.98  
% 51.14/6.98  ------ General
% 51.14/6.98  
% 51.14/6.98  abstr_ref_over_cycles:                  0
% 51.14/6.98  abstr_ref_under_cycles:                 0
% 51.14/6.98  gc_basic_clause_elim:                   0
% 51.14/6.98  forced_gc_time:                         0
% 51.14/6.98  parsing_time:                           0.012
% 51.14/6.98  unif_index_cands_time:                  0.
% 51.14/6.98  unif_index_add_time:                    0.
% 51.14/6.98  orderings_time:                         0.
% 51.14/6.98  out_proof_time:                         0.071
% 51.14/6.98  total_time:                             6.21
% 51.14/6.98  num_of_symbols:                         53
% 51.14/6.98  num_of_terms:                           175027
% 51.14/6.98  
% 51.14/6.98  ------ Preprocessing
% 51.14/6.98  
% 51.14/6.98  num_of_splits:                          0
% 51.14/6.98  num_of_split_atoms:                     0
% 51.14/6.98  num_of_reused_defs:                     0
% 51.14/6.98  num_eq_ax_congr_red:                    6
% 51.14/6.98  num_of_sem_filtered_clauses:            1
% 51.14/6.98  num_of_subtypes:                        0
% 51.14/6.98  monotx_restored_types:                  0
% 51.14/6.98  sat_num_of_epr_types:                   0
% 51.14/6.98  sat_num_of_non_cyclic_types:            0
% 51.14/6.98  sat_guarded_non_collapsed_types:        0
% 51.14/6.98  num_pure_diseq_elim:                    0
% 51.14/6.98  simp_replaced_by:                       0
% 51.14/6.98  res_preprocessed:                       247
% 51.14/6.98  prep_upred:                             0
% 51.14/6.98  prep_unflattend:                        8
% 51.14/6.98  smt_new_axioms:                         0
% 51.14/6.98  pred_elim_cands:                        5
% 51.14/6.98  pred_elim:                              1
% 51.14/6.98  pred_elim_cl:                           2
% 51.14/6.98  pred_elim_cycles:                       3
% 51.14/6.98  merged_defs:                            0
% 51.14/6.98  merged_defs_ncl:                        0
% 51.14/6.98  bin_hyper_res:                          0
% 51.14/6.98  prep_cycles:                            4
% 51.14/6.98  pred_elim_time:                         0.003
% 51.14/6.98  splitting_time:                         0.
% 51.14/6.98  sem_filter_time:                        0.
% 51.14/6.98  monotx_time:                            0.001
% 51.14/6.98  subtype_inf_time:                       0.
% 51.14/6.98  
% 51.14/6.98  ------ Problem properties
% 51.14/6.98  
% 51.14/6.98  clauses:                                52
% 51.14/6.98  conjectures:                            11
% 51.14/6.98  epr:                                    7
% 51.14/6.98  horn:                                   46
% 51.14/6.98  ground:                                 12
% 51.14/6.98  unary:                                  18
% 51.14/6.98  binary:                                 5
% 51.14/6.98  lits:                                   162
% 51.14/6.98  lits_eq:                                43
% 51.14/6.98  fd_pure:                                0
% 51.14/6.98  fd_pseudo:                              0
% 51.14/6.98  fd_cond:                                5
% 51.14/6.98  fd_pseudo_cond:                         1
% 51.14/6.98  ac_symbols:                             0
% 51.14/6.98  
% 51.14/6.98  ------ Propositional Solver
% 51.14/6.98  
% 51.14/6.98  prop_solver_calls:                      68
% 51.14/6.98  prop_fast_solver_calls:                 7721
% 51.14/6.98  smt_solver_calls:                       0
% 51.14/6.98  smt_fast_solver_calls:                  0
% 51.14/6.98  prop_num_of_clauses:                    67516
% 51.14/6.98  prop_preprocess_simplified:             148419
% 51.14/6.98  prop_fo_subsumed:                       1800
% 51.14/6.98  prop_solver_time:                       0.
% 51.14/6.98  smt_solver_time:                        0.
% 51.14/6.98  smt_fast_solver_time:                   0.
% 51.14/6.98  prop_fast_solver_time:                  0.
% 51.14/6.98  prop_unsat_core_time:                   0.012
% 51.14/6.98  
% 51.14/6.98  ------ QBF
% 51.14/6.98  
% 51.14/6.98  qbf_q_res:                              0
% 51.14/6.98  qbf_num_tautologies:                    0
% 51.14/6.98  qbf_prep_cycles:                        0
% 51.14/6.98  
% 51.14/6.98  ------ BMC1
% 51.14/6.98  
% 51.14/6.98  bmc1_current_bound:                     -1
% 51.14/6.98  bmc1_last_solved_bound:                 -1
% 51.14/6.98  bmc1_unsat_core_size:                   -1
% 51.14/6.98  bmc1_unsat_core_parents_size:           -1
% 51.14/6.98  bmc1_merge_next_fun:                    0
% 51.14/6.98  bmc1_unsat_core_clauses_time:           0.
% 51.14/6.98  
% 51.14/6.98  ------ Instantiation
% 51.14/6.98  
% 51.14/6.98  inst_num_of_clauses:                    13156
% 51.14/6.98  inst_num_in_passive:                    7765
% 51.14/6.98  inst_num_in_active:                     7028
% 51.14/6.98  inst_num_in_unprocessed:                1090
% 51.14/6.98  inst_num_of_loops:                      7499
% 51.14/6.98  inst_num_of_learning_restarts:          1
% 51.14/6.98  inst_num_moves_active_passive:          471
% 51.14/6.98  inst_lit_activity:                      0
% 51.14/6.98  inst_lit_activity_moves:                7
% 51.14/6.98  inst_num_tautologies:                   0
% 51.14/6.98  inst_num_prop_implied:                  0
% 51.14/6.98  inst_num_existing_simplified:           0
% 51.14/6.98  inst_num_eq_res_simplified:             0
% 51.14/6.98  inst_num_child_elim:                    0
% 51.14/6.98  inst_num_of_dismatching_blockings:      6897
% 51.14/6.98  inst_num_of_non_proper_insts:           17258
% 51.14/6.98  inst_num_of_duplicates:                 0
% 51.14/6.98  inst_inst_num_from_inst_to_res:         0
% 51.14/6.98  inst_dismatching_checking_time:         0.
% 51.14/6.98  
% 51.14/6.98  ------ Resolution
% 51.14/6.98  
% 51.14/6.98  res_num_of_clauses:                     70
% 51.14/6.98  res_num_in_passive:                     70
% 51.14/6.98  res_num_in_active:                      0
% 51.14/6.98  res_num_of_loops:                       251
% 51.14/6.98  res_forward_subset_subsumed:            639
% 51.14/6.98  res_backward_subset_subsumed:           2
% 51.14/6.98  res_forward_subsumed:                   0
% 51.14/6.98  res_backward_subsumed:                  0
% 51.14/6.98  res_forward_subsumption_resolution:     1
% 51.14/6.98  res_backward_subsumption_resolution:    0
% 51.14/6.98  res_clause_to_clause_subsumption:       20585
% 51.14/6.98  res_orphan_elimination:                 0
% 51.14/6.98  res_tautology_del:                      346
% 51.14/6.98  res_num_eq_res_simplified:              0
% 51.14/6.98  res_num_sel_changes:                    0
% 51.14/6.98  res_moves_from_active_to_pass:          0
% 51.14/6.98  
% 51.14/6.98  ------ Superposition
% 51.14/6.98  
% 51.14/6.98  sup_time_total:                         0.
% 51.14/6.98  sup_time_generating:                    0.
% 51.14/6.98  sup_time_sim_full:                      0.
% 51.14/6.98  sup_time_sim_immed:                     0.
% 51.14/6.98  
% 51.14/6.98  sup_num_of_clauses:                     6878
% 51.14/6.98  sup_num_in_active:                      1012
% 51.14/6.98  sup_num_in_passive:                     5866
% 51.14/6.98  sup_num_of_loops:                       1499
% 51.14/6.98  sup_fw_superposition:                   4989
% 51.14/6.98  sup_bw_superposition:                   5032
% 51.14/6.98  sup_immediate_simplified:               6011
% 51.14/6.98  sup_given_eliminated:                   0
% 51.14/6.98  comparisons_done:                       0
% 51.14/6.98  comparisons_avoided:                    1
% 51.14/6.98  
% 51.14/6.98  ------ Simplifications
% 51.14/6.98  
% 51.14/6.98  
% 51.14/6.98  sim_fw_subset_subsumed:                 103
% 51.14/6.98  sim_bw_subset_subsumed:                 232
% 51.14/6.98  sim_fw_subsumed:                        149
% 51.14/6.98  sim_bw_subsumed:                        5
% 51.14/6.98  sim_fw_subsumption_res:                 0
% 51.14/6.98  sim_bw_subsumption_res:                 0
% 51.14/6.98  sim_tautology_del:                      120
% 51.14/6.98  sim_eq_tautology_del:                   1872
% 51.14/6.98  sim_eq_res_simp:                        57
% 51.14/6.98  sim_fw_demodulated:                     876
% 51.14/6.98  sim_bw_demodulated:                     514
% 51.14/6.98  sim_light_normalised:                   5339
% 51.14/6.98  sim_joinable_taut:                      0
% 51.14/6.98  sim_joinable_simp:                      0
% 51.14/6.98  sim_ac_normalised:                      0
% 51.14/6.98  sim_smt_subsumption:                    0
% 51.14/6.98  
%------------------------------------------------------------------------------
