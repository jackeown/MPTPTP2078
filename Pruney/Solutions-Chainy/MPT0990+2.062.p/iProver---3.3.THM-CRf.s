%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:03:09 EST 2020

% Result     : Theorem 3.37s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  211 (1156 expanded)
%              Number of clauses        :  122 ( 301 expanded)
%              Number of leaves         :   23 ( 311 expanded)
%              Depth                    :   22
%              Number of atoms          :  809 (9686 expanded)
%              Number of equality atoms :  397 (3572 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f49,plain,(
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

fof(f48,plain,
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

fof(f50,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f49,f48])).

fof(f86,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f50])).

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
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f87,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f19,axiom,(
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

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | o_0_0_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f80,f51])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f50])).

fof(f89,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f50])).

fof(f106,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f91,f51])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f62,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | o_0_0_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f79,f51])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f56,f73])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f50])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f69,f73])).

fof(f84,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f50])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
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

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f101,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X4)
      | o_0_0_xboole_0 = X2
      | k2_relset_1(X0,X1,X3) != X1
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(definition_unfolding,[],[f77,f51])).

fof(f85,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f90,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f50])).

fof(f107,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f90,f51])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f95,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f55,f73])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f92,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1262,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1275,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2374,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1275])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1259,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2375,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_1275])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1257,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1282,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X2)
    | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1286,plain,
    ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
    | v1_relat_1(X2) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5059,plain,
    ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1282,c_1286])).

cnf(c_10033,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_5059])).

cnf(c_10181,plain,
    ( v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10033,c_2375])).

cnf(c_10182,plain,
    ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_10181])).

cnf(c_10190,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2375,c_10182])).

cnf(c_33,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1265,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3520,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | sK1 = o_0_0_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1265])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_29,negated_conjecture,
    ( o_0_0_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1333,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
    | o_0_0_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_1422,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | o_0_0_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1333])).

cnf(c_1669,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
    | o_0_0_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1422])).

cnf(c_4332,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3520,c_39,c_38,c_37,c_33,c_31,c_29,c_1669])).

cnf(c_10194,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10190,c_4332])).

cnf(c_10219,plain,
    ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(superposition,[status(thm)],[c_2374,c_10194])).

cnf(c_1263,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1279,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3548,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1279])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4828,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3548,c_40,c_2375])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1276,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3578,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1276])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1264,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | o_0_0_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3151,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | sK1 = o_0_0_xboole_0
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1264])).

cnf(c_1334,plain,
    ( ~ v1_funct_2(X0,X1,sK1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,sK1,X0) != sK1
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | o_0_0_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_1448,plain,
    ( ~ v1_funct_2(sK2,X0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
    | o_0_0_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1334])).

cnf(c_1684,plain,
    ( ~ v1_funct_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(sK0,sK1,sK2) != sK1
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
    | o_0_0_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1448])).

cnf(c_3279,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3151,c_39,c_38,c_37,c_33,c_31,c_29,c_1684])).

cnf(c_3579,plain,
    ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3578,c_3279])).

cnf(c_2,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_3580,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3579,c_2])).

cnf(c_3587,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3580,c_40,c_2375])).

cnf(c_4830,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_4828,c_3587])).

cnf(c_4,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1284,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3199,plain,
    ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1282,c_1284])).

cnf(c_3513,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1257,c_3199])).

cnf(c_4825,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3513,c_2375])).

cnf(c_4831,plain,
    ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4830,c_4825])).

cnf(c_16,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_422,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
    | k6_partfun1(sK0) != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_32])).

cnf(c_423,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_17,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_431,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_423,c_17])).

cnf(c_1255,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1371,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_2135,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1255,c_39,c_37,c_36,c_34,c_431,c_1371])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X4,X1,X3) != X1
    | o_0_0_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1268,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | o_0_0_xboole_0 = X3
    | v1_funct_2(X4,X1,X3) != iProver_top
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X4) = iProver_top
    | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5409,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_33,c_1268])).

cnf(c_41,plain,
    ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_5462,plain,
    ( v1_funct_1(X1) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | o_0_0_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5409,c_40,c_41,c_42])).

cnf(c_5463,plain,
    ( o_0_0_xboole_0 = X0
    | v1_funct_2(X1,sK1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_5462])).

cnf(c_5466,plain,
    ( sK0 = o_0_0_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(k6_partfun1(sK0)) != iProver_top
    | v2_funct_1(sK3) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2135,c_5463])).

cnf(c_43,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_44,plain,
    ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_45,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_30,negated_conjecture,
    ( o_0_0_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_714,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_745,plain,
    ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_715,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1369,plain,
    ( sK0 != X0
    | o_0_0_xboole_0 != X0
    | o_0_0_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_1370,plain,
    ( sK0 != o_0_0_xboole_0
    | o_0_0_xboole_0 = sK0
    | o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1369])).

cnf(c_7,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_3055,plain,
    ( v2_funct_1(k6_partfun1(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3056,plain,
    ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3055])).

cnf(c_6570,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5466,c_43,c_44,c_45,c_30,c_745,c_1370,c_3056])).

cnf(c_6575,plain,
    ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_6570,c_1276])).

cnf(c_21,plain,
    ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X1,X0)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3)
    | k2_relset_1(X1,X0,X3) = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_435,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X2,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,X2,X0) = X2
    | k6_partfun1(X2) != k6_partfun1(sK0)
    | sK0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_32])).

cnf(c_436,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0
    | k6_partfun1(sK0) != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_435])).

cnf(c_523,plain,
    ( ~ v1_funct_2(X0,X1,sK0)
    | ~ v1_funct_2(X2,sK0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X1,sK0,X0) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_436])).

cnf(c_1254,plain,
    ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | k2_relset_1(X0,sK0,X2) = sK0
    | v1_funct_2(X2,X0,sK0) != iProver_top
    | v1_funct_2(X1,sK0,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_1807,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK1) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1254])).

cnf(c_2142,plain,
    ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1807,c_40,c_41,c_42,c_43,c_44,c_45])).

cnf(c_3152,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | sK0 = o_0_0_xboole_0
    | v1_funct_2(sK3,sK1,sK0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2142,c_1264])).

cnf(c_3322,plain,
    ( v2_funct_1(sK3) != iProver_top
    | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3152,c_43,c_44,c_45,c_30,c_745,c_1370])).

cnf(c_3323,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
    | v2_funct_1(sK3) != iProver_top ),
    inference(renaming,[status(thm)],[c_3322])).

cnf(c_6579,plain,
    ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
    inference(superposition,[status(thm)],[c_6570,c_3323])).

cnf(c_6581,plain,
    ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6575,c_6579])).

cnf(c_6582,plain,
    ( k1_relat_1(sK3) = sK1
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6581,c_2])).

cnf(c_6677,plain,
    ( k1_relat_1(sK3) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6582,c_43,c_2374])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1285,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2605,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
    inference(superposition,[status(thm)],[c_2374,c_1285])).

cnf(c_6679,plain,
    ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
    inference(demodulation,[status(thm)],[c_6677,c_2605])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1270,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5348,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1270])).

cnf(c_5469,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5348,c_43])).

cnf(c_5470,plain,
    ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_5469])).

cnf(c_5478,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_5470])).

cnf(c_5479,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5478,c_2135])).

cnf(c_6766,plain,
    ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5479,c_40])).

cnf(c_10226,plain,
    ( k2_funct_1(sK2) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_10219,c_4831,c_6679,c_6766])).

cnf(c_28,negated_conjecture,
    ( k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f92])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10226,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.37/1.05  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.37/1.05  
% 3.37/1.05  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.37/1.05  
% 3.37/1.05  ------  iProver source info
% 3.37/1.05  
% 3.37/1.05  git: date: 2020-06-30 10:37:57 +0100
% 3.37/1.05  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.37/1.05  git: non_committed_changes: false
% 3.37/1.05  git: last_make_outside_of_git: false
% 3.37/1.05  
% 3.37/1.05  ------ 
% 3.37/1.05  
% 3.37/1.05  ------ Input Options
% 3.37/1.05  
% 3.37/1.05  --out_options                           all
% 3.37/1.05  --tptp_safe_out                         true
% 3.37/1.05  --problem_path                          ""
% 3.37/1.05  --include_path                          ""
% 3.37/1.05  --clausifier                            res/vclausify_rel
% 3.37/1.05  --clausifier_options                    ""
% 3.37/1.05  --stdin                                 false
% 3.37/1.05  --stats_out                             all
% 3.37/1.05  
% 3.37/1.05  ------ General Options
% 3.37/1.05  
% 3.37/1.05  --fof                                   false
% 3.37/1.05  --time_out_real                         305.
% 3.37/1.05  --time_out_virtual                      -1.
% 3.37/1.05  --symbol_type_check                     false
% 3.37/1.05  --clausify_out                          false
% 3.37/1.05  --sig_cnt_out                           false
% 3.37/1.05  --trig_cnt_out                          false
% 3.37/1.05  --trig_cnt_out_tolerance                1.
% 3.37/1.05  --trig_cnt_out_sk_spl                   false
% 3.37/1.05  --abstr_cl_out                          false
% 3.37/1.05  
% 3.37/1.05  ------ Global Options
% 3.37/1.05  
% 3.37/1.05  --schedule                              default
% 3.37/1.05  --add_important_lit                     false
% 3.37/1.05  --prop_solver_per_cl                    1000
% 3.37/1.05  --min_unsat_core                        false
% 3.37/1.05  --soft_assumptions                      false
% 3.37/1.05  --soft_lemma_size                       3
% 3.37/1.05  --prop_impl_unit_size                   0
% 3.37/1.05  --prop_impl_unit                        []
% 3.37/1.05  --share_sel_clauses                     true
% 3.37/1.05  --reset_solvers                         false
% 3.37/1.05  --bc_imp_inh                            [conj_cone]
% 3.37/1.05  --conj_cone_tolerance                   3.
% 3.37/1.05  --extra_neg_conj                        none
% 3.37/1.05  --large_theory_mode                     true
% 3.37/1.05  --prolific_symb_bound                   200
% 3.37/1.05  --lt_threshold                          2000
% 3.37/1.05  --clause_weak_htbl                      true
% 3.37/1.05  --gc_record_bc_elim                     false
% 3.37/1.05  
% 3.37/1.05  ------ Preprocessing Options
% 3.37/1.05  
% 3.37/1.05  --preprocessing_flag                    true
% 3.37/1.05  --time_out_prep_mult                    0.1
% 3.37/1.05  --splitting_mode                        input
% 3.37/1.05  --splitting_grd                         true
% 3.37/1.05  --splitting_cvd                         false
% 3.37/1.05  --splitting_cvd_svl                     false
% 3.37/1.05  --splitting_nvd                         32
% 3.37/1.05  --sub_typing                            true
% 3.37/1.05  --prep_gs_sim                           true
% 3.37/1.05  --prep_unflatten                        true
% 3.37/1.05  --prep_res_sim                          true
% 3.37/1.05  --prep_upred                            true
% 3.37/1.05  --prep_sem_filter                       exhaustive
% 3.37/1.05  --prep_sem_filter_out                   false
% 3.37/1.05  --pred_elim                             true
% 3.37/1.05  --res_sim_input                         true
% 3.37/1.05  --eq_ax_congr_red                       true
% 3.37/1.05  --pure_diseq_elim                       true
% 3.37/1.05  --brand_transform                       false
% 3.37/1.05  --non_eq_to_eq                          false
% 3.37/1.05  --prep_def_merge                        true
% 3.37/1.05  --prep_def_merge_prop_impl              false
% 3.37/1.05  --prep_def_merge_mbd                    true
% 3.37/1.05  --prep_def_merge_tr_red                 false
% 3.37/1.05  --prep_def_merge_tr_cl                  false
% 3.37/1.05  --smt_preprocessing                     true
% 3.37/1.05  --smt_ac_axioms                         fast
% 3.37/1.05  --preprocessed_out                      false
% 3.37/1.05  --preprocessed_stats                    false
% 3.37/1.05  
% 3.37/1.05  ------ Abstraction refinement Options
% 3.37/1.05  
% 3.37/1.05  --abstr_ref                             []
% 3.37/1.05  --abstr_ref_prep                        false
% 3.37/1.05  --abstr_ref_until_sat                   false
% 3.37/1.05  --abstr_ref_sig_restrict                funpre
% 3.37/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.05  --abstr_ref_under                       []
% 3.37/1.05  
% 3.37/1.05  ------ SAT Options
% 3.37/1.05  
% 3.37/1.05  --sat_mode                              false
% 3.37/1.05  --sat_fm_restart_options                ""
% 3.37/1.05  --sat_gr_def                            false
% 3.37/1.05  --sat_epr_types                         true
% 3.37/1.05  --sat_non_cyclic_types                  false
% 3.37/1.05  --sat_finite_models                     false
% 3.37/1.05  --sat_fm_lemmas                         false
% 3.37/1.05  --sat_fm_prep                           false
% 3.37/1.05  --sat_fm_uc_incr                        true
% 3.37/1.05  --sat_out_model                         small
% 3.37/1.05  --sat_out_clauses                       false
% 3.37/1.05  
% 3.37/1.05  ------ QBF Options
% 3.37/1.05  
% 3.37/1.05  --qbf_mode                              false
% 3.37/1.05  --qbf_elim_univ                         false
% 3.37/1.05  --qbf_dom_inst                          none
% 3.37/1.05  --qbf_dom_pre_inst                      false
% 3.37/1.05  --qbf_sk_in                             false
% 3.37/1.05  --qbf_pred_elim                         true
% 3.37/1.05  --qbf_split                             512
% 3.37/1.05  
% 3.37/1.05  ------ BMC1 Options
% 3.37/1.05  
% 3.37/1.05  --bmc1_incremental                      false
% 3.37/1.05  --bmc1_axioms                           reachable_all
% 3.37/1.05  --bmc1_min_bound                        0
% 3.37/1.05  --bmc1_max_bound                        -1
% 3.37/1.05  --bmc1_max_bound_default                -1
% 3.37/1.05  --bmc1_symbol_reachability              true
% 3.37/1.05  --bmc1_property_lemmas                  false
% 3.37/1.05  --bmc1_k_induction                      false
% 3.37/1.05  --bmc1_non_equiv_states                 false
% 3.37/1.05  --bmc1_deadlock                         false
% 3.37/1.05  --bmc1_ucm                              false
% 3.37/1.05  --bmc1_add_unsat_core                   none
% 3.37/1.05  --bmc1_unsat_core_children              false
% 3.37/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.05  --bmc1_out_stat                         full
% 3.37/1.05  --bmc1_ground_init                      false
% 3.37/1.05  --bmc1_pre_inst_next_state              false
% 3.37/1.05  --bmc1_pre_inst_state                   false
% 3.37/1.05  --bmc1_pre_inst_reach_state             false
% 3.37/1.05  --bmc1_out_unsat_core                   false
% 3.37/1.05  --bmc1_aig_witness_out                  false
% 3.37/1.05  --bmc1_verbose                          false
% 3.37/1.05  --bmc1_dump_clauses_tptp                false
% 3.37/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.05  --bmc1_dump_file                        -
% 3.37/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.05  --bmc1_ucm_extend_mode                  1
% 3.37/1.05  --bmc1_ucm_init_mode                    2
% 3.37/1.05  --bmc1_ucm_cone_mode                    none
% 3.37/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.05  --bmc1_ucm_relax_model                  4
% 3.37/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.05  --bmc1_ucm_layered_model                none
% 3.37/1.05  --bmc1_ucm_max_lemma_size               10
% 3.37/1.05  
% 3.37/1.05  ------ AIG Options
% 3.37/1.05  
% 3.37/1.05  --aig_mode                              false
% 3.37/1.05  
% 3.37/1.05  ------ Instantiation Options
% 3.37/1.05  
% 3.37/1.05  --instantiation_flag                    true
% 3.37/1.05  --inst_sos_flag                         true
% 3.37/1.05  --inst_sos_phase                        true
% 3.37/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.05  --inst_lit_sel_side                     num_symb
% 3.37/1.05  --inst_solver_per_active                1400
% 3.37/1.05  --inst_solver_calls_frac                1.
% 3.37/1.05  --inst_passive_queue_type               priority_queues
% 3.37/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.05  --inst_passive_queues_freq              [25;2]
% 3.37/1.05  --inst_dismatching                      true
% 3.37/1.05  --inst_eager_unprocessed_to_passive     true
% 3.37/1.05  --inst_prop_sim_given                   true
% 3.37/1.05  --inst_prop_sim_new                     false
% 3.37/1.05  --inst_subs_new                         false
% 3.37/1.05  --inst_eq_res_simp                      false
% 3.37/1.05  --inst_subs_given                       false
% 3.37/1.05  --inst_orphan_elimination               true
% 3.37/1.05  --inst_learning_loop_flag               true
% 3.37/1.05  --inst_learning_start                   3000
% 3.37/1.05  --inst_learning_factor                  2
% 3.37/1.05  --inst_start_prop_sim_after_learn       3
% 3.37/1.05  --inst_sel_renew                        solver
% 3.37/1.05  --inst_lit_activity_flag                true
% 3.37/1.05  --inst_restr_to_given                   false
% 3.37/1.05  --inst_activity_threshold               500
% 3.37/1.05  --inst_out_proof                        true
% 3.37/1.05  
% 3.37/1.05  ------ Resolution Options
% 3.37/1.05  
% 3.37/1.05  --resolution_flag                       true
% 3.37/1.05  --res_lit_sel                           adaptive
% 3.37/1.05  --res_lit_sel_side                      none
% 3.37/1.05  --res_ordering                          kbo
% 3.37/1.05  --res_to_prop_solver                    active
% 3.37/1.05  --res_prop_simpl_new                    false
% 3.37/1.05  --res_prop_simpl_given                  true
% 3.37/1.05  --res_passive_queue_type                priority_queues
% 3.37/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.05  --res_passive_queues_freq               [15;5]
% 3.37/1.05  --res_forward_subs                      full
% 3.37/1.05  --res_backward_subs                     full
% 3.37/1.05  --res_forward_subs_resolution           true
% 3.37/1.05  --res_backward_subs_resolution          true
% 3.37/1.05  --res_orphan_elimination                true
% 3.37/1.05  --res_time_limit                        2.
% 3.37/1.05  --res_out_proof                         true
% 3.37/1.05  
% 3.37/1.05  ------ Superposition Options
% 3.37/1.05  
% 3.37/1.05  --superposition_flag                    true
% 3.37/1.05  --sup_passive_queue_type                priority_queues
% 3.37/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.05  --demod_completeness_check              fast
% 3.37/1.05  --demod_use_ground                      true
% 3.37/1.05  --sup_to_prop_solver                    passive
% 3.37/1.05  --sup_prop_simpl_new                    true
% 3.37/1.05  --sup_prop_simpl_given                  true
% 3.37/1.05  --sup_fun_splitting                     true
% 3.37/1.05  --sup_smt_interval                      50000
% 3.37/1.05  
% 3.37/1.05  ------ Superposition Simplification Setup
% 3.37/1.05  
% 3.37/1.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.37/1.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.37/1.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.37/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.37/1.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.37/1.05  --sup_immed_triv                        [TrivRules]
% 3.37/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.05  --sup_immed_bw_main                     []
% 3.37/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.37/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.05  --sup_input_bw                          []
% 3.37/1.05  
% 3.37/1.05  ------ Combination Options
% 3.37/1.05  
% 3.37/1.05  --comb_res_mult                         3
% 3.37/1.05  --comb_sup_mult                         2
% 3.37/1.05  --comb_inst_mult                        10
% 3.37/1.05  
% 3.37/1.05  ------ Debug Options
% 3.37/1.05  
% 3.37/1.05  --dbg_backtrace                         false
% 3.37/1.05  --dbg_dump_prop_clauses                 false
% 3.37/1.05  --dbg_dump_prop_clauses_file            -
% 3.37/1.05  --dbg_out_stat                          false
% 3.37/1.05  ------ Parsing...
% 3.37/1.05  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.37/1.05  
% 3.37/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.37/1.05  
% 3.37/1.05  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.37/1.05  
% 3.37/1.05  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.37/1.05  ------ Proving...
% 3.37/1.05  ------ Problem Properties 
% 3.37/1.05  
% 3.37/1.05  
% 3.37/1.05  clauses                                 39
% 3.37/1.05  conjectures                             11
% 3.37/1.05  EPR                                     7
% 3.37/1.05  Horn                                    35
% 3.37/1.05  unary                                   16
% 3.37/1.05  binary                                  5
% 3.37/1.05  lits                                    135
% 3.37/1.05  lits eq                                 32
% 3.37/1.05  fd_pure                                 0
% 3.37/1.05  fd_pseudo                               0
% 3.37/1.05  fd_cond                                 4
% 3.37/1.05  fd_pseudo_cond                          0
% 3.37/1.05  AC symbols                              0
% 3.37/1.05  
% 3.37/1.05  ------ Schedule dynamic 5 is on 
% 3.37/1.05  
% 3.37/1.05  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.37/1.05  
% 3.37/1.05  
% 3.37/1.05  ------ 
% 3.37/1.05  Current options:
% 3.37/1.05  ------ 
% 3.37/1.05  
% 3.37/1.05  ------ Input Options
% 3.37/1.05  
% 3.37/1.05  --out_options                           all
% 3.37/1.05  --tptp_safe_out                         true
% 3.37/1.05  --problem_path                          ""
% 3.37/1.05  --include_path                          ""
% 3.37/1.05  --clausifier                            res/vclausify_rel
% 3.37/1.05  --clausifier_options                    ""
% 3.37/1.05  --stdin                                 false
% 3.37/1.05  --stats_out                             all
% 3.37/1.05  
% 3.37/1.05  ------ General Options
% 3.37/1.05  
% 3.37/1.05  --fof                                   false
% 3.37/1.05  --time_out_real                         305.
% 3.37/1.05  --time_out_virtual                      -1.
% 3.37/1.05  --symbol_type_check                     false
% 3.37/1.05  --clausify_out                          false
% 3.37/1.05  --sig_cnt_out                           false
% 3.37/1.05  --trig_cnt_out                          false
% 3.37/1.05  --trig_cnt_out_tolerance                1.
% 3.37/1.05  --trig_cnt_out_sk_spl                   false
% 3.37/1.05  --abstr_cl_out                          false
% 3.37/1.05  
% 3.37/1.05  ------ Global Options
% 3.37/1.05  
% 3.37/1.05  --schedule                              default
% 3.37/1.05  --add_important_lit                     false
% 3.37/1.05  --prop_solver_per_cl                    1000
% 3.37/1.05  --min_unsat_core                        false
% 3.37/1.05  --soft_assumptions                      false
% 3.37/1.05  --soft_lemma_size                       3
% 3.37/1.05  --prop_impl_unit_size                   0
% 3.37/1.05  --prop_impl_unit                        []
% 3.37/1.05  --share_sel_clauses                     true
% 3.37/1.05  --reset_solvers                         false
% 3.37/1.05  --bc_imp_inh                            [conj_cone]
% 3.37/1.05  --conj_cone_tolerance                   3.
% 3.37/1.05  --extra_neg_conj                        none
% 3.37/1.05  --large_theory_mode                     true
% 3.37/1.05  --prolific_symb_bound                   200
% 3.37/1.05  --lt_threshold                          2000
% 3.37/1.05  --clause_weak_htbl                      true
% 3.37/1.05  --gc_record_bc_elim                     false
% 3.37/1.05  
% 3.37/1.05  ------ Preprocessing Options
% 3.37/1.05  
% 3.37/1.05  --preprocessing_flag                    true
% 3.37/1.05  --time_out_prep_mult                    0.1
% 3.37/1.05  --splitting_mode                        input
% 3.37/1.05  --splitting_grd                         true
% 3.37/1.05  --splitting_cvd                         false
% 3.37/1.05  --splitting_cvd_svl                     false
% 3.37/1.05  --splitting_nvd                         32
% 3.37/1.05  --sub_typing                            true
% 3.37/1.05  --prep_gs_sim                           true
% 3.37/1.05  --prep_unflatten                        true
% 3.37/1.05  --prep_res_sim                          true
% 3.37/1.05  --prep_upred                            true
% 3.37/1.05  --prep_sem_filter                       exhaustive
% 3.37/1.05  --prep_sem_filter_out                   false
% 3.37/1.05  --pred_elim                             true
% 3.37/1.05  --res_sim_input                         true
% 3.37/1.05  --eq_ax_congr_red                       true
% 3.37/1.05  --pure_diseq_elim                       true
% 3.37/1.05  --brand_transform                       false
% 3.37/1.05  --non_eq_to_eq                          false
% 3.37/1.05  --prep_def_merge                        true
% 3.37/1.05  --prep_def_merge_prop_impl              false
% 3.37/1.05  --prep_def_merge_mbd                    true
% 3.37/1.05  --prep_def_merge_tr_red                 false
% 3.37/1.05  --prep_def_merge_tr_cl                  false
% 3.37/1.05  --smt_preprocessing                     true
% 3.37/1.05  --smt_ac_axioms                         fast
% 3.37/1.05  --preprocessed_out                      false
% 3.37/1.05  --preprocessed_stats                    false
% 3.37/1.05  
% 3.37/1.05  ------ Abstraction refinement Options
% 3.37/1.05  
% 3.37/1.05  --abstr_ref                             []
% 3.37/1.05  --abstr_ref_prep                        false
% 3.37/1.05  --abstr_ref_until_sat                   false
% 3.37/1.05  --abstr_ref_sig_restrict                funpre
% 3.37/1.05  --abstr_ref_af_restrict_to_split_sk     false
% 3.37/1.05  --abstr_ref_under                       []
% 3.37/1.05  
% 3.37/1.05  ------ SAT Options
% 3.37/1.05  
% 3.37/1.05  --sat_mode                              false
% 3.37/1.05  --sat_fm_restart_options                ""
% 3.37/1.05  --sat_gr_def                            false
% 3.37/1.05  --sat_epr_types                         true
% 3.37/1.05  --sat_non_cyclic_types                  false
% 3.37/1.05  --sat_finite_models                     false
% 3.37/1.05  --sat_fm_lemmas                         false
% 3.37/1.05  --sat_fm_prep                           false
% 3.37/1.05  --sat_fm_uc_incr                        true
% 3.37/1.05  --sat_out_model                         small
% 3.37/1.05  --sat_out_clauses                       false
% 3.37/1.05  
% 3.37/1.05  ------ QBF Options
% 3.37/1.05  
% 3.37/1.05  --qbf_mode                              false
% 3.37/1.05  --qbf_elim_univ                         false
% 3.37/1.05  --qbf_dom_inst                          none
% 3.37/1.05  --qbf_dom_pre_inst                      false
% 3.37/1.05  --qbf_sk_in                             false
% 3.37/1.05  --qbf_pred_elim                         true
% 3.37/1.05  --qbf_split                             512
% 3.37/1.05  
% 3.37/1.05  ------ BMC1 Options
% 3.37/1.05  
% 3.37/1.05  --bmc1_incremental                      false
% 3.37/1.05  --bmc1_axioms                           reachable_all
% 3.37/1.05  --bmc1_min_bound                        0
% 3.37/1.05  --bmc1_max_bound                        -1
% 3.37/1.05  --bmc1_max_bound_default                -1
% 3.37/1.05  --bmc1_symbol_reachability              true
% 3.37/1.05  --bmc1_property_lemmas                  false
% 3.37/1.05  --bmc1_k_induction                      false
% 3.37/1.05  --bmc1_non_equiv_states                 false
% 3.37/1.05  --bmc1_deadlock                         false
% 3.37/1.05  --bmc1_ucm                              false
% 3.37/1.05  --bmc1_add_unsat_core                   none
% 3.37/1.05  --bmc1_unsat_core_children              false
% 3.37/1.05  --bmc1_unsat_core_extrapolate_axioms    false
% 3.37/1.05  --bmc1_out_stat                         full
% 3.37/1.05  --bmc1_ground_init                      false
% 3.37/1.05  --bmc1_pre_inst_next_state              false
% 3.37/1.05  --bmc1_pre_inst_state                   false
% 3.37/1.05  --bmc1_pre_inst_reach_state             false
% 3.37/1.05  --bmc1_out_unsat_core                   false
% 3.37/1.05  --bmc1_aig_witness_out                  false
% 3.37/1.05  --bmc1_verbose                          false
% 3.37/1.05  --bmc1_dump_clauses_tptp                false
% 3.37/1.05  --bmc1_dump_unsat_core_tptp             false
% 3.37/1.05  --bmc1_dump_file                        -
% 3.37/1.05  --bmc1_ucm_expand_uc_limit              128
% 3.37/1.05  --bmc1_ucm_n_expand_iterations          6
% 3.37/1.05  --bmc1_ucm_extend_mode                  1
% 3.37/1.05  --bmc1_ucm_init_mode                    2
% 3.37/1.05  --bmc1_ucm_cone_mode                    none
% 3.37/1.05  --bmc1_ucm_reduced_relation_type        0
% 3.37/1.05  --bmc1_ucm_relax_model                  4
% 3.37/1.05  --bmc1_ucm_full_tr_after_sat            true
% 3.37/1.05  --bmc1_ucm_expand_neg_assumptions       false
% 3.37/1.05  --bmc1_ucm_layered_model                none
% 3.37/1.05  --bmc1_ucm_max_lemma_size               10
% 3.37/1.05  
% 3.37/1.05  ------ AIG Options
% 3.37/1.05  
% 3.37/1.05  --aig_mode                              false
% 3.37/1.05  
% 3.37/1.05  ------ Instantiation Options
% 3.37/1.05  
% 3.37/1.05  --instantiation_flag                    true
% 3.37/1.05  --inst_sos_flag                         true
% 3.37/1.05  --inst_sos_phase                        true
% 3.37/1.05  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.37/1.05  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.37/1.05  --inst_lit_sel_side                     none
% 3.37/1.05  --inst_solver_per_active                1400
% 3.37/1.05  --inst_solver_calls_frac                1.
% 3.37/1.05  --inst_passive_queue_type               priority_queues
% 3.37/1.05  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.37/1.05  --inst_passive_queues_freq              [25;2]
% 3.37/1.05  --inst_dismatching                      true
% 3.37/1.05  --inst_eager_unprocessed_to_passive     true
% 3.37/1.05  --inst_prop_sim_given                   true
% 3.37/1.05  --inst_prop_sim_new                     false
% 3.37/1.05  --inst_subs_new                         false
% 3.37/1.05  --inst_eq_res_simp                      false
% 3.37/1.05  --inst_subs_given                       false
% 3.37/1.05  --inst_orphan_elimination               true
% 3.37/1.05  --inst_learning_loop_flag               true
% 3.37/1.05  --inst_learning_start                   3000
% 3.37/1.05  --inst_learning_factor                  2
% 3.37/1.05  --inst_start_prop_sim_after_learn       3
% 3.37/1.05  --inst_sel_renew                        solver
% 3.37/1.05  --inst_lit_activity_flag                true
% 3.37/1.05  --inst_restr_to_given                   false
% 3.37/1.05  --inst_activity_threshold               500
% 3.37/1.05  --inst_out_proof                        true
% 3.37/1.05  
% 3.37/1.05  ------ Resolution Options
% 3.37/1.05  
% 3.37/1.05  --resolution_flag                       false
% 3.37/1.05  --res_lit_sel                           adaptive
% 3.37/1.05  --res_lit_sel_side                      none
% 3.37/1.05  --res_ordering                          kbo
% 3.37/1.05  --res_to_prop_solver                    active
% 3.37/1.05  --res_prop_simpl_new                    false
% 3.37/1.05  --res_prop_simpl_given                  true
% 3.37/1.05  --res_passive_queue_type                priority_queues
% 3.37/1.05  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.37/1.05  --res_passive_queues_freq               [15;5]
% 3.37/1.05  --res_forward_subs                      full
% 3.37/1.05  --res_backward_subs                     full
% 3.37/1.05  --res_forward_subs_resolution           true
% 3.37/1.05  --res_backward_subs_resolution          true
% 3.37/1.05  --res_orphan_elimination                true
% 3.37/1.05  --res_time_limit                        2.
% 3.37/1.05  --res_out_proof                         true
% 3.37/1.05  
% 3.37/1.05  ------ Superposition Options
% 3.37/1.05  
% 3.37/1.05  --superposition_flag                    true
% 3.37/1.05  --sup_passive_queue_type                priority_queues
% 3.37/1.05  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.37/1.05  --sup_passive_queues_freq               [8;1;4]
% 3.37/1.05  --demod_completeness_check              fast
% 3.37/1.05  --demod_use_ground                      true
% 3.37/1.05  --sup_to_prop_solver                    passive
% 3.37/1.05  --sup_prop_simpl_new                    true
% 3.37/1.05  --sup_prop_simpl_given                  true
% 3.37/1.05  --sup_fun_splitting                     true
% 3.37/1.05  --sup_smt_interval                      50000
% 3.37/1.05  
% 3.37/1.05  ------ Superposition Simplification Setup
% 3.37/1.05  
% 3.37/1.05  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.37/1.05  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.37/1.05  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.37/1.05  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.37/1.05  --sup_full_triv                         [TrivRules;PropSubs]
% 3.37/1.05  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.37/1.05  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.37/1.05  --sup_immed_triv                        [TrivRules]
% 3.37/1.05  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.05  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.05  --sup_immed_bw_main                     []
% 3.37/1.05  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.37/1.05  --sup_input_triv                        [Unflattening;TrivRules]
% 3.37/1.05  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.37/1.05  --sup_input_bw                          []
% 3.37/1.05  
% 3.37/1.05  ------ Combination Options
% 3.37/1.05  
% 3.37/1.05  --comb_res_mult                         3
% 3.37/1.05  --comb_sup_mult                         2
% 3.37/1.05  --comb_inst_mult                        10
% 3.37/1.05  
% 3.37/1.05  ------ Debug Options
% 3.37/1.05  
% 3.37/1.05  --dbg_backtrace                         false
% 3.37/1.05  --dbg_dump_prop_clauses                 false
% 3.37/1.05  --dbg_dump_prop_clauses_file            -
% 3.37/1.05  --dbg_out_stat                          false
% 3.37/1.05  
% 3.37/1.05  
% 3.37/1.05  
% 3.37/1.05  
% 3.37/1.05  ------ Proving...
% 3.37/1.05  
% 3.37/1.05  
% 3.37/1.05  % SZS status Theorem for theBenchmark.p
% 3.37/1.05  
% 3.37/1.05  % SZS output start CNFRefutation for theBenchmark.p
% 3.37/1.05  
% 3.37/1.05  fof(f20,conjecture,(
% 3.37/1.05    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.37/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.05  
% 3.37/1.05  fof(f21,negated_conjecture,(
% 3.37/1.05    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 3.37/1.05    inference(negated_conjecture,[],[f20])).
% 3.37/1.05  
% 3.37/1.05  fof(f45,plain,(
% 3.37/1.05    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.37/1.05    inference(ennf_transformation,[],[f21])).
% 3.37/1.05  
% 3.37/1.05  fof(f46,plain,(
% 3.37/1.05    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.37/1.05    inference(flattening,[],[f45])).
% 3.37/1.05  
% 3.37/1.05  fof(f49,plain,(
% 3.37/1.05    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 3.37/1.05    introduced(choice_axiom,[])).
% 3.37/1.05  
% 3.37/1.05  fof(f48,plain,(
% 3.37/1.05    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.37/1.05    introduced(choice_axiom,[])).
% 3.37/1.05  
% 3.37/1.05  fof(f50,plain,(
% 3.37/1.05    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.37/1.05    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f46,f49,f48])).
% 3.37/1.05  
% 3.37/1.05  fof(f86,plain,(
% 3.37/1.05    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 3.37/1.05    inference(cnf_transformation,[],[f50])).
% 3.37/1.05  
% 3.37/1.05  fof(f10,axiom,(
% 3.37/1.05    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.37/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.05  
% 3.37/1.05  fof(f31,plain,(
% 3.37/1.05    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/1.05    inference(ennf_transformation,[],[f10])).
% 3.37/1.05  
% 3.37/1.05  fof(f65,plain,(
% 3.37/1.05    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.37/1.05    inference(cnf_transformation,[],[f31])).
% 3.37/1.05  
% 3.37/1.05  fof(f83,plain,(
% 3.37/1.05    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.37/1.05    inference(cnf_transformation,[],[f50])).
% 3.37/1.05  
% 3.37/1.05  fof(f81,plain,(
% 3.37/1.05    v1_funct_1(sK2)),
% 3.37/1.05    inference(cnf_transformation,[],[f50])).
% 3.37/1.05  
% 3.37/1.05  fof(f6,axiom,(
% 3.37/1.05    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.37/1.05    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.05  
% 3.37/1.05  fof(f25,plain,(
% 3.37/1.05    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.37/1.05    inference(ennf_transformation,[],[f6])).
% 3.37/1.05  
% 3.37/1.05  fof(f26,plain,(
% 3.37/1.05    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.05    inference(flattening,[],[f25])).
% 3.37/1.05  
% 3.37/1.05  fof(f57,plain,(
% 3.37/1.05    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.05    inference(cnf_transformation,[],[f26])).
% 3.37/1.05  
% 3.37/1.05  fof(f2,axiom,(
% 3.37/1.05    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f22,plain,(
% 3.37/1.06    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.37/1.06    inference(ennf_transformation,[],[f2])).
% 3.37/1.06  
% 3.37/1.06  fof(f52,plain,(
% 3.37/1.06    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f22])).
% 3.37/1.06  
% 3.37/1.06  fof(f87,plain,(
% 3.37/1.06    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.37/1.06    inference(cnf_transformation,[],[f50])).
% 3.37/1.06  
% 3.37/1.06  fof(f19,axiom,(
% 3.37/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f43,plain,(
% 3.37/1.06    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.37/1.06    inference(ennf_transformation,[],[f19])).
% 3.37/1.06  
% 3.37/1.06  fof(f44,plain,(
% 3.37/1.06    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.37/1.06    inference(flattening,[],[f43])).
% 3.37/1.06  
% 3.37/1.06  fof(f80,plain,(
% 3.37/1.06    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f44])).
% 3.37/1.06  
% 3.37/1.06  fof(f1,axiom,(
% 3.37/1.06    k1_xboole_0 = o_0_0_xboole_0),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f51,plain,(
% 3.37/1.06    k1_xboole_0 = o_0_0_xboole_0),
% 3.37/1.06    inference(cnf_transformation,[],[f1])).
% 3.37/1.06  
% 3.37/1.06  fof(f104,plain,(
% 3.37/1.06    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | o_0_0_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.37/1.06    inference(definition_unfolding,[],[f80,f51])).
% 3.37/1.06  
% 3.37/1.06  fof(f82,plain,(
% 3.37/1.06    v1_funct_2(sK2,sK0,sK1)),
% 3.37/1.06    inference(cnf_transformation,[],[f50])).
% 3.37/1.06  
% 3.37/1.06  fof(f89,plain,(
% 3.37/1.06    v2_funct_1(sK2)),
% 3.37/1.06    inference(cnf_transformation,[],[f50])).
% 3.37/1.06  
% 3.37/1.06  fof(f91,plain,(
% 3.37/1.06    k1_xboole_0 != sK1),
% 3.37/1.06    inference(cnf_transformation,[],[f50])).
% 3.37/1.06  
% 3.37/1.06  fof(f106,plain,(
% 3.37/1.06    o_0_0_xboole_0 != sK1),
% 3.37/1.06    inference(definition_unfolding,[],[f91,f51])).
% 3.37/1.06  
% 3.37/1.06  fof(f8,axiom,(
% 3.37/1.06    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f27,plain,(
% 3.37/1.06    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.37/1.06    inference(ennf_transformation,[],[f8])).
% 3.37/1.06  
% 3.37/1.06  fof(f28,plain,(
% 3.37/1.06    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.06    inference(flattening,[],[f27])).
% 3.37/1.06  
% 3.37/1.06  fof(f62,plain,(
% 3.37/1.06    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f28])).
% 3.37/1.06  
% 3.37/1.06  fof(f9,axiom,(
% 3.37/1.06    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f29,plain,(
% 3.37/1.06    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.37/1.06    inference(ennf_transformation,[],[f9])).
% 3.37/1.06  
% 3.37/1.06  fof(f30,plain,(
% 3.37/1.06    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.37/1.06    inference(flattening,[],[f29])).
% 3.37/1.06  
% 3.37/1.06  fof(f63,plain,(
% 3.37/1.06    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f30])).
% 3.37/1.06  
% 3.37/1.06  fof(f79,plain,(
% 3.37/1.06    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f44])).
% 3.37/1.06  
% 3.37/1.06  fof(f105,plain,(
% 3.37/1.06    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | o_0_0_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.37/1.06    inference(definition_unfolding,[],[f79,f51])).
% 3.37/1.06  
% 3.37/1.06  fof(f3,axiom,(
% 3.37/1.06    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f53,plain,(
% 3.37/1.06    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.37/1.06    inference(cnf_transformation,[],[f3])).
% 3.37/1.06  
% 3.37/1.06  fof(f16,axiom,(
% 3.37/1.06    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f73,plain,(
% 3.37/1.06    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f16])).
% 3.37/1.06  
% 3.37/1.06  fof(f94,plain,(
% 3.37/1.06    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.37/1.06    inference(definition_unfolding,[],[f53,f73])).
% 3.37/1.06  
% 3.37/1.06  fof(f5,axiom,(
% 3.37/1.06    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f24,plain,(
% 3.37/1.06    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.37/1.06    inference(ennf_transformation,[],[f5])).
% 3.37/1.06  
% 3.37/1.06  fof(f56,plain,(
% 3.37/1.06    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f24])).
% 3.37/1.06  
% 3.37/1.06  fof(f96,plain,(
% 3.37/1.06    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.37/1.06    inference(definition_unfolding,[],[f56,f73])).
% 3.37/1.06  
% 3.37/1.06  fof(f12,axiom,(
% 3.37/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f33,plain,(
% 3.37/1.06    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.37/1.06    inference(ennf_transformation,[],[f12])).
% 3.37/1.06  
% 3.37/1.06  fof(f34,plain,(
% 3.37/1.06    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/1.06    inference(flattening,[],[f33])).
% 3.37/1.06  
% 3.37/1.06  fof(f47,plain,(
% 3.37/1.06    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.37/1.06    inference(nnf_transformation,[],[f34])).
% 3.37/1.06  
% 3.37/1.06  fof(f67,plain,(
% 3.37/1.06    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.37/1.06    inference(cnf_transformation,[],[f47])).
% 3.37/1.06  
% 3.37/1.06  fof(f88,plain,(
% 3.37/1.06    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 3.37/1.06    inference(cnf_transformation,[],[f50])).
% 3.37/1.06  
% 3.37/1.06  fof(f13,axiom,(
% 3.37/1.06    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f69,plain,(
% 3.37/1.06    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.37/1.06    inference(cnf_transformation,[],[f13])).
% 3.37/1.06  
% 3.37/1.06  fof(f99,plain,(
% 3.37/1.06    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 3.37/1.06    inference(definition_unfolding,[],[f69,f73])).
% 3.37/1.06  
% 3.37/1.06  fof(f84,plain,(
% 3.37/1.06    v1_funct_1(sK3)),
% 3.37/1.06    inference(cnf_transformation,[],[f50])).
% 3.37/1.06  
% 3.37/1.06  fof(f14,axiom,(
% 3.37/1.06    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f35,plain,(
% 3.37/1.06    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.37/1.06    inference(ennf_transformation,[],[f14])).
% 3.37/1.06  
% 3.37/1.06  fof(f36,plain,(
% 3.37/1.06    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.37/1.06    inference(flattening,[],[f35])).
% 3.37/1.06  
% 3.37/1.06  fof(f71,plain,(
% 3.37/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f36])).
% 3.37/1.06  
% 3.37/1.06  fof(f18,axiom,(
% 3.37/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f41,plain,(
% 3.37/1.06    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.37/1.06    inference(ennf_transformation,[],[f18])).
% 3.37/1.06  
% 3.37/1.06  fof(f42,plain,(
% 3.37/1.06    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.37/1.06    inference(flattening,[],[f41])).
% 3.37/1.06  
% 3.37/1.06  fof(f77,plain,(
% 3.37/1.06    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f42])).
% 3.37/1.06  
% 3.37/1.06  fof(f101,plain,(
% 3.37/1.06    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | o_0_0_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.37/1.06    inference(definition_unfolding,[],[f77,f51])).
% 3.37/1.06  
% 3.37/1.06  fof(f85,plain,(
% 3.37/1.06    v1_funct_2(sK3,sK1,sK0)),
% 3.37/1.06    inference(cnf_transformation,[],[f50])).
% 3.37/1.06  
% 3.37/1.06  fof(f90,plain,(
% 3.37/1.06    k1_xboole_0 != sK0),
% 3.37/1.06    inference(cnf_transformation,[],[f50])).
% 3.37/1.06  
% 3.37/1.06  fof(f107,plain,(
% 3.37/1.06    o_0_0_xboole_0 != sK0),
% 3.37/1.06    inference(definition_unfolding,[],[f90,f51])).
% 3.37/1.06  
% 3.37/1.06  fof(f7,axiom,(
% 3.37/1.06    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f60,plain,(
% 3.37/1.06    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.37/1.06    inference(cnf_transformation,[],[f7])).
% 3.37/1.06  
% 3.37/1.06  fof(f97,plain,(
% 3.37/1.06    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.37/1.06    inference(definition_unfolding,[],[f60,f73])).
% 3.37/1.06  
% 3.37/1.06  fof(f17,axiom,(
% 3.37/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f39,plain,(
% 3.37/1.06    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.37/1.06    inference(ennf_transformation,[],[f17])).
% 3.37/1.06  
% 3.37/1.06  fof(f40,plain,(
% 3.37/1.06    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.37/1.06    inference(flattening,[],[f39])).
% 3.37/1.06  
% 3.37/1.06  fof(f74,plain,(
% 3.37/1.06    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f40])).
% 3.37/1.06  
% 3.37/1.06  fof(f4,axiom,(
% 3.37/1.06    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f23,plain,(
% 3.37/1.06    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 3.37/1.06    inference(ennf_transformation,[],[f4])).
% 3.37/1.06  
% 3.37/1.06  fof(f55,plain,(
% 3.37/1.06    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f23])).
% 3.37/1.06  
% 3.37/1.06  fof(f95,plain,(
% 3.37/1.06    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 3.37/1.06    inference(definition_unfolding,[],[f55,f73])).
% 3.37/1.06  
% 3.37/1.06  fof(f15,axiom,(
% 3.37/1.06    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 3.37/1.06    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.37/1.06  
% 3.37/1.06  fof(f37,plain,(
% 3.37/1.06    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 3.37/1.06    inference(ennf_transformation,[],[f15])).
% 3.37/1.06  
% 3.37/1.06  fof(f38,plain,(
% 3.37/1.06    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 3.37/1.06    inference(flattening,[],[f37])).
% 3.37/1.06  
% 3.37/1.06  fof(f72,plain,(
% 3.37/1.06    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 3.37/1.06    inference(cnf_transformation,[],[f38])).
% 3.37/1.06  
% 3.37/1.06  fof(f92,plain,(
% 3.37/1.06    k2_funct_1(sK2) != sK3),
% 3.37/1.06    inference(cnf_transformation,[],[f50])).
% 3.37/1.06  
% 3.37/1.06  cnf(c_34,negated_conjecture,
% 3.37/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 3.37/1.06      inference(cnf_transformation,[],[f86]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1262,plain,
% 3.37/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_13,plain,
% 3.37/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.06      | v1_relat_1(X0) ),
% 3.37/1.06      inference(cnf_transformation,[],[f65]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1275,plain,
% 3.37/1.06      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.37/1.06      | v1_relat_1(X0) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_2374,plain,
% 3.37/1.06      ( v1_relat_1(sK3) = iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_1262,c_1275]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_37,negated_conjecture,
% 3.37/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.37/1.06      inference(cnf_transformation,[],[f83]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1259,plain,
% 3.37/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_2375,plain,
% 3.37/1.06      ( v1_relat_1(sK2) = iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_1259,c_1275]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_39,negated_conjecture,
% 3.37/1.06      ( v1_funct_1(sK2) ),
% 3.37/1.06      inference(cnf_transformation,[],[f81]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1257,plain,
% 3.37/1.06      ( v1_funct_1(sK2) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_6,plain,
% 3.37/1.06      ( ~ v1_funct_1(X0)
% 3.37/1.06      | ~ v1_relat_1(X0)
% 3.37/1.06      | v1_relat_1(k2_funct_1(X0)) ),
% 3.37/1.06      inference(cnf_transformation,[],[f57]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1282,plain,
% 3.37/1.06      ( v1_funct_1(X0) != iProver_top
% 3.37/1.06      | v1_relat_1(X0) != iProver_top
% 3.37/1.06      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_0,plain,
% 3.37/1.06      ( ~ v1_relat_1(X0)
% 3.37/1.06      | ~ v1_relat_1(X1)
% 3.37/1.06      | ~ v1_relat_1(X2)
% 3.37/1.06      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 3.37/1.06      inference(cnf_transformation,[],[f52]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1286,plain,
% 3.37/1.06      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 3.37/1.06      | v1_relat_1(X2) != iProver_top
% 3.37/1.06      | v1_relat_1(X1) != iProver_top
% 3.37/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_5059,plain,
% 3.37/1.06      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 3.37/1.06      | v1_funct_1(X0) != iProver_top
% 3.37/1.06      | v1_relat_1(X0) != iProver_top
% 3.37/1.06      | v1_relat_1(X1) != iProver_top
% 3.37/1.06      | v1_relat_1(X2) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_1282,c_1286]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_10033,plain,
% 3.37/1.06      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 3.37/1.06      | v1_relat_1(X0) != iProver_top
% 3.37/1.06      | v1_relat_1(X1) != iProver_top
% 3.37/1.06      | v1_relat_1(sK2) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_1257,c_5059]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_10181,plain,
% 3.37/1.06      ( v1_relat_1(X1) != iProver_top
% 3.37/1.06      | v1_relat_1(X0) != iProver_top
% 3.37/1.06      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_10033,c_2375]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_10182,plain,
% 3.37/1.06      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 3.37/1.06      | v1_relat_1(X0) != iProver_top
% 3.37/1.06      | v1_relat_1(X1) != iProver_top ),
% 3.37/1.06      inference(renaming,[status(thm)],[c_10181]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_10190,plain,
% 3.37/1.06      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 3.37/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_2375,c_10182]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_33,negated_conjecture,
% 3.37/1.06      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.37/1.06      inference(cnf_transformation,[],[f87]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_26,plain,
% 3.37/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.06      | ~ v2_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | k2_relset_1(X1,X2,X0) != X2
% 3.37/1.06      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 3.37/1.06      | o_0_0_xboole_0 = X2 ),
% 3.37/1.06      inference(cnf_transformation,[],[f104]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1265,plain,
% 3.37/1.06      ( k2_relset_1(X0,X1,X2) != X1
% 3.37/1.06      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 3.37/1.06      | o_0_0_xboole_0 = X1
% 3.37/1.06      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.37/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.37/1.06      | v2_funct_1(X2) != iProver_top
% 3.37/1.06      | v1_funct_1(X2) != iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3520,plain,
% 3.37/1.06      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.37/1.06      | sK1 = o_0_0_xboole_0
% 3.37/1.06      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.37/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.37/1.06      | v2_funct_1(sK2) != iProver_top
% 3.37/1.06      | v1_funct_1(sK2) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_33,c_1265]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_38,negated_conjecture,
% 3.37/1.06      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.37/1.06      inference(cnf_transformation,[],[f82]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_31,negated_conjecture,
% 3.37/1.06      ( v2_funct_1(sK2) ),
% 3.37/1.06      inference(cnf_transformation,[],[f89]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_29,negated_conjecture,
% 3.37/1.06      ( o_0_0_xboole_0 != sK1 ),
% 3.37/1.06      inference(cnf_transformation,[],[f106]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1333,plain,
% 3.37/1.06      ( ~ v1_funct_2(X0,X1,sK1)
% 3.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.37/1.06      | ~ v2_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | k2_relset_1(X1,sK1,X0) != sK1
% 3.37/1.06      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 3.37/1.06      | o_0_0_xboole_0 = sK1 ),
% 3.37/1.06      inference(instantiation,[status(thm)],[c_26]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1422,plain,
% 3.37/1.06      ( ~ v1_funct_2(sK2,X0,sK1)
% 3.37/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.37/1.06      | ~ v2_funct_1(sK2)
% 3.37/1.06      | ~ v1_funct_1(sK2)
% 3.37/1.06      | k2_relset_1(X0,sK1,sK2) != sK1
% 3.37/1.06      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.37/1.06      | o_0_0_xboole_0 = sK1 ),
% 3.37/1.06      inference(instantiation,[status(thm)],[c_1333]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1669,plain,
% 3.37/1.06      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.37/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.37/1.06      | ~ v2_funct_1(sK2)
% 3.37/1.06      | ~ v1_funct_1(sK2)
% 3.37/1.06      | k2_relset_1(sK0,sK1,sK2) != sK1
% 3.37/1.06      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 3.37/1.06      | o_0_0_xboole_0 = sK1 ),
% 3.37/1.06      inference(instantiation,[status(thm)],[c_1422]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_4332,plain,
% 3.37/1.06      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_3520,c_39,c_38,c_37,c_33,c_31,c_29,c_1669]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_10194,plain,
% 3.37/1.06      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 3.37/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.06      inference(light_normalisation,[status(thm)],[c_10190,c_4332]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_10219,plain,
% 3.37/1.06      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_2374,c_10194]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1263,plain,
% 3.37/1.06      ( v2_funct_1(sK2) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_9,plain,
% 3.37/1.06      ( ~ v2_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | ~ v1_relat_1(X0)
% 3.37/1.06      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.37/1.06      inference(cnf_transformation,[],[f62]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1279,plain,
% 3.37/1.06      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.37/1.06      | v2_funct_1(X0) != iProver_top
% 3.37/1.06      | v1_funct_1(X0) != iProver_top
% 3.37/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3548,plain,
% 3.37/1.06      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.37/1.06      | v1_funct_1(sK2) != iProver_top
% 3.37/1.06      | v1_relat_1(sK2) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_1263,c_1279]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_40,plain,
% 3.37/1.06      ( v1_funct_1(sK2) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_4828,plain,
% 3.37/1.06      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_3548,c_40,c_2375]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_12,plain,
% 3.37/1.06      ( ~ v2_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | ~ v1_relat_1(X0)
% 3.37/1.06      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 3.37/1.06      inference(cnf_transformation,[],[f63]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1276,plain,
% 3.37/1.06      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 3.37/1.06      | v2_funct_1(X0) != iProver_top
% 3.37/1.06      | v1_funct_1(X0) != iProver_top
% 3.37/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3578,plain,
% 3.37/1.06      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 3.37/1.06      | v1_funct_1(sK2) != iProver_top
% 3.37/1.06      | v1_relat_1(sK2) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_1263,c_1276]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_27,plain,
% 3.37/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.06      | ~ v2_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | k2_relset_1(X1,X2,X0) != X2
% 3.37/1.06      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.37/1.06      | o_0_0_xboole_0 = X2 ),
% 3.37/1.06      inference(cnf_transformation,[],[f105]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1264,plain,
% 3.37/1.06      ( k2_relset_1(X0,X1,X2) != X1
% 3.37/1.06      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 3.37/1.06      | o_0_0_xboole_0 = X1
% 3.37/1.06      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.37/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.37/1.06      | v2_funct_1(X2) != iProver_top
% 3.37/1.06      | v1_funct_1(X2) != iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3151,plain,
% 3.37/1.06      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.37/1.06      | sK1 = o_0_0_xboole_0
% 3.37/1.06      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.37/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.37/1.06      | v2_funct_1(sK2) != iProver_top
% 3.37/1.06      | v1_funct_1(sK2) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_33,c_1264]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1334,plain,
% 3.37/1.06      ( ~ v1_funct_2(X0,X1,sK1)
% 3.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 3.37/1.06      | ~ v2_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | k2_relset_1(X1,sK1,X0) != sK1
% 3.37/1.06      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.37/1.06      | o_0_0_xboole_0 = sK1 ),
% 3.37/1.06      inference(instantiation,[status(thm)],[c_27]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1448,plain,
% 3.37/1.06      ( ~ v1_funct_2(sK2,X0,sK1)
% 3.37/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 3.37/1.06      | ~ v2_funct_1(sK2)
% 3.37/1.06      | ~ v1_funct_1(sK2)
% 3.37/1.06      | k2_relset_1(X0,sK1,sK2) != sK1
% 3.37/1.06      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 3.37/1.06      | o_0_0_xboole_0 = sK1 ),
% 3.37/1.06      inference(instantiation,[status(thm)],[c_1334]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1684,plain,
% 3.37/1.06      ( ~ v1_funct_2(sK2,sK0,sK1)
% 3.37/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.37/1.06      | ~ v2_funct_1(sK2)
% 3.37/1.06      | ~ v1_funct_1(sK2)
% 3.37/1.06      | k2_relset_1(sK0,sK1,sK2) != sK1
% 3.37/1.06      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 3.37/1.06      | o_0_0_xboole_0 = sK1 ),
% 3.37/1.06      inference(instantiation,[status(thm)],[c_1448]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3279,plain,
% 3.37/1.06      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_3151,c_39,c_38,c_37,c_33,c_31,c_29,c_1684]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3579,plain,
% 3.37/1.06      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 3.37/1.06      | v1_funct_1(sK2) != iProver_top
% 3.37/1.06      | v1_relat_1(sK2) != iProver_top ),
% 3.37/1.06      inference(light_normalisation,[status(thm)],[c_3578,c_3279]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_2,plain,
% 3.37/1.06      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.37/1.06      inference(cnf_transformation,[],[f94]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3580,plain,
% 3.37/1.06      ( k1_relat_1(sK2) = sK0
% 3.37/1.06      | v1_funct_1(sK2) != iProver_top
% 3.37/1.06      | v1_relat_1(sK2) != iProver_top ),
% 3.37/1.06      inference(demodulation,[status(thm)],[c_3579,c_2]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3587,plain,
% 3.37/1.06      ( k1_relat_1(sK2) = sK0 ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_3580,c_40,c_2375]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_4830,plain,
% 3.37/1.06      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 3.37/1.06      inference(light_normalisation,[status(thm)],[c_4828,c_3587]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_4,plain,
% 3.37/1.06      ( ~ v1_relat_1(X0)
% 3.37/1.06      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 3.37/1.06      inference(cnf_transformation,[],[f96]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1284,plain,
% 3.37/1.06      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 3.37/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3199,plain,
% 3.37/1.06      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 3.37/1.06      | v1_funct_1(X0) != iProver_top
% 3.37/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_1282,c_1284]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3513,plain,
% 3.37/1.06      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 3.37/1.06      | v1_relat_1(sK2) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_1257,c_3199]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_4825,plain,
% 3.37/1.06      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2) ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_3513,c_2375]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_4831,plain,
% 3.37/1.06      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 3.37/1.06      inference(demodulation,[status(thm)],[c_4830,c_4825]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_16,plain,
% 3.37/1.06      ( ~ r2_relset_1(X0,X1,X2,X3)
% 3.37/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/1.06      | X3 = X2 ),
% 3.37/1.06      inference(cnf_transformation,[],[f67]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_32,negated_conjecture,
% 3.37/1.06      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 3.37/1.06      inference(cnf_transformation,[],[f88]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_422,plain,
% 3.37/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.06      | X3 = X0
% 3.37/1.06      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 3.37/1.06      | k6_partfun1(sK0) != X3
% 3.37/1.06      | sK0 != X2
% 3.37/1.06      | sK0 != X1 ),
% 3.37/1.06      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_423,plain,
% 3.37/1.06      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/1.06      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/1.06      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.37/1.06      inference(unflattening,[status(thm)],[c_422]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_17,plain,
% 3.37/1.06      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 3.37/1.06      inference(cnf_transformation,[],[f99]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_431,plain,
% 3.37/1.06      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/1.06      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.37/1.06      inference(forward_subsumption_resolution,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_423,c_17]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1255,plain,
% 3.37/1.06      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.37/1.06      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_36,negated_conjecture,
% 3.37/1.06      ( v1_funct_1(sK3) ),
% 3.37/1.06      inference(cnf_transformation,[],[f84]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_18,plain,
% 3.37/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.37/1.06      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X3) ),
% 3.37/1.06      inference(cnf_transformation,[],[f71]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1371,plain,
% 3.37/1.06      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 3.37/1.06      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.37/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.37/1.06      | ~ v1_funct_1(sK3)
% 3.37/1.06      | ~ v1_funct_1(sK2) ),
% 3.37/1.06      inference(instantiation,[status(thm)],[c_18]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_2135,plain,
% 3.37/1.06      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_1255,c_39,c_37,c_36,c_34,c_431,c_1371]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_23,plain,
% 3.37/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/1.06      | ~ v1_funct_2(X3,X4,X1)
% 3.37/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 3.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.06      | v2_funct_1(X0)
% 3.37/1.06      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X3)
% 3.37/1.06      | k2_relset_1(X4,X1,X3) != X1
% 3.37/1.06      | o_0_0_xboole_0 = X2 ),
% 3.37/1.06      inference(cnf_transformation,[],[f101]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1268,plain,
% 3.37/1.06      ( k2_relset_1(X0,X1,X2) != X1
% 3.37/1.06      | o_0_0_xboole_0 = X3
% 3.37/1.06      | v1_funct_2(X4,X1,X3) != iProver_top
% 3.37/1.06      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.37/1.06      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 3.37/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.37/1.06      | v2_funct_1(X4) = iProver_top
% 3.37/1.06      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 3.37/1.06      | v1_funct_1(X4) != iProver_top
% 3.37/1.06      | v1_funct_1(X2) != iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_5409,plain,
% 3.37/1.06      ( o_0_0_xboole_0 = X0
% 3.37/1.06      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.37/1.06      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.37/1.06      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.37/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.37/1.06      | v2_funct_1(X1) = iProver_top
% 3.37/1.06      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 3.37/1.06      | v1_funct_1(X1) != iProver_top
% 3.37/1.06      | v1_funct_1(sK2) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_33,c_1268]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_41,plain,
% 3.37/1.06      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_42,plain,
% 3.37/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_5462,plain,
% 3.37/1.06      ( v1_funct_1(X1) != iProver_top
% 3.37/1.06      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 3.37/1.06      | v2_funct_1(X1) = iProver_top
% 3.37/1.06      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.37/1.06      | o_0_0_xboole_0 = X0
% 3.37/1.06      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_5409,c_40,c_41,c_42]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_5463,plain,
% 3.37/1.06      ( o_0_0_xboole_0 = X0
% 3.37/1.06      | v1_funct_2(X1,sK1,X0) != iProver_top
% 3.37/1.06      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 3.37/1.06      | v2_funct_1(X1) = iProver_top
% 3.37/1.06      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 3.37/1.06      | v1_funct_1(X1) != iProver_top ),
% 3.37/1.06      inference(renaming,[status(thm)],[c_5462]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_5466,plain,
% 3.37/1.06      ( sK0 = o_0_0_xboole_0
% 3.37/1.06      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.37/1.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.37/1.06      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 3.37/1.06      | v2_funct_1(sK3) = iProver_top
% 3.37/1.06      | v1_funct_1(sK3) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_2135,c_5463]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_43,plain,
% 3.37/1.06      ( v1_funct_1(sK3) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_35,negated_conjecture,
% 3.37/1.06      ( v1_funct_2(sK3,sK1,sK0) ),
% 3.37/1.06      inference(cnf_transformation,[],[f85]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_44,plain,
% 3.37/1.06      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_45,plain,
% 3.37/1.06      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_30,negated_conjecture,
% 3.37/1.06      ( o_0_0_xboole_0 != sK0 ),
% 3.37/1.06      inference(cnf_transformation,[],[f107]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_714,plain,( X0 = X0 ),theory(equality) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_745,plain,
% 3.37/1.06      ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
% 3.37/1.06      inference(instantiation,[status(thm)],[c_714]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_715,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1369,plain,
% 3.37/1.06      ( sK0 != X0 | o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK0 ),
% 3.37/1.06      inference(instantiation,[status(thm)],[c_715]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1370,plain,
% 3.37/1.06      ( sK0 != o_0_0_xboole_0
% 3.37/1.06      | o_0_0_xboole_0 = sK0
% 3.37/1.06      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 3.37/1.06      inference(instantiation,[status(thm)],[c_1369]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_7,plain,
% 3.37/1.06      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.37/1.06      inference(cnf_transformation,[],[f97]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3055,plain,
% 3.37/1.06      ( v2_funct_1(k6_partfun1(sK0)) ),
% 3.37/1.06      inference(instantiation,[status(thm)],[c_7]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3056,plain,
% 3.37/1.06      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_3055]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_6570,plain,
% 3.37/1.06      ( v2_funct_1(sK3) = iProver_top ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_5466,c_43,c_44,c_45,c_30,c_745,c_1370,c_3056]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_6575,plain,
% 3.37/1.06      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 3.37/1.06      | v1_funct_1(sK3) != iProver_top
% 3.37/1.06      | v1_relat_1(sK3) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_6570,c_1276]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_21,plain,
% 3.37/1.06      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 3.37/1.06      | ~ v1_funct_2(X2,X0,X1)
% 3.37/1.06      | ~ v1_funct_2(X3,X1,X0)
% 3.37/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.37/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.37/1.06      | ~ v1_funct_1(X2)
% 3.37/1.06      | ~ v1_funct_1(X3)
% 3.37/1.06      | k2_relset_1(X1,X0,X3) = X0 ),
% 3.37/1.06      inference(cnf_transformation,[],[f74]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_435,plain,
% 3.37/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 3.37/1.06      | ~ v1_funct_2(X3,X2,X1)
% 3.37/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X3)
% 3.37/1.06      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.37/1.06      | k2_relset_1(X1,X2,X0) = X2
% 3.37/1.06      | k6_partfun1(X2) != k6_partfun1(sK0)
% 3.37/1.06      | sK0 != X2 ),
% 3.37/1.06      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_436,plain,
% 3.37/1.06      ( ~ v1_funct_2(X0,X1,sK0)
% 3.37/1.06      | ~ v1_funct_2(X2,sK0,X1)
% 3.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.37/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X2)
% 3.37/1.06      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.37/1.06      | k2_relset_1(X1,sK0,X0) = sK0
% 3.37/1.06      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 3.37/1.06      inference(unflattening,[status(thm)],[c_435]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_523,plain,
% 3.37/1.06      ( ~ v1_funct_2(X0,X1,sK0)
% 3.37/1.06      | ~ v1_funct_2(X2,sK0,X1)
% 3.37/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 3.37/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X2)
% 3.37/1.06      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.37/1.06      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 3.37/1.06      inference(equality_resolution_simp,[status(thm)],[c_436]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1254,plain,
% 3.37/1.06      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 3.37/1.06      | k2_relset_1(X0,sK0,X2) = sK0
% 3.37/1.06      | v1_funct_2(X2,X0,sK0) != iProver_top
% 3.37/1.06      | v1_funct_2(X1,sK0,X0) != iProver_top
% 3.37/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 3.37/1.06      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 3.37/1.06      | v1_funct_1(X2) != iProver_top
% 3.37/1.06      | v1_funct_1(X1) != iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1807,plain,
% 3.37/1.06      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 3.37/1.06      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.37/1.06      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 3.37/1.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.37/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.37/1.06      | v1_funct_1(sK3) != iProver_top
% 3.37/1.06      | v1_funct_1(sK2) != iProver_top ),
% 3.37/1.06      inference(equality_resolution,[status(thm)],[c_1254]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_2142,plain,
% 3.37/1.06      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_1807,c_40,c_41,c_42,c_43,c_44,c_45]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3152,plain,
% 3.37/1.06      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 3.37/1.06      | sK0 = o_0_0_xboole_0
% 3.37/1.06      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 3.37/1.06      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.37/1.06      | v2_funct_1(sK3) != iProver_top
% 3.37/1.06      | v1_funct_1(sK3) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_2142,c_1264]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3322,plain,
% 3.37/1.06      ( v2_funct_1(sK3) != iProver_top
% 3.37/1.06      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_3152,c_43,c_44,c_45,c_30,c_745,c_1370]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3323,plain,
% 3.37/1.06      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 3.37/1.06      | v2_funct_1(sK3) != iProver_top ),
% 3.37/1.06      inference(renaming,[status(thm)],[c_3322]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_6579,plain,
% 3.37/1.06      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_6570,c_3323]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_6581,plain,
% 3.37/1.06      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
% 3.37/1.06      | v1_funct_1(sK3) != iProver_top
% 3.37/1.06      | v1_relat_1(sK3) != iProver_top ),
% 3.37/1.06      inference(demodulation,[status(thm)],[c_6575,c_6579]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_6582,plain,
% 3.37/1.06      ( k1_relat_1(sK3) = sK1
% 3.37/1.06      | v1_funct_1(sK3) != iProver_top
% 3.37/1.06      | v1_relat_1(sK3) != iProver_top ),
% 3.37/1.06      inference(demodulation,[status(thm)],[c_6581,c_2]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_6677,plain,
% 3.37/1.06      ( k1_relat_1(sK3) = sK1 ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_6582,c_43,c_2374]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_3,plain,
% 3.37/1.06      ( ~ v1_relat_1(X0)
% 3.37/1.06      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 3.37/1.06      inference(cnf_transformation,[],[f95]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1285,plain,
% 3.37/1.06      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 3.37/1.06      | v1_relat_1(X0) != iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_2605,plain,
% 3.37/1.06      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_2374,c_1285]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_6679,plain,
% 3.37/1.06      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 3.37/1.06      inference(demodulation,[status(thm)],[c_6677,c_2605]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_20,plain,
% 3.37/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.37/1.06      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 3.37/1.06      | ~ v1_funct_1(X0)
% 3.37/1.06      | ~ v1_funct_1(X3)
% 3.37/1.06      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 3.37/1.06      inference(cnf_transformation,[],[f72]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_1270,plain,
% 3.37/1.06      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 3.37/1.06      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 3.37/1.06      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.37/1.06      | v1_funct_1(X5) != iProver_top
% 3.37/1.06      | v1_funct_1(X4) != iProver_top ),
% 3.37/1.06      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_5348,plain,
% 3.37/1.06      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.37/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.37/1.06      | v1_funct_1(X2) != iProver_top
% 3.37/1.06      | v1_funct_1(sK3) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_1262,c_1270]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_5469,plain,
% 3.37/1.06      ( v1_funct_1(X2) != iProver_top
% 3.37/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.37/1.06      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_5348,c_43]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_5470,plain,
% 3.37/1.06      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 3.37/1.06      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.37/1.06      | v1_funct_1(X2) != iProver_top ),
% 3.37/1.06      inference(renaming,[status(thm)],[c_5469]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_5478,plain,
% 3.37/1.06      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 3.37/1.06      | v1_funct_1(sK2) != iProver_top ),
% 3.37/1.06      inference(superposition,[status(thm)],[c_1259,c_5470]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_5479,plain,
% 3.37/1.06      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 3.37/1.06      | v1_funct_1(sK2) != iProver_top ),
% 3.37/1.06      inference(light_normalisation,[status(thm)],[c_5478,c_2135]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_6766,plain,
% 3.37/1.06      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 3.37/1.06      inference(global_propositional_subsumption,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_5479,c_40]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_10226,plain,
% 3.37/1.06      ( k2_funct_1(sK2) = sK3 ),
% 3.37/1.06      inference(light_normalisation,
% 3.37/1.06                [status(thm)],
% 3.37/1.06                [c_10219,c_4831,c_6679,c_6766]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(c_28,negated_conjecture,
% 3.37/1.06      ( k2_funct_1(sK2) != sK3 ),
% 3.37/1.06      inference(cnf_transformation,[],[f92]) ).
% 3.37/1.06  
% 3.37/1.06  cnf(contradiction,plain,
% 3.37/1.06      ( $false ),
% 3.37/1.06      inference(minisat,[status(thm)],[c_10226,c_28]) ).
% 3.37/1.06  
% 3.37/1.06  
% 3.37/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 3.37/1.06  
% 3.37/1.06  ------                               Statistics
% 3.37/1.06  
% 3.37/1.06  ------ General
% 3.37/1.06  
% 3.37/1.06  abstr_ref_over_cycles:                  0
% 3.37/1.06  abstr_ref_under_cycles:                 0
% 3.37/1.06  gc_basic_clause_elim:                   0
% 3.37/1.06  forced_gc_time:                         0
% 3.37/1.06  parsing_time:                           0.013
% 3.37/1.06  unif_index_cands_time:                  0.
% 3.37/1.06  unif_index_add_time:                    0.
% 3.37/1.06  orderings_time:                         0.
% 3.37/1.06  out_proof_time:                         0.015
% 3.37/1.06  total_time:                             0.482
% 3.37/1.06  num_of_symbols:                         51
% 3.37/1.06  num_of_terms:                           16225
% 3.37/1.06  
% 3.37/1.06  ------ Preprocessing
% 3.37/1.06  
% 3.37/1.06  num_of_splits:                          0
% 3.37/1.06  num_of_split_atoms:                     0
% 3.37/1.06  num_of_reused_defs:                     0
% 3.37/1.06  num_eq_ax_congr_red:                    0
% 3.37/1.06  num_of_sem_filtered_clauses:            1
% 3.37/1.06  num_of_subtypes:                        0
% 3.37/1.06  monotx_restored_types:                  0
% 3.37/1.06  sat_num_of_epr_types:                   0
% 3.37/1.06  sat_num_of_non_cyclic_types:            0
% 3.37/1.06  sat_guarded_non_collapsed_types:        0
% 3.37/1.06  num_pure_diseq_elim:                    0
% 3.37/1.06  simp_replaced_by:                       0
% 3.37/1.06  res_preprocessed:                       190
% 3.37/1.06  prep_upred:                             0
% 3.37/1.06  prep_unflattend:                        12
% 3.37/1.06  smt_new_axioms:                         0
% 3.37/1.06  pred_elim_cands:                        5
% 3.37/1.06  pred_elim:                              1
% 3.37/1.06  pred_elim_cl:                           1
% 3.37/1.06  pred_elim_cycles:                       3
% 3.37/1.06  merged_defs:                            0
% 3.37/1.06  merged_defs_ncl:                        0
% 3.37/1.06  bin_hyper_res:                          0
% 3.37/1.06  prep_cycles:                            4
% 3.37/1.06  pred_elim_time:                         0.007
% 3.37/1.06  splitting_time:                         0.
% 3.37/1.06  sem_filter_time:                        0.
% 3.37/1.06  monotx_time:                            0.001
% 3.37/1.06  subtype_inf_time:                       0.
% 3.37/1.06  
% 3.37/1.06  ------ Problem properties
% 3.37/1.06  
% 3.37/1.06  clauses:                                39
% 3.37/1.06  conjectures:                            11
% 3.37/1.06  epr:                                    7
% 3.37/1.06  horn:                                   35
% 3.37/1.06  ground:                                 12
% 3.37/1.06  unary:                                  16
% 3.37/1.06  binary:                                 5
% 3.37/1.06  lits:                                   135
% 3.37/1.06  lits_eq:                                32
% 3.37/1.06  fd_pure:                                0
% 3.37/1.06  fd_pseudo:                              0
% 3.37/1.06  fd_cond:                                4
% 3.37/1.06  fd_pseudo_cond:                         0
% 3.37/1.06  ac_symbols:                             0
% 3.37/1.06  
% 3.37/1.06  ------ Propositional Solver
% 3.37/1.06  
% 3.37/1.06  prop_solver_calls:                      29
% 3.37/1.06  prop_fast_solver_calls:                 1816
% 3.37/1.06  smt_solver_calls:                       0
% 3.37/1.06  smt_fast_solver_calls:                  0
% 3.37/1.06  prop_num_of_clauses:                    5418
% 3.37/1.06  prop_preprocess_simplified:             13740
% 3.37/1.06  prop_fo_subsumed:                       116
% 3.37/1.06  prop_solver_time:                       0.
% 3.37/1.06  smt_solver_time:                        0.
% 3.37/1.06  smt_fast_solver_time:                   0.
% 3.37/1.06  prop_fast_solver_time:                  0.
% 3.37/1.06  prop_unsat_core_time:                   0.
% 3.37/1.06  
% 3.37/1.06  ------ QBF
% 3.37/1.06  
% 3.37/1.06  qbf_q_res:                              0
% 3.37/1.06  qbf_num_tautologies:                    0
% 3.37/1.06  qbf_prep_cycles:                        0
% 3.37/1.06  
% 3.37/1.06  ------ BMC1
% 3.37/1.06  
% 3.37/1.06  bmc1_current_bound:                     -1
% 3.37/1.06  bmc1_last_solved_bound:                 -1
% 3.37/1.06  bmc1_unsat_core_size:                   -1
% 3.37/1.06  bmc1_unsat_core_parents_size:           -1
% 3.37/1.06  bmc1_merge_next_fun:                    0
% 3.37/1.06  bmc1_unsat_core_clauses_time:           0.
% 3.37/1.06  
% 3.37/1.06  ------ Instantiation
% 3.37/1.06  
% 3.37/1.06  inst_num_of_clauses:                    1297
% 3.37/1.06  inst_num_in_passive:                    466
% 3.37/1.06  inst_num_in_active:                     717
% 3.37/1.06  inst_num_in_unprocessed:                114
% 3.37/1.06  inst_num_of_loops:                      790
% 3.37/1.06  inst_num_of_learning_restarts:          0
% 3.37/1.06  inst_num_moves_active_passive:          72
% 3.37/1.06  inst_lit_activity:                      0
% 3.37/1.06  inst_lit_activity_moves:                1
% 3.37/1.06  inst_num_tautologies:                   0
% 3.37/1.06  inst_num_prop_implied:                  0
% 3.37/1.06  inst_num_existing_simplified:           0
% 3.37/1.06  inst_num_eq_res_simplified:             0
% 3.37/1.06  inst_num_child_elim:                    0
% 3.37/1.06  inst_num_of_dismatching_blockings:      145
% 3.37/1.06  inst_num_of_non_proper_insts:           1140
% 3.37/1.06  inst_num_of_duplicates:                 0
% 3.37/1.06  inst_inst_num_from_inst_to_res:         0
% 3.37/1.06  inst_dismatching_checking_time:         0.
% 3.37/1.06  
% 3.37/1.06  ------ Resolution
% 3.37/1.06  
% 3.37/1.06  res_num_of_clauses:                     0
% 3.37/1.06  res_num_in_passive:                     0
% 3.37/1.06  res_num_in_active:                      0
% 3.37/1.06  res_num_of_loops:                       194
% 3.37/1.06  res_forward_subset_subsumed:            56
% 3.37/1.06  res_backward_subset_subsumed:           0
% 3.37/1.06  res_forward_subsumed:                   0
% 3.37/1.06  res_backward_subsumed:                  0
% 3.37/1.06  res_forward_subsumption_resolution:     2
% 3.37/1.06  res_backward_subsumption_resolution:    0
% 3.37/1.06  res_clause_to_clause_subsumption:       545
% 3.37/1.06  res_orphan_elimination:                 0
% 3.37/1.06  res_tautology_del:                      20
% 3.37/1.06  res_num_eq_res_simplified:              1
% 3.37/1.06  res_num_sel_changes:                    0
% 3.37/1.06  res_moves_from_active_to_pass:          0
% 3.37/1.06  
% 3.37/1.06  ------ Superposition
% 3.37/1.06  
% 3.37/1.06  sup_time_total:                         0.
% 3.37/1.06  sup_time_generating:                    0.
% 3.37/1.06  sup_time_sim_full:                      0.
% 3.37/1.06  sup_time_sim_immed:                     0.
% 3.37/1.06  
% 3.37/1.06  sup_num_of_clauses:                     266
% 3.37/1.06  sup_num_in_active:                      148
% 3.37/1.06  sup_num_in_passive:                     118
% 3.37/1.06  sup_num_of_loops:                       157
% 3.37/1.06  sup_fw_superposition:                   156
% 3.37/1.06  sup_bw_superposition:                   110
% 3.37/1.06  sup_immediate_simplified:               61
% 3.37/1.06  sup_given_eliminated:                   1
% 3.37/1.06  comparisons_done:                       0
% 3.37/1.06  comparisons_avoided:                    4
% 3.37/1.06  
% 3.37/1.06  ------ Simplifications
% 3.37/1.06  
% 3.37/1.06  
% 3.37/1.06  sim_fw_subset_subsumed:                 4
% 3.37/1.06  sim_bw_subset_subsumed:                 12
% 3.37/1.06  sim_fw_subsumed:                        5
% 3.37/1.06  sim_bw_subsumed:                        0
% 3.37/1.06  sim_fw_subsumption_res:                 0
% 3.37/1.06  sim_bw_subsumption_res:                 0
% 3.37/1.06  sim_tautology_del:                      2
% 3.37/1.06  sim_eq_tautology_del:                   4
% 3.37/1.06  sim_eq_res_simp:                        0
% 3.37/1.06  sim_fw_demodulated:                     6
% 3.37/1.06  sim_bw_demodulated:                     10
% 3.37/1.06  sim_light_normalised:                   54
% 3.37/1.06  sim_joinable_taut:                      0
% 3.37/1.06  sim_joinable_simp:                      0
% 3.37/1.06  sim_ac_normalised:                      0
% 3.37/1.06  sim_smt_subsumption:                    0
% 3.37/1.06  
%------------------------------------------------------------------------------
