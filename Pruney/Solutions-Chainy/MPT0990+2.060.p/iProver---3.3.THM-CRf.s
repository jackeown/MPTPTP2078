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
% DateTime   : Thu Dec  3 12:03:09 EST 2020

% Result     : Theorem 7.60s
% Output     : CNFRefutation 7.60s
% Verified   : 
% Statistics : Number of formulae       :  211 (1144 expanded)
%              Number of clauses        :  122 ( 301 expanded)
%              Number of leaves         :   23 ( 305 expanded)
%              Depth                    :   22
%              Number of atoms          :  810 (9680 expanded)
%              Number of equality atoms :  397 (3560 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f21])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f50,plain,(
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

fof(f49,plain,
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

fof(f51,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f50,f49])).

fof(f87,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

fof(f82,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f51])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
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
    inference(definition_unfolding,[],[f81,f52])).

fof(f83,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f90,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f92,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,(
    o_0_0_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f92,f52])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | o_0_0_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_unfolding,[],[f80,f52])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f54,f74])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f57,f74])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f34])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f89,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f51])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f72,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f85,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f37])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f18])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f43])).

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
    inference(definition_unfolding,[],[f78,f52])).

fof(f86,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f91,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f51])).

fof(f107,plain,(
    o_0_0_xboole_0 != sK0 ),
    inference(definition_unfolding,[],[f91,f52])).

fof(f7,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f98,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f61,f74])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f17])).

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
    inference(flattening,[],[f40])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f56,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f96,plain,(
    ! [X0] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f56,f74])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f38])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f93,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1262,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1275,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2374,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1275])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1259,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2375,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1259,c_1275])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1257,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

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
    inference(cnf_transformation,[],[f53])).

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
    inference(cnf_transformation,[],[f88])).

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
    inference(cnf_transformation,[],[f83])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f90])).

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
    inference(cnf_transformation,[],[f63])).

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
    inference(cnf_transformation,[],[f64])).

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
    inference(cnf_transformation,[],[f95])).

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
    inference(cnf_transformation,[],[f97])).

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
    inference(cnf_transformation,[],[f68])).

cnf(c_32,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f89])).

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

cnf(c_19,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_431,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_423,c_19])).

cnf(c_1255,plain,
    ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_17,plain,
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
    inference(instantiation,[status(thm)],[c_17])).

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
    inference(cnf_transformation,[],[f86])).

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
    inference(cnf_transformation,[],[f98])).

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
    inference(cnf_transformation,[],[f75])).

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
    inference(cnf_transformation,[],[f96])).

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
    inference(cnf_transformation,[],[f73])).

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
    inference(cnf_transformation,[],[f93])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10226,c_28])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:12:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.60/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.60/1.48  
% 7.60/1.48  ------  iProver source info
% 7.60/1.48  
% 7.60/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.60/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.60/1.48  git: non_committed_changes: false
% 7.60/1.48  git: last_make_outside_of_git: false
% 7.60/1.48  
% 7.60/1.48  ------ 
% 7.60/1.48  
% 7.60/1.48  ------ Input Options
% 7.60/1.48  
% 7.60/1.48  --out_options                           all
% 7.60/1.48  --tptp_safe_out                         true
% 7.60/1.48  --problem_path                          ""
% 7.60/1.48  --include_path                          ""
% 7.60/1.48  --clausifier                            res/vclausify_rel
% 7.60/1.48  --clausifier_options                    ""
% 7.60/1.48  --stdin                                 false
% 7.60/1.48  --stats_out                             all
% 7.60/1.48  
% 7.60/1.48  ------ General Options
% 7.60/1.48  
% 7.60/1.48  --fof                                   false
% 7.60/1.48  --time_out_real                         305.
% 7.60/1.48  --time_out_virtual                      -1.
% 7.60/1.48  --symbol_type_check                     false
% 7.60/1.48  --clausify_out                          false
% 7.60/1.48  --sig_cnt_out                           false
% 7.60/1.48  --trig_cnt_out                          false
% 7.60/1.48  --trig_cnt_out_tolerance                1.
% 7.60/1.48  --trig_cnt_out_sk_spl                   false
% 7.60/1.48  --abstr_cl_out                          false
% 7.60/1.48  
% 7.60/1.48  ------ Global Options
% 7.60/1.48  
% 7.60/1.48  --schedule                              default
% 7.60/1.48  --add_important_lit                     false
% 7.60/1.48  --prop_solver_per_cl                    1000
% 7.60/1.48  --min_unsat_core                        false
% 7.60/1.48  --soft_assumptions                      false
% 7.60/1.48  --soft_lemma_size                       3
% 7.60/1.48  --prop_impl_unit_size                   0
% 7.60/1.48  --prop_impl_unit                        []
% 7.60/1.48  --share_sel_clauses                     true
% 7.60/1.48  --reset_solvers                         false
% 7.60/1.48  --bc_imp_inh                            [conj_cone]
% 7.60/1.48  --conj_cone_tolerance                   3.
% 7.60/1.48  --extra_neg_conj                        none
% 7.60/1.48  --large_theory_mode                     true
% 7.60/1.48  --prolific_symb_bound                   200
% 7.60/1.48  --lt_threshold                          2000
% 7.60/1.48  --clause_weak_htbl                      true
% 7.60/1.48  --gc_record_bc_elim                     false
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing Options
% 7.60/1.48  
% 7.60/1.48  --preprocessing_flag                    true
% 7.60/1.48  --time_out_prep_mult                    0.1
% 7.60/1.48  --splitting_mode                        input
% 7.60/1.48  --splitting_grd                         true
% 7.60/1.48  --splitting_cvd                         false
% 7.60/1.48  --splitting_cvd_svl                     false
% 7.60/1.48  --splitting_nvd                         32
% 7.60/1.48  --sub_typing                            true
% 7.60/1.48  --prep_gs_sim                           true
% 7.60/1.48  --prep_unflatten                        true
% 7.60/1.48  --prep_res_sim                          true
% 7.60/1.48  --prep_upred                            true
% 7.60/1.48  --prep_sem_filter                       exhaustive
% 7.60/1.48  --prep_sem_filter_out                   false
% 7.60/1.48  --pred_elim                             true
% 7.60/1.48  --res_sim_input                         true
% 7.60/1.48  --eq_ax_congr_red                       true
% 7.60/1.48  --pure_diseq_elim                       true
% 7.60/1.48  --brand_transform                       false
% 7.60/1.48  --non_eq_to_eq                          false
% 7.60/1.48  --prep_def_merge                        true
% 7.60/1.48  --prep_def_merge_prop_impl              false
% 7.60/1.48  --prep_def_merge_mbd                    true
% 7.60/1.48  --prep_def_merge_tr_red                 false
% 7.60/1.48  --prep_def_merge_tr_cl                  false
% 7.60/1.48  --smt_preprocessing                     true
% 7.60/1.48  --smt_ac_axioms                         fast
% 7.60/1.48  --preprocessed_out                      false
% 7.60/1.48  --preprocessed_stats                    false
% 7.60/1.48  
% 7.60/1.48  ------ Abstraction refinement Options
% 7.60/1.48  
% 7.60/1.48  --abstr_ref                             []
% 7.60/1.48  --abstr_ref_prep                        false
% 7.60/1.48  --abstr_ref_until_sat                   false
% 7.60/1.48  --abstr_ref_sig_restrict                funpre
% 7.60/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.60/1.48  --abstr_ref_under                       []
% 7.60/1.48  
% 7.60/1.48  ------ SAT Options
% 7.60/1.48  
% 7.60/1.48  --sat_mode                              false
% 7.60/1.48  --sat_fm_restart_options                ""
% 7.60/1.48  --sat_gr_def                            false
% 7.60/1.48  --sat_epr_types                         true
% 7.60/1.48  --sat_non_cyclic_types                  false
% 7.60/1.48  --sat_finite_models                     false
% 7.60/1.48  --sat_fm_lemmas                         false
% 7.60/1.48  --sat_fm_prep                           false
% 7.60/1.48  --sat_fm_uc_incr                        true
% 7.60/1.48  --sat_out_model                         small
% 7.60/1.48  --sat_out_clauses                       false
% 7.60/1.48  
% 7.60/1.48  ------ QBF Options
% 7.60/1.48  
% 7.60/1.48  --qbf_mode                              false
% 7.60/1.48  --qbf_elim_univ                         false
% 7.60/1.48  --qbf_dom_inst                          none
% 7.60/1.48  --qbf_dom_pre_inst                      false
% 7.60/1.48  --qbf_sk_in                             false
% 7.60/1.48  --qbf_pred_elim                         true
% 7.60/1.48  --qbf_split                             512
% 7.60/1.48  
% 7.60/1.48  ------ BMC1 Options
% 7.60/1.48  
% 7.60/1.48  --bmc1_incremental                      false
% 7.60/1.48  --bmc1_axioms                           reachable_all
% 7.60/1.48  --bmc1_min_bound                        0
% 7.60/1.48  --bmc1_max_bound                        -1
% 7.60/1.48  --bmc1_max_bound_default                -1
% 7.60/1.48  --bmc1_symbol_reachability              true
% 7.60/1.48  --bmc1_property_lemmas                  false
% 7.60/1.48  --bmc1_k_induction                      false
% 7.60/1.48  --bmc1_non_equiv_states                 false
% 7.60/1.48  --bmc1_deadlock                         false
% 7.60/1.48  --bmc1_ucm                              false
% 7.60/1.48  --bmc1_add_unsat_core                   none
% 7.60/1.48  --bmc1_unsat_core_children              false
% 7.60/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.60/1.48  --bmc1_out_stat                         full
% 7.60/1.48  --bmc1_ground_init                      false
% 7.60/1.48  --bmc1_pre_inst_next_state              false
% 7.60/1.48  --bmc1_pre_inst_state                   false
% 7.60/1.48  --bmc1_pre_inst_reach_state             false
% 7.60/1.48  --bmc1_out_unsat_core                   false
% 7.60/1.48  --bmc1_aig_witness_out                  false
% 7.60/1.48  --bmc1_verbose                          false
% 7.60/1.48  --bmc1_dump_clauses_tptp                false
% 7.60/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.60/1.48  --bmc1_dump_file                        -
% 7.60/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.60/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.60/1.48  --bmc1_ucm_extend_mode                  1
% 7.60/1.48  --bmc1_ucm_init_mode                    2
% 7.60/1.48  --bmc1_ucm_cone_mode                    none
% 7.60/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.60/1.48  --bmc1_ucm_relax_model                  4
% 7.60/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.60/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.60/1.48  --bmc1_ucm_layered_model                none
% 7.60/1.48  --bmc1_ucm_max_lemma_size               10
% 7.60/1.48  
% 7.60/1.48  ------ AIG Options
% 7.60/1.48  
% 7.60/1.48  --aig_mode                              false
% 7.60/1.48  
% 7.60/1.48  ------ Instantiation Options
% 7.60/1.48  
% 7.60/1.48  --instantiation_flag                    true
% 7.60/1.48  --inst_sos_flag                         true
% 7.60/1.48  --inst_sos_phase                        true
% 7.60/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.60/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.60/1.48  --inst_lit_sel_side                     num_symb
% 7.60/1.48  --inst_solver_per_active                1400
% 7.60/1.48  --inst_solver_calls_frac                1.
% 7.60/1.48  --inst_passive_queue_type               priority_queues
% 7.60/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.60/1.48  --inst_passive_queues_freq              [25;2]
% 7.60/1.48  --inst_dismatching                      true
% 7.60/1.48  --inst_eager_unprocessed_to_passive     true
% 7.60/1.48  --inst_prop_sim_given                   true
% 7.60/1.48  --inst_prop_sim_new                     false
% 7.60/1.48  --inst_subs_new                         false
% 7.60/1.48  --inst_eq_res_simp                      false
% 7.60/1.48  --inst_subs_given                       false
% 7.60/1.48  --inst_orphan_elimination               true
% 7.60/1.48  --inst_learning_loop_flag               true
% 7.60/1.48  --inst_learning_start                   3000
% 7.60/1.48  --inst_learning_factor                  2
% 7.60/1.48  --inst_start_prop_sim_after_learn       3
% 7.60/1.48  --inst_sel_renew                        solver
% 7.60/1.48  --inst_lit_activity_flag                true
% 7.60/1.48  --inst_restr_to_given                   false
% 7.60/1.48  --inst_activity_threshold               500
% 7.60/1.48  --inst_out_proof                        true
% 7.60/1.48  
% 7.60/1.48  ------ Resolution Options
% 7.60/1.48  
% 7.60/1.48  --resolution_flag                       true
% 7.60/1.48  --res_lit_sel                           adaptive
% 7.60/1.48  --res_lit_sel_side                      none
% 7.60/1.48  --res_ordering                          kbo
% 7.60/1.48  --res_to_prop_solver                    active
% 7.60/1.48  --res_prop_simpl_new                    false
% 7.60/1.48  --res_prop_simpl_given                  true
% 7.60/1.48  --res_passive_queue_type                priority_queues
% 7.60/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.60/1.48  --res_passive_queues_freq               [15;5]
% 7.60/1.48  --res_forward_subs                      full
% 7.60/1.48  --res_backward_subs                     full
% 7.60/1.48  --res_forward_subs_resolution           true
% 7.60/1.48  --res_backward_subs_resolution          true
% 7.60/1.48  --res_orphan_elimination                true
% 7.60/1.48  --res_time_limit                        2.
% 7.60/1.48  --res_out_proof                         true
% 7.60/1.48  
% 7.60/1.48  ------ Superposition Options
% 7.60/1.48  
% 7.60/1.48  --superposition_flag                    true
% 7.60/1.48  --sup_passive_queue_type                priority_queues
% 7.60/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.60/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.60/1.48  --demod_completeness_check              fast
% 7.60/1.48  --demod_use_ground                      true
% 7.60/1.48  --sup_to_prop_solver                    passive
% 7.60/1.48  --sup_prop_simpl_new                    true
% 7.60/1.48  --sup_prop_simpl_given                  true
% 7.60/1.48  --sup_fun_splitting                     true
% 7.60/1.48  --sup_smt_interval                      50000
% 7.60/1.48  
% 7.60/1.48  ------ Superposition Simplification Setup
% 7.60/1.48  
% 7.60/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.60/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.60/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.60/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.60/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.60/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.60/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.60/1.48  --sup_immed_triv                        [TrivRules]
% 7.60/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.48  --sup_immed_bw_main                     []
% 7.60/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.60/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.60/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.48  --sup_input_bw                          []
% 7.60/1.48  
% 7.60/1.48  ------ Combination Options
% 7.60/1.48  
% 7.60/1.48  --comb_res_mult                         3
% 7.60/1.48  --comb_sup_mult                         2
% 7.60/1.48  --comb_inst_mult                        10
% 7.60/1.48  
% 7.60/1.48  ------ Debug Options
% 7.60/1.48  
% 7.60/1.48  --dbg_backtrace                         false
% 7.60/1.48  --dbg_dump_prop_clauses                 false
% 7.60/1.48  --dbg_dump_prop_clauses_file            -
% 7.60/1.48  --dbg_out_stat                          false
% 7.60/1.48  ------ Parsing...
% 7.60/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.60/1.48  ------ Proving...
% 7.60/1.48  ------ Problem Properties 
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  clauses                                 39
% 7.60/1.48  conjectures                             11
% 7.60/1.48  EPR                                     7
% 7.60/1.48  Horn                                    35
% 7.60/1.48  unary                                   16
% 7.60/1.48  binary                                  5
% 7.60/1.48  lits                                    135
% 7.60/1.48  lits eq                                 32
% 7.60/1.48  fd_pure                                 0
% 7.60/1.48  fd_pseudo                               0
% 7.60/1.48  fd_cond                                 4
% 7.60/1.48  fd_pseudo_cond                          0
% 7.60/1.48  AC symbols                              0
% 7.60/1.48  
% 7.60/1.48  ------ Schedule dynamic 5 is on 
% 7.60/1.48  
% 7.60/1.48  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ 
% 7.60/1.48  Current options:
% 7.60/1.48  ------ 
% 7.60/1.48  
% 7.60/1.48  ------ Input Options
% 7.60/1.48  
% 7.60/1.48  --out_options                           all
% 7.60/1.48  --tptp_safe_out                         true
% 7.60/1.48  --problem_path                          ""
% 7.60/1.48  --include_path                          ""
% 7.60/1.48  --clausifier                            res/vclausify_rel
% 7.60/1.48  --clausifier_options                    ""
% 7.60/1.48  --stdin                                 false
% 7.60/1.48  --stats_out                             all
% 7.60/1.48  
% 7.60/1.48  ------ General Options
% 7.60/1.48  
% 7.60/1.48  --fof                                   false
% 7.60/1.48  --time_out_real                         305.
% 7.60/1.48  --time_out_virtual                      -1.
% 7.60/1.48  --symbol_type_check                     false
% 7.60/1.48  --clausify_out                          false
% 7.60/1.48  --sig_cnt_out                           false
% 7.60/1.48  --trig_cnt_out                          false
% 7.60/1.48  --trig_cnt_out_tolerance                1.
% 7.60/1.48  --trig_cnt_out_sk_spl                   false
% 7.60/1.48  --abstr_cl_out                          false
% 7.60/1.48  
% 7.60/1.48  ------ Global Options
% 7.60/1.48  
% 7.60/1.48  --schedule                              default
% 7.60/1.48  --add_important_lit                     false
% 7.60/1.48  --prop_solver_per_cl                    1000
% 7.60/1.48  --min_unsat_core                        false
% 7.60/1.48  --soft_assumptions                      false
% 7.60/1.48  --soft_lemma_size                       3
% 7.60/1.48  --prop_impl_unit_size                   0
% 7.60/1.48  --prop_impl_unit                        []
% 7.60/1.48  --share_sel_clauses                     true
% 7.60/1.48  --reset_solvers                         false
% 7.60/1.48  --bc_imp_inh                            [conj_cone]
% 7.60/1.48  --conj_cone_tolerance                   3.
% 7.60/1.48  --extra_neg_conj                        none
% 7.60/1.48  --large_theory_mode                     true
% 7.60/1.48  --prolific_symb_bound                   200
% 7.60/1.48  --lt_threshold                          2000
% 7.60/1.48  --clause_weak_htbl                      true
% 7.60/1.48  --gc_record_bc_elim                     false
% 7.60/1.48  
% 7.60/1.48  ------ Preprocessing Options
% 7.60/1.48  
% 7.60/1.48  --preprocessing_flag                    true
% 7.60/1.48  --time_out_prep_mult                    0.1
% 7.60/1.48  --splitting_mode                        input
% 7.60/1.48  --splitting_grd                         true
% 7.60/1.48  --splitting_cvd                         false
% 7.60/1.48  --splitting_cvd_svl                     false
% 7.60/1.48  --splitting_nvd                         32
% 7.60/1.48  --sub_typing                            true
% 7.60/1.48  --prep_gs_sim                           true
% 7.60/1.48  --prep_unflatten                        true
% 7.60/1.48  --prep_res_sim                          true
% 7.60/1.48  --prep_upred                            true
% 7.60/1.48  --prep_sem_filter                       exhaustive
% 7.60/1.48  --prep_sem_filter_out                   false
% 7.60/1.48  --pred_elim                             true
% 7.60/1.48  --res_sim_input                         true
% 7.60/1.48  --eq_ax_congr_red                       true
% 7.60/1.48  --pure_diseq_elim                       true
% 7.60/1.48  --brand_transform                       false
% 7.60/1.48  --non_eq_to_eq                          false
% 7.60/1.48  --prep_def_merge                        true
% 7.60/1.48  --prep_def_merge_prop_impl              false
% 7.60/1.48  --prep_def_merge_mbd                    true
% 7.60/1.48  --prep_def_merge_tr_red                 false
% 7.60/1.48  --prep_def_merge_tr_cl                  false
% 7.60/1.48  --smt_preprocessing                     true
% 7.60/1.48  --smt_ac_axioms                         fast
% 7.60/1.48  --preprocessed_out                      false
% 7.60/1.48  --preprocessed_stats                    false
% 7.60/1.48  
% 7.60/1.48  ------ Abstraction refinement Options
% 7.60/1.48  
% 7.60/1.48  --abstr_ref                             []
% 7.60/1.48  --abstr_ref_prep                        false
% 7.60/1.48  --abstr_ref_until_sat                   false
% 7.60/1.48  --abstr_ref_sig_restrict                funpre
% 7.60/1.48  --abstr_ref_af_restrict_to_split_sk     false
% 7.60/1.48  --abstr_ref_under                       []
% 7.60/1.48  
% 7.60/1.48  ------ SAT Options
% 7.60/1.48  
% 7.60/1.48  --sat_mode                              false
% 7.60/1.48  --sat_fm_restart_options                ""
% 7.60/1.48  --sat_gr_def                            false
% 7.60/1.48  --sat_epr_types                         true
% 7.60/1.48  --sat_non_cyclic_types                  false
% 7.60/1.48  --sat_finite_models                     false
% 7.60/1.48  --sat_fm_lemmas                         false
% 7.60/1.48  --sat_fm_prep                           false
% 7.60/1.48  --sat_fm_uc_incr                        true
% 7.60/1.48  --sat_out_model                         small
% 7.60/1.48  --sat_out_clauses                       false
% 7.60/1.48  
% 7.60/1.48  ------ QBF Options
% 7.60/1.48  
% 7.60/1.48  --qbf_mode                              false
% 7.60/1.48  --qbf_elim_univ                         false
% 7.60/1.48  --qbf_dom_inst                          none
% 7.60/1.48  --qbf_dom_pre_inst                      false
% 7.60/1.48  --qbf_sk_in                             false
% 7.60/1.48  --qbf_pred_elim                         true
% 7.60/1.48  --qbf_split                             512
% 7.60/1.48  
% 7.60/1.48  ------ BMC1 Options
% 7.60/1.48  
% 7.60/1.48  --bmc1_incremental                      false
% 7.60/1.48  --bmc1_axioms                           reachable_all
% 7.60/1.48  --bmc1_min_bound                        0
% 7.60/1.48  --bmc1_max_bound                        -1
% 7.60/1.48  --bmc1_max_bound_default                -1
% 7.60/1.48  --bmc1_symbol_reachability              true
% 7.60/1.48  --bmc1_property_lemmas                  false
% 7.60/1.48  --bmc1_k_induction                      false
% 7.60/1.48  --bmc1_non_equiv_states                 false
% 7.60/1.48  --bmc1_deadlock                         false
% 7.60/1.48  --bmc1_ucm                              false
% 7.60/1.48  --bmc1_add_unsat_core                   none
% 7.60/1.48  --bmc1_unsat_core_children              false
% 7.60/1.48  --bmc1_unsat_core_extrapolate_axioms    false
% 7.60/1.48  --bmc1_out_stat                         full
% 7.60/1.48  --bmc1_ground_init                      false
% 7.60/1.48  --bmc1_pre_inst_next_state              false
% 7.60/1.48  --bmc1_pre_inst_state                   false
% 7.60/1.48  --bmc1_pre_inst_reach_state             false
% 7.60/1.48  --bmc1_out_unsat_core                   false
% 7.60/1.48  --bmc1_aig_witness_out                  false
% 7.60/1.48  --bmc1_verbose                          false
% 7.60/1.48  --bmc1_dump_clauses_tptp                false
% 7.60/1.48  --bmc1_dump_unsat_core_tptp             false
% 7.60/1.48  --bmc1_dump_file                        -
% 7.60/1.48  --bmc1_ucm_expand_uc_limit              128
% 7.60/1.48  --bmc1_ucm_n_expand_iterations          6
% 7.60/1.48  --bmc1_ucm_extend_mode                  1
% 7.60/1.48  --bmc1_ucm_init_mode                    2
% 7.60/1.48  --bmc1_ucm_cone_mode                    none
% 7.60/1.48  --bmc1_ucm_reduced_relation_type        0
% 7.60/1.48  --bmc1_ucm_relax_model                  4
% 7.60/1.48  --bmc1_ucm_full_tr_after_sat            true
% 7.60/1.48  --bmc1_ucm_expand_neg_assumptions       false
% 7.60/1.48  --bmc1_ucm_layered_model                none
% 7.60/1.48  --bmc1_ucm_max_lemma_size               10
% 7.60/1.48  
% 7.60/1.48  ------ AIG Options
% 7.60/1.48  
% 7.60/1.48  --aig_mode                              false
% 7.60/1.48  
% 7.60/1.48  ------ Instantiation Options
% 7.60/1.48  
% 7.60/1.48  --instantiation_flag                    true
% 7.60/1.48  --inst_sos_flag                         true
% 7.60/1.48  --inst_sos_phase                        true
% 7.60/1.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 7.60/1.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 7.60/1.48  --inst_lit_sel_side                     none
% 7.60/1.48  --inst_solver_per_active                1400
% 7.60/1.48  --inst_solver_calls_frac                1.
% 7.60/1.48  --inst_passive_queue_type               priority_queues
% 7.60/1.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 7.60/1.48  --inst_passive_queues_freq              [25;2]
% 7.60/1.48  --inst_dismatching                      true
% 7.60/1.48  --inst_eager_unprocessed_to_passive     true
% 7.60/1.48  --inst_prop_sim_given                   true
% 7.60/1.48  --inst_prop_sim_new                     false
% 7.60/1.48  --inst_subs_new                         false
% 7.60/1.48  --inst_eq_res_simp                      false
% 7.60/1.48  --inst_subs_given                       false
% 7.60/1.48  --inst_orphan_elimination               true
% 7.60/1.48  --inst_learning_loop_flag               true
% 7.60/1.48  --inst_learning_start                   3000
% 7.60/1.48  --inst_learning_factor                  2
% 7.60/1.48  --inst_start_prop_sim_after_learn       3
% 7.60/1.48  --inst_sel_renew                        solver
% 7.60/1.48  --inst_lit_activity_flag                true
% 7.60/1.48  --inst_restr_to_given                   false
% 7.60/1.48  --inst_activity_threshold               500
% 7.60/1.48  --inst_out_proof                        true
% 7.60/1.48  
% 7.60/1.48  ------ Resolution Options
% 7.60/1.48  
% 7.60/1.48  --resolution_flag                       false
% 7.60/1.48  --res_lit_sel                           adaptive
% 7.60/1.48  --res_lit_sel_side                      none
% 7.60/1.48  --res_ordering                          kbo
% 7.60/1.48  --res_to_prop_solver                    active
% 7.60/1.48  --res_prop_simpl_new                    false
% 7.60/1.48  --res_prop_simpl_given                  true
% 7.60/1.48  --res_passive_queue_type                priority_queues
% 7.60/1.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 7.60/1.48  --res_passive_queues_freq               [15;5]
% 7.60/1.48  --res_forward_subs                      full
% 7.60/1.48  --res_backward_subs                     full
% 7.60/1.48  --res_forward_subs_resolution           true
% 7.60/1.48  --res_backward_subs_resolution          true
% 7.60/1.48  --res_orphan_elimination                true
% 7.60/1.48  --res_time_limit                        2.
% 7.60/1.48  --res_out_proof                         true
% 7.60/1.48  
% 7.60/1.48  ------ Superposition Options
% 7.60/1.48  
% 7.60/1.48  --superposition_flag                    true
% 7.60/1.48  --sup_passive_queue_type                priority_queues
% 7.60/1.48  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 7.60/1.48  --sup_passive_queues_freq               [8;1;4]
% 7.60/1.48  --demod_completeness_check              fast
% 7.60/1.48  --demod_use_ground                      true
% 7.60/1.48  --sup_to_prop_solver                    passive
% 7.60/1.48  --sup_prop_simpl_new                    true
% 7.60/1.48  --sup_prop_simpl_given                  true
% 7.60/1.48  --sup_fun_splitting                     true
% 7.60/1.48  --sup_smt_interval                      50000
% 7.60/1.48  
% 7.60/1.48  ------ Superposition Simplification Setup
% 7.60/1.48  
% 7.60/1.48  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 7.60/1.48  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 7.60/1.48  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 7.60/1.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 7.60/1.48  --sup_full_triv                         [TrivRules;PropSubs]
% 7.60/1.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 7.60/1.48  --sup_full_bw                           [BwDemod;BwSubsumption]
% 7.60/1.48  --sup_immed_triv                        [TrivRules]
% 7.60/1.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.48  --sup_immed_bw_main                     []
% 7.60/1.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 7.60/1.48  --sup_input_triv                        [Unflattening;TrivRules]
% 7.60/1.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 7.60/1.48  --sup_input_bw                          []
% 7.60/1.48  
% 7.60/1.48  ------ Combination Options
% 7.60/1.48  
% 7.60/1.48  --comb_res_mult                         3
% 7.60/1.48  --comb_sup_mult                         2
% 7.60/1.48  --comb_inst_mult                        10
% 7.60/1.48  
% 7.60/1.48  ------ Debug Options
% 7.60/1.48  
% 7.60/1.48  --dbg_backtrace                         false
% 7.60/1.48  --dbg_dump_prop_clauses                 false
% 7.60/1.48  --dbg_dump_prop_clauses_file            -
% 7.60/1.48  --dbg_out_stat                          false
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  ------ Proving...
% 7.60/1.48  
% 7.60/1.48  
% 7.60/1.48  % SZS status Theorem for theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.60/1.48  
% 7.60/1.48  fof(f20,conjecture,(
% 7.60/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f21,negated_conjecture,(
% 7.60/1.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 7.60/1.48    inference(negated_conjecture,[],[f20])).
% 7.60/1.48  
% 7.60/1.48  fof(f46,plain,(
% 7.60/1.48    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 7.60/1.48    inference(ennf_transformation,[],[f21])).
% 7.60/1.48  
% 7.60/1.48  fof(f47,plain,(
% 7.60/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 7.60/1.48    inference(flattening,[],[f46])).
% 7.60/1.48  
% 7.60/1.48  fof(f50,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (k2_funct_1(X2) != sK3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,sK3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(sK3,X1,X0) & v1_funct_1(sK3))) )),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f49,plain,(
% 7.60/1.48    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 7.60/1.48    introduced(choice_axiom,[])).
% 7.60/1.48  
% 7.60/1.48  fof(f51,plain,(
% 7.60/1.48    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & k2_relset_1(sK0,sK1,sK2) = sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 7.60/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f47,f50,f49])).
% 7.60/1.48  
% 7.60/1.48  fof(f87,plain,(
% 7.60/1.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  fof(f10,axiom,(
% 7.60/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f32,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.60/1.48    inference(ennf_transformation,[],[f10])).
% 7.60/1.48  
% 7.60/1.48  fof(f66,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f32])).
% 7.60/1.48  
% 7.60/1.48  fof(f84,plain,(
% 7.60/1.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  fof(f82,plain,(
% 7.60/1.48    v1_funct_1(sK2)),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  fof(f6,axiom,(
% 7.60/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f26,plain,(
% 7.60/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f6])).
% 7.60/1.48  
% 7.60/1.48  fof(f27,plain,(
% 7.60/1.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.60/1.48    inference(flattening,[],[f26])).
% 7.60/1.48  
% 7.60/1.48  fof(f58,plain,(
% 7.60/1.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f27])).
% 7.60/1.48  
% 7.60/1.48  fof(f2,axiom,(
% 7.60/1.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f23,plain,(
% 7.60/1.48    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.60/1.48    inference(ennf_transformation,[],[f2])).
% 7.60/1.48  
% 7.60/1.48  fof(f53,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (k5_relat_1(X0,k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(X0,X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f23])).
% 7.60/1.48  
% 7.60/1.48  fof(f88,plain,(
% 7.60/1.48    k2_relset_1(sK0,sK1,sK2) = sK1),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  fof(f19,axiom,(
% 7.60/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f44,plain,(
% 7.60/1.48    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.60/1.48    inference(ennf_transformation,[],[f19])).
% 7.60/1.48  
% 7.60/1.48  fof(f45,plain,(
% 7.60/1.48    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.60/1.48    inference(flattening,[],[f44])).
% 7.60/1.48  
% 7.60/1.48  fof(f81,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f45])).
% 7.60/1.48  
% 7.60/1.48  fof(f1,axiom,(
% 7.60/1.48    k1_xboole_0 = o_0_0_xboole_0),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f52,plain,(
% 7.60/1.48    k1_xboole_0 = o_0_0_xboole_0),
% 7.60/1.48    inference(cnf_transformation,[],[f1])).
% 7.60/1.48  
% 7.60/1.48  fof(f104,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | o_0_0_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.60/1.48    inference(definition_unfolding,[],[f81,f52])).
% 7.60/1.48  
% 7.60/1.48  fof(f83,plain,(
% 7.60/1.48    v1_funct_2(sK2,sK0,sK1)),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  fof(f90,plain,(
% 7.60/1.48    v2_funct_1(sK2)),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  fof(f92,plain,(
% 7.60/1.48    k1_xboole_0 != sK1),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  fof(f106,plain,(
% 7.60/1.48    o_0_0_xboole_0 != sK1),
% 7.60/1.48    inference(definition_unfolding,[],[f92,f52])).
% 7.60/1.48  
% 7.60/1.48  fof(f8,axiom,(
% 7.60/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f28,plain,(
% 7.60/1.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f8])).
% 7.60/1.48  
% 7.60/1.48  fof(f29,plain,(
% 7.60/1.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.60/1.48    inference(flattening,[],[f28])).
% 7.60/1.48  
% 7.60/1.48  fof(f63,plain,(
% 7.60/1.48    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f29])).
% 7.60/1.48  
% 7.60/1.48  fof(f9,axiom,(
% 7.60/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f30,plain,(
% 7.60/1.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.60/1.48    inference(ennf_transformation,[],[f9])).
% 7.60/1.48  
% 7.60/1.48  fof(f31,plain,(
% 7.60/1.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.60/1.48    inference(flattening,[],[f30])).
% 7.60/1.48  
% 7.60/1.48  fof(f64,plain,(
% 7.60/1.48    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f31])).
% 7.60/1.48  
% 7.60/1.48  fof(f80,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f45])).
% 7.60/1.48  
% 7.60/1.48  fof(f105,plain,(
% 7.60/1.48    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | o_0_0_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.60/1.48    inference(definition_unfolding,[],[f80,f52])).
% 7.60/1.48  
% 7.60/1.48  fof(f3,axiom,(
% 7.60/1.48    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f54,plain,(
% 7.60/1.48    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.60/1.48    inference(cnf_transformation,[],[f3])).
% 7.60/1.48  
% 7.60/1.48  fof(f16,axiom,(
% 7.60/1.48    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f74,plain,(
% 7.60/1.48    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f16])).
% 7.60/1.48  
% 7.60/1.48  fof(f95,plain,(
% 7.60/1.48    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 7.60/1.48    inference(definition_unfolding,[],[f54,f74])).
% 7.60/1.48  
% 7.60/1.48  fof(f5,axiom,(
% 7.60/1.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f25,plain,(
% 7.60/1.48    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 7.60/1.48    inference(ennf_transformation,[],[f5])).
% 7.60/1.48  
% 7.60/1.48  fof(f57,plain,(
% 7.60/1.48    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f25])).
% 7.60/1.48  
% 7.60/1.48  fof(f97,plain,(
% 7.60/1.48    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 7.60/1.48    inference(definition_unfolding,[],[f57,f74])).
% 7.60/1.48  
% 7.60/1.48  fof(f12,axiom,(
% 7.60/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f34,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 7.60/1.48    inference(ennf_transformation,[],[f12])).
% 7.60/1.48  
% 7.60/1.48  fof(f35,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.60/1.48    inference(flattening,[],[f34])).
% 7.60/1.48  
% 7.60/1.48  fof(f48,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.60/1.48    inference(nnf_transformation,[],[f35])).
% 7.60/1.48  
% 7.60/1.48  fof(f68,plain,(
% 7.60/1.48    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f48])).
% 7.60/1.48  
% 7.60/1.48  fof(f89,plain,(
% 7.60/1.48    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  fof(f14,axiom,(
% 7.60/1.48    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f22,plain,(
% 7.60/1.48    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 7.60/1.48    inference(pure_predicate_removal,[],[f14])).
% 7.60/1.48  
% 7.60/1.48  fof(f72,plain,(
% 7.60/1.48    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f22])).
% 7.60/1.48  
% 7.60/1.48  fof(f85,plain,(
% 7.60/1.48    v1_funct_1(sK3)),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  fof(f13,axiom,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f36,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.60/1.48    inference(ennf_transformation,[],[f13])).
% 7.60/1.48  
% 7.60/1.48  fof(f37,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.60/1.48    inference(flattening,[],[f36])).
% 7.60/1.48  
% 7.60/1.48  fof(f71,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f37])).
% 7.60/1.48  
% 7.60/1.48  fof(f18,axiom,(
% 7.60/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f42,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 7.60/1.48    inference(ennf_transformation,[],[f18])).
% 7.60/1.48  
% 7.60/1.48  fof(f43,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 7.60/1.48    inference(flattening,[],[f42])).
% 7.60/1.48  
% 7.60/1.48  fof(f78,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | k1_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f43])).
% 7.60/1.48  
% 7.60/1.48  fof(f101,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X4) | o_0_0_xboole_0 = X2 | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 7.60/1.48    inference(definition_unfolding,[],[f78,f52])).
% 7.60/1.48  
% 7.60/1.48  fof(f86,plain,(
% 7.60/1.48    v1_funct_2(sK3,sK1,sK0)),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  fof(f91,plain,(
% 7.60/1.48    k1_xboole_0 != sK0),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  fof(f107,plain,(
% 7.60/1.48    o_0_0_xboole_0 != sK0),
% 7.60/1.48    inference(definition_unfolding,[],[f91,f52])).
% 7.60/1.48  
% 7.60/1.48  fof(f7,axiom,(
% 7.60/1.48    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f61,plain,(
% 7.60/1.48    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 7.60/1.48    inference(cnf_transformation,[],[f7])).
% 7.60/1.48  
% 7.60/1.48  fof(f98,plain,(
% 7.60/1.48    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 7.60/1.48    inference(definition_unfolding,[],[f61,f74])).
% 7.60/1.48  
% 7.60/1.48  fof(f17,axiom,(
% 7.60/1.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f40,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 7.60/1.48    inference(ennf_transformation,[],[f17])).
% 7.60/1.48  
% 7.60/1.48  fof(f41,plain,(
% 7.60/1.48    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 7.60/1.48    inference(flattening,[],[f40])).
% 7.60/1.48  
% 7.60/1.48  fof(f75,plain,(
% 7.60/1.48    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f41])).
% 7.60/1.48  
% 7.60/1.48  fof(f4,axiom,(
% 7.60/1.48    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f24,plain,(
% 7.60/1.48    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 7.60/1.48    inference(ennf_transformation,[],[f4])).
% 7.60/1.48  
% 7.60/1.48  fof(f56,plain,(
% 7.60/1.48    ( ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f24])).
% 7.60/1.48  
% 7.60/1.48  fof(f96,plain,(
% 7.60/1.48    ( ! [X0] : (k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0)) )),
% 7.60/1.48    inference(definition_unfolding,[],[f56,f74])).
% 7.60/1.48  
% 7.60/1.48  fof(f15,axiom,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 7.60/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.60/1.48  
% 7.60/1.48  fof(f38,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 7.60/1.48    inference(ennf_transformation,[],[f15])).
% 7.60/1.48  
% 7.60/1.48  fof(f39,plain,(
% 7.60/1.48    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 7.60/1.48    inference(flattening,[],[f38])).
% 7.60/1.48  
% 7.60/1.48  fof(f73,plain,(
% 7.60/1.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 7.60/1.48    inference(cnf_transformation,[],[f39])).
% 7.60/1.48  
% 7.60/1.48  fof(f93,plain,(
% 7.60/1.48    k2_funct_1(sK2) != sK3),
% 7.60/1.48    inference(cnf_transformation,[],[f51])).
% 7.60/1.48  
% 7.60/1.48  cnf(c_34,negated_conjecture,
% 7.60/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
% 7.60/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1262,plain,
% 7.60/1.48      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_13,plain,
% 7.60/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | v1_relat_1(X0) ),
% 7.60/1.48      inference(cnf_transformation,[],[f66]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1275,plain,
% 7.60/1.48      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 7.60/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2374,plain,
% 7.60/1.48      ( v1_relat_1(sK3) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1262,c_1275]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_37,negated_conjecture,
% 7.60/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 7.60/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1259,plain,
% 7.60/1.48      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_2375,plain,
% 7.60/1.48      ( v1_relat_1(sK2) = iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1259,c_1275]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_39,negated_conjecture,
% 7.60/1.48      ( v1_funct_1(sK2) ),
% 7.60/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1257,plain,
% 7.60/1.48      ( v1_funct_1(sK2) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_6,plain,
% 7.60/1.48      ( ~ v1_funct_1(X0)
% 7.60/1.48      | ~ v1_relat_1(X0)
% 7.60/1.48      | v1_relat_1(k2_funct_1(X0)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f58]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1282,plain,
% 7.60/1.48      ( v1_funct_1(X0) != iProver_top
% 7.60/1.48      | v1_relat_1(X0) != iProver_top
% 7.60/1.48      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_0,plain,
% 7.60/1.48      ( ~ v1_relat_1(X0)
% 7.60/1.48      | ~ v1_relat_1(X1)
% 7.60/1.48      | ~ v1_relat_1(X2)
% 7.60/1.48      | k5_relat_1(k5_relat_1(X2,X1),X0) = k5_relat_1(X2,k5_relat_1(X1,X0)) ),
% 7.60/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1286,plain,
% 7.60/1.48      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
% 7.60/1.48      | v1_relat_1(X2) != iProver_top
% 7.60/1.48      | v1_relat_1(X1) != iProver_top
% 7.60/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_5059,plain,
% 7.60/1.48      ( k5_relat_1(k2_funct_1(X0),k5_relat_1(X1,X2)) = k5_relat_1(k5_relat_1(k2_funct_1(X0),X1),X2)
% 7.60/1.48      | v1_funct_1(X0) != iProver_top
% 7.60/1.48      | v1_relat_1(X0) != iProver_top
% 7.60/1.48      | v1_relat_1(X1) != iProver_top
% 7.60/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1282,c_1286]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_10033,plain,
% 7.60/1.48      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.60/1.48      | v1_relat_1(X0) != iProver_top
% 7.60/1.48      | v1_relat_1(X1) != iProver_top
% 7.60/1.48      | v1_relat_1(sK2) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_1257,c_5059]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_10181,plain,
% 7.60/1.48      ( v1_relat_1(X1) != iProver_top
% 7.60/1.48      | v1_relat_1(X0) != iProver_top
% 7.60/1.48      | k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1)) ),
% 7.60/1.48      inference(global_propositional_subsumption,
% 7.60/1.48                [status(thm)],
% 7.60/1.48                [c_10033,c_2375]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_10182,plain,
% 7.60/1.48      ( k5_relat_1(k5_relat_1(k2_funct_1(sK2),X0),X1) = k5_relat_1(k2_funct_1(sK2),k5_relat_1(X0,X1))
% 7.60/1.48      | v1_relat_1(X0) != iProver_top
% 7.60/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.60/1.48      inference(renaming,[status(thm)],[c_10181]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_10190,plain,
% 7.60/1.48      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k5_relat_1(k2_funct_1(sK2),sK2),X0)
% 7.60/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.60/1.48      inference(superposition,[status(thm)],[c_2375,c_10182]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_33,negated_conjecture,
% 7.60/1.48      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 7.60/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_26,plain,
% 7.60/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.60/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.48      | ~ v2_funct_1(X0)
% 7.60/1.48      | ~ v1_funct_1(X0)
% 7.60/1.48      | k2_relset_1(X1,X2,X0) != X2
% 7.60/1.48      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 7.60/1.48      | o_0_0_xboole_0 = X2 ),
% 7.60/1.48      inference(cnf_transformation,[],[f104]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_1265,plain,
% 7.60/1.48      ( k2_relset_1(X0,X1,X2) != X1
% 7.60/1.48      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 7.60/1.48      | o_0_0_xboole_0 = X1
% 7.60/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.60/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.48      | v2_funct_1(X2) != iProver_top
% 7.60/1.48      | v1_funct_1(X2) != iProver_top ),
% 7.60/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.60/1.48  
% 7.60/1.48  cnf(c_3520,plain,
% 7.60/1.48      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.60/1.48      | sK1 = o_0_0_xboole_0
% 7.60/1.48      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.60/1.48      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.60/1.49      | v2_funct_1(sK2) != iProver_top
% 7.60/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_33,c_1265]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_38,negated_conjecture,
% 7.60/1.49      ( v1_funct_2(sK2,sK0,sK1) ),
% 7.60/1.49      inference(cnf_transformation,[],[f83]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_31,negated_conjecture,
% 7.60/1.49      ( v2_funct_1(sK2) ),
% 7.60/1.49      inference(cnf_transformation,[],[f90]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_29,negated_conjecture,
% 7.60/1.49      ( o_0_0_xboole_0 != sK1 ),
% 7.60/1.49      inference(cnf_transformation,[],[f106]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1333,plain,
% 7.60/1.49      ( ~ v1_funct_2(X0,X1,sK1)
% 7.60/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.60/1.49      | ~ v2_funct_1(X0)
% 7.60/1.49      | ~ v1_funct_1(X0)
% 7.60/1.49      | k2_relset_1(X1,sK1,X0) != sK1
% 7.60/1.49      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(sK1)
% 7.60/1.49      | o_0_0_xboole_0 = sK1 ),
% 7.60/1.49      inference(instantiation,[status(thm)],[c_26]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1422,plain,
% 7.60/1.49      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.60/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.60/1.49      | ~ v2_funct_1(sK2)
% 7.60/1.49      | ~ v1_funct_1(sK2)
% 7.60/1.49      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.60/1.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.60/1.49      | o_0_0_xboole_0 = sK1 ),
% 7.60/1.49      inference(instantiation,[status(thm)],[c_1333]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1669,plain,
% 7.60/1.49      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.60/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.60/1.49      | ~ v2_funct_1(sK2)
% 7.60/1.49      | ~ v1_funct_1(sK2)
% 7.60/1.49      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.60/1.49      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)
% 7.60/1.49      | o_0_0_xboole_0 = sK1 ),
% 7.60/1.49      inference(instantiation,[status(thm)],[c_1422]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_4332,plain,
% 7.60/1.49      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_3520,c_39,c_38,c_37,c_33,c_31,c_29,c_1669]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_10194,plain,
% 7.60/1.49      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,X0)) = k5_relat_1(k6_partfun1(sK1),X0)
% 7.60/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.60/1.49      inference(light_normalisation,[status(thm)],[c_10190,c_4332]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_10219,plain,
% 7.60/1.49      ( k5_relat_1(k2_funct_1(sK2),k5_relat_1(sK2,sK3)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_2374,c_10194]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1263,plain,
% 7.60/1.49      ( v2_funct_1(sK2) = iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_9,plain,
% 7.60/1.49      ( ~ v2_funct_1(X0)
% 7.60/1.49      | ~ v1_funct_1(X0)
% 7.60/1.49      | ~ v1_relat_1(X0)
% 7.60/1.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 7.60/1.49      inference(cnf_transformation,[],[f63]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1279,plain,
% 7.60/1.49      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 7.60/1.49      | v2_funct_1(X0) != iProver_top
% 7.60/1.49      | v1_funct_1(X0) != iProver_top
% 7.60/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3548,plain,
% 7.60/1.49      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 7.60/1.49      | v1_funct_1(sK2) != iProver_top
% 7.60/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_1263,c_1279]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_40,plain,
% 7.60/1.49      ( v1_funct_1(sK2) = iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_4828,plain,
% 7.60/1.49      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_3548,c_40,c_2375]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_12,plain,
% 7.60/1.49      ( ~ v2_funct_1(X0)
% 7.60/1.49      | ~ v1_funct_1(X0)
% 7.60/1.49      | ~ v1_relat_1(X0)
% 7.60/1.49      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 7.60/1.49      inference(cnf_transformation,[],[f64]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1276,plain,
% 7.60/1.49      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 7.60/1.49      | v2_funct_1(X0) != iProver_top
% 7.60/1.49      | v1_funct_1(X0) != iProver_top
% 7.60/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3578,plain,
% 7.60/1.49      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 7.60/1.49      | v1_funct_1(sK2) != iProver_top
% 7.60/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_1263,c_1276]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_27,plain,
% 7.60/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.60/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.49      | ~ v2_funct_1(X0)
% 7.60/1.49      | ~ v1_funct_1(X0)
% 7.60/1.49      | k2_relset_1(X1,X2,X0) != X2
% 7.60/1.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.60/1.49      | o_0_0_xboole_0 = X2 ),
% 7.60/1.49      inference(cnf_transformation,[],[f105]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1264,plain,
% 7.60/1.49      ( k2_relset_1(X0,X1,X2) != X1
% 7.60/1.49      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 7.60/1.49      | o_0_0_xboole_0 = X1
% 7.60/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.60/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.49      | v2_funct_1(X2) != iProver_top
% 7.60/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3151,plain,
% 7.60/1.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.60/1.49      | sK1 = o_0_0_xboole_0
% 7.60/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.60/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.60/1.49      | v2_funct_1(sK2) != iProver_top
% 7.60/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_33,c_1264]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1334,plain,
% 7.60/1.49      ( ~ v1_funct_2(X0,X1,sK1)
% 7.60/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
% 7.60/1.49      | ~ v2_funct_1(X0)
% 7.60/1.49      | ~ v1_funct_1(X0)
% 7.60/1.49      | k2_relset_1(X1,sK1,X0) != sK1
% 7.60/1.49      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 7.60/1.49      | o_0_0_xboole_0 = sK1 ),
% 7.60/1.49      inference(instantiation,[status(thm)],[c_27]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1448,plain,
% 7.60/1.49      ( ~ v1_funct_2(sK2,X0,sK1)
% 7.60/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
% 7.60/1.49      | ~ v2_funct_1(sK2)
% 7.60/1.49      | ~ v1_funct_1(sK2)
% 7.60/1.49      | k2_relset_1(X0,sK1,sK2) != sK1
% 7.60/1.49      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(X0)
% 7.60/1.49      | o_0_0_xboole_0 = sK1 ),
% 7.60/1.49      inference(instantiation,[status(thm)],[c_1334]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1684,plain,
% 7.60/1.49      ( ~ v1_funct_2(sK2,sK0,sK1)
% 7.60/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.60/1.49      | ~ v2_funct_1(sK2)
% 7.60/1.49      | ~ v1_funct_1(sK2)
% 7.60/1.49      | k2_relset_1(sK0,sK1,sK2) != sK1
% 7.60/1.49      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0)
% 7.60/1.49      | o_0_0_xboole_0 = sK1 ),
% 7.60/1.49      inference(instantiation,[status(thm)],[c_1448]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3279,plain,
% 7.60/1.49      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(sK0) ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_3151,c_39,c_38,c_37,c_33,c_31,c_29,c_1684]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3579,plain,
% 7.60/1.49      ( k1_relat_1(k6_partfun1(sK0)) = k1_relat_1(sK2)
% 7.60/1.49      | v1_funct_1(sK2) != iProver_top
% 7.60/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.60/1.49      inference(light_normalisation,[status(thm)],[c_3578,c_3279]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_2,plain,
% 7.60/1.49      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 7.60/1.49      inference(cnf_transformation,[],[f95]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3580,plain,
% 7.60/1.49      ( k1_relat_1(sK2) = sK0
% 7.60/1.49      | v1_funct_1(sK2) != iProver_top
% 7.60/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.60/1.49      inference(demodulation,[status(thm)],[c_3579,c_2]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3587,plain,
% 7.60/1.49      ( k1_relat_1(sK2) = sK0 ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_3580,c_40,c_2375]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_4830,plain,
% 7.60/1.49      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 7.60/1.49      inference(light_normalisation,[status(thm)],[c_4828,c_3587]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_4,plain,
% 7.60/1.49      ( ~ v1_relat_1(X0)
% 7.60/1.49      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 7.60/1.49      inference(cnf_transformation,[],[f97]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1284,plain,
% 7.60/1.49      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 7.60/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3199,plain,
% 7.60/1.49      ( k5_relat_1(k2_funct_1(X0),k6_partfun1(k2_relat_1(k2_funct_1(X0)))) = k2_funct_1(X0)
% 7.60/1.49      | v1_funct_1(X0) != iProver_top
% 7.60/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_1282,c_1284]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3513,plain,
% 7.60/1.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2)
% 7.60/1.49      | v1_relat_1(sK2) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_1257,c_3199]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_4825,plain,
% 7.60/1.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(k2_relat_1(k2_funct_1(sK2)))) = k2_funct_1(sK2) ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_3513,c_2375]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_4831,plain,
% 7.60/1.49      ( k5_relat_1(k2_funct_1(sK2),k6_partfun1(sK0)) = k2_funct_1(sK2) ),
% 7.60/1.49      inference(demodulation,[status(thm)],[c_4830,c_4825]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_16,plain,
% 7.60/1.49      ( ~ r2_relset_1(X0,X1,X2,X3)
% 7.60/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.60/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.60/1.49      | X3 = X2 ),
% 7.60/1.49      inference(cnf_transformation,[],[f68]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_32,negated_conjecture,
% 7.60/1.49      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
% 7.60/1.49      inference(cnf_transformation,[],[f89]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_422,plain,
% 7.60/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.49      | X3 = X0
% 7.60/1.49      | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) != X0
% 7.60/1.49      | k6_partfun1(sK0) != X3
% 7.60/1.49      | sK0 != X2
% 7.60/1.49      | sK0 != X1 ),
% 7.60/1.49      inference(resolution_lifted,[status(thm)],[c_16,c_32]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_423,plain,
% 7.60/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.60/1.49      | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.60/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.60/1.49      inference(unflattening,[status(thm)],[c_422]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_19,plain,
% 7.60/1.49      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 7.60/1.49      inference(cnf_transformation,[],[f72]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_431,plain,
% 7.60/1.49      ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.60/1.49      | k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.60/1.49      inference(forward_subsumption_resolution,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_423,c_19]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1255,plain,
% 7.60/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.60/1.49      | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_36,negated_conjecture,
% 7.60/1.49      ( v1_funct_1(sK3) ),
% 7.60/1.49      inference(cnf_transformation,[],[f85]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_17,plain,
% 7.60/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.60/1.49      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 7.60/1.49      | ~ v1_funct_1(X0)
% 7.60/1.49      | ~ v1_funct_1(X3) ),
% 7.60/1.49      inference(cnf_transformation,[],[f71]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1371,plain,
% 7.60/1.49      ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 7.60/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 7.60/1.49      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 7.60/1.49      | ~ v1_funct_1(sK3)
% 7.60/1.49      | ~ v1_funct_1(sK2) ),
% 7.60/1.49      inference(instantiation,[status(thm)],[c_17]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_2135,plain,
% 7.60/1.49      ( k6_partfun1(sK0) = k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_1255,c_39,c_37,c_36,c_34,c_431,c_1371]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_23,plain,
% 7.60/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.60/1.49      | ~ v1_funct_2(X3,X4,X1)
% 7.60/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 7.60/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.49      | v2_funct_1(X0)
% 7.60/1.49      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 7.60/1.49      | ~ v1_funct_1(X0)
% 7.60/1.49      | ~ v1_funct_1(X3)
% 7.60/1.49      | k2_relset_1(X4,X1,X3) != X1
% 7.60/1.49      | o_0_0_xboole_0 = X2 ),
% 7.60/1.49      inference(cnf_transformation,[],[f101]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1268,plain,
% 7.60/1.49      ( k2_relset_1(X0,X1,X2) != X1
% 7.60/1.49      | o_0_0_xboole_0 = X3
% 7.60/1.49      | v1_funct_2(X4,X1,X3) != iProver_top
% 7.60/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.60/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) != iProver_top
% 7.60/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.49      | v2_funct_1(X4) = iProver_top
% 7.60/1.49      | v2_funct_1(k1_partfun1(X0,X1,X1,X3,X2,X4)) != iProver_top
% 7.60/1.49      | v1_funct_1(X4) != iProver_top
% 7.60/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_5409,plain,
% 7.60/1.49      ( o_0_0_xboole_0 = X0
% 7.60/1.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.60/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.60/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.60/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.60/1.49      | v2_funct_1(X1) = iProver_top
% 7.60/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.60/1.49      | v1_funct_1(X1) != iProver_top
% 7.60/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_33,c_1268]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_41,plain,
% 7.60/1.49      ( v1_funct_2(sK2,sK0,sK1) = iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_42,plain,
% 7.60/1.49      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_5462,plain,
% 7.60/1.49      ( v1_funct_1(X1) != iProver_top
% 7.60/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.60/1.49      | v2_funct_1(X1) = iProver_top
% 7.60/1.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.60/1.49      | o_0_0_xboole_0 = X0
% 7.60/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_5409,c_40,c_41,c_42]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_5463,plain,
% 7.60/1.49      ( o_0_0_xboole_0 = X0
% 7.60/1.49      | v1_funct_2(X1,sK1,X0) != iProver_top
% 7.60/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) != iProver_top
% 7.60/1.49      | v2_funct_1(X1) = iProver_top
% 7.60/1.49      | v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) != iProver_top
% 7.60/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.60/1.49      inference(renaming,[status(thm)],[c_5462]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_5466,plain,
% 7.60/1.49      ( sK0 = o_0_0_xboole_0
% 7.60/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.60/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.60/1.49      | v2_funct_1(k6_partfun1(sK0)) != iProver_top
% 7.60/1.49      | v2_funct_1(sK3) = iProver_top
% 7.60/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_2135,c_5463]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_43,plain,
% 7.60/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_35,negated_conjecture,
% 7.60/1.49      ( v1_funct_2(sK3,sK1,sK0) ),
% 7.60/1.49      inference(cnf_transformation,[],[f86]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_44,plain,
% 7.60/1.49      ( v1_funct_2(sK3,sK1,sK0) = iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_45,plain,
% 7.60/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_30,negated_conjecture,
% 7.60/1.49      ( o_0_0_xboole_0 != sK0 ),
% 7.60/1.49      inference(cnf_transformation,[],[f107]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_714,plain,( X0 = X0 ),theory(equality) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_745,plain,
% 7.60/1.49      ( o_0_0_xboole_0 = o_0_0_xboole_0 ),
% 7.60/1.49      inference(instantiation,[status(thm)],[c_714]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_715,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1369,plain,
% 7.60/1.49      ( sK0 != X0 | o_0_0_xboole_0 != X0 | o_0_0_xboole_0 = sK0 ),
% 7.60/1.49      inference(instantiation,[status(thm)],[c_715]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1370,plain,
% 7.60/1.49      ( sK0 != o_0_0_xboole_0
% 7.60/1.49      | o_0_0_xboole_0 = sK0
% 7.60/1.49      | o_0_0_xboole_0 != o_0_0_xboole_0 ),
% 7.60/1.49      inference(instantiation,[status(thm)],[c_1369]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_7,plain,
% 7.60/1.49      ( v2_funct_1(k6_partfun1(X0)) ),
% 7.60/1.49      inference(cnf_transformation,[],[f98]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3055,plain,
% 7.60/1.49      ( v2_funct_1(k6_partfun1(sK0)) ),
% 7.60/1.49      inference(instantiation,[status(thm)],[c_7]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3056,plain,
% 7.60/1.49      ( v2_funct_1(k6_partfun1(sK0)) = iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_3055]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_6570,plain,
% 7.60/1.49      ( v2_funct_1(sK3) = iProver_top ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_5466,c_43,c_44,c_45,c_30,c_745,c_1370,c_3056]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_6575,plain,
% 7.60/1.49      ( k1_relat_1(k5_relat_1(sK3,k2_funct_1(sK3))) = k1_relat_1(sK3)
% 7.60/1.49      | v1_funct_1(sK3) != iProver_top
% 7.60/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_6570,c_1276]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_21,plain,
% 7.60/1.49      ( ~ r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
% 7.60/1.49      | ~ v1_funct_2(X2,X0,X1)
% 7.60/1.49      | ~ v1_funct_2(X3,X1,X0)
% 7.60/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 7.60/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 7.60/1.49      | ~ v1_funct_1(X2)
% 7.60/1.49      | ~ v1_funct_1(X3)
% 7.60/1.49      | k2_relset_1(X1,X0,X3) = X0 ),
% 7.60/1.49      inference(cnf_transformation,[],[f75]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_435,plain,
% 7.60/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 7.60/1.49      | ~ v1_funct_2(X3,X2,X1)
% 7.60/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 7.60/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.49      | ~ v1_funct_1(X0)
% 7.60/1.49      | ~ v1_funct_1(X3)
% 7.60/1.49      | k1_partfun1(X2,X1,X1,X2,X3,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.60/1.49      | k2_relset_1(X1,X2,X0) = X2
% 7.60/1.49      | k6_partfun1(X2) != k6_partfun1(sK0)
% 7.60/1.49      | sK0 != X2 ),
% 7.60/1.49      inference(resolution_lifted,[status(thm)],[c_21,c_32]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_436,plain,
% 7.60/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.60/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.60/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.60/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.60/1.49      | ~ v1_funct_1(X0)
% 7.60/1.49      | ~ v1_funct_1(X2)
% 7.60/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.60/1.49      | k2_relset_1(X1,sK0,X0) = sK0
% 7.60/1.49      | k6_partfun1(sK0) != k6_partfun1(sK0) ),
% 7.60/1.49      inference(unflattening,[status(thm)],[c_435]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_523,plain,
% 7.60/1.49      ( ~ v1_funct_2(X0,X1,sK0)
% 7.60/1.49      | ~ v1_funct_2(X2,sK0,X1)
% 7.60/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK0)))
% 7.60/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 7.60/1.49      | ~ v1_funct_1(X0)
% 7.60/1.49      | ~ v1_funct_1(X2)
% 7.60/1.49      | k1_partfun1(sK0,X1,X1,sK0,X2,X0) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.60/1.49      | k2_relset_1(X1,sK0,X0) = sK0 ),
% 7.60/1.49      inference(equality_resolution_simp,[status(thm)],[c_436]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1254,plain,
% 7.60/1.49      ( k1_partfun1(sK0,X0,X0,sK0,X1,X2) != k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)
% 7.60/1.49      | k2_relset_1(X0,sK0,X2) = sK0
% 7.60/1.49      | v1_funct_2(X2,X0,sK0) != iProver_top
% 7.60/1.49      | v1_funct_2(X1,sK0,X0) != iProver_top
% 7.60/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,sK0))) != iProver_top
% 7.60/1.49      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) != iProver_top
% 7.60/1.49      | v1_funct_1(X2) != iProver_top
% 7.60/1.49      | v1_funct_1(X1) != iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1807,plain,
% 7.60/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0
% 7.60/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.60/1.49      | v1_funct_2(sK2,sK0,sK1) != iProver_top
% 7.60/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.60/1.49      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 7.60/1.49      | v1_funct_1(sK3) != iProver_top
% 7.60/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.60/1.49      inference(equality_resolution,[status(thm)],[c_1254]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_2142,plain,
% 7.60/1.49      ( k2_relset_1(sK1,sK0,sK3) = sK0 ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_1807,c_40,c_41,c_42,c_43,c_44,c_45]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3152,plain,
% 7.60/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.60/1.49      | sK0 = o_0_0_xboole_0
% 7.60/1.49      | v1_funct_2(sK3,sK1,sK0) != iProver_top
% 7.60/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 7.60/1.49      | v2_funct_1(sK3) != iProver_top
% 7.60/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_2142,c_1264]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3322,plain,
% 7.60/1.49      ( v2_funct_1(sK3) != iProver_top
% 7.60/1.49      | k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_3152,c_43,c_44,c_45,c_30,c_745,c_1370]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3323,plain,
% 7.60/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1)
% 7.60/1.49      | v2_funct_1(sK3) != iProver_top ),
% 7.60/1.49      inference(renaming,[status(thm)],[c_3322]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_6579,plain,
% 7.60/1.49      ( k5_relat_1(sK3,k2_funct_1(sK3)) = k6_partfun1(sK1) ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_6570,c_3323]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_6581,plain,
% 7.60/1.49      ( k1_relat_1(k6_partfun1(sK1)) = k1_relat_1(sK3)
% 7.60/1.49      | v1_funct_1(sK3) != iProver_top
% 7.60/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.60/1.49      inference(demodulation,[status(thm)],[c_6575,c_6579]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_6582,plain,
% 7.60/1.49      ( k1_relat_1(sK3) = sK1
% 7.60/1.49      | v1_funct_1(sK3) != iProver_top
% 7.60/1.49      | v1_relat_1(sK3) != iProver_top ),
% 7.60/1.49      inference(demodulation,[status(thm)],[c_6581,c_2]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_6677,plain,
% 7.60/1.49      ( k1_relat_1(sK3) = sK1 ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_6582,c_43,c_2374]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_3,plain,
% 7.60/1.49      ( ~ v1_relat_1(X0)
% 7.60/1.49      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ),
% 7.60/1.49      inference(cnf_transformation,[],[f96]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1285,plain,
% 7.60/1.49      ( k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0
% 7.60/1.49      | v1_relat_1(X0) != iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_2605,plain,
% 7.60/1.49      ( k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) = sK3 ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_2374,c_1285]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_6679,plain,
% 7.60/1.49      ( k5_relat_1(k6_partfun1(sK1),sK3) = sK3 ),
% 7.60/1.49      inference(demodulation,[status(thm)],[c_6677,c_2605]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_20,plain,
% 7.60/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.60/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 7.60/1.49      | ~ v1_funct_1(X0)
% 7.60/1.49      | ~ v1_funct_1(X3)
% 7.60/1.49      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 7.60/1.49      inference(cnf_transformation,[],[f73]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_1270,plain,
% 7.60/1.49      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 7.60/1.49      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 7.60/1.49      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.49      | v1_funct_1(X5) != iProver_top
% 7.60/1.49      | v1_funct_1(X4) != iProver_top ),
% 7.60/1.49      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_5348,plain,
% 7.60/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.60/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.49      | v1_funct_1(X2) != iProver_top
% 7.60/1.49      | v1_funct_1(sK3) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_1262,c_1270]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_5469,plain,
% 7.60/1.49      ( v1_funct_1(X2) != iProver_top
% 7.60/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.49      | k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3) ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_5348,c_43]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_5470,plain,
% 7.60/1.49      ( k1_partfun1(X0,X1,sK1,sK0,X2,sK3) = k5_relat_1(X2,sK3)
% 7.60/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 7.60/1.49      | v1_funct_1(X2) != iProver_top ),
% 7.60/1.49      inference(renaming,[status(thm)],[c_5469]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_5478,plain,
% 7.60/1.49      ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
% 7.60/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.60/1.49      inference(superposition,[status(thm)],[c_1259,c_5470]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_5479,plain,
% 7.60/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0)
% 7.60/1.49      | v1_funct_1(sK2) != iProver_top ),
% 7.60/1.49      inference(light_normalisation,[status(thm)],[c_5478,c_2135]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_6766,plain,
% 7.60/1.49      ( k5_relat_1(sK2,sK3) = k6_partfun1(sK0) ),
% 7.60/1.49      inference(global_propositional_subsumption,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_5479,c_40]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_10226,plain,
% 7.60/1.49      ( k2_funct_1(sK2) = sK3 ),
% 7.60/1.49      inference(light_normalisation,
% 7.60/1.49                [status(thm)],
% 7.60/1.49                [c_10219,c_4831,c_6679,c_6766]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(c_28,negated_conjecture,
% 7.60/1.49      ( k2_funct_1(sK2) != sK3 ),
% 7.60/1.49      inference(cnf_transformation,[],[f93]) ).
% 7.60/1.49  
% 7.60/1.49  cnf(contradiction,plain,
% 7.60/1.49      ( $false ),
% 7.60/1.49      inference(minisat,[status(thm)],[c_10226,c_28]) ).
% 7.60/1.49  
% 7.60/1.49  
% 7.60/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 7.60/1.49  
% 7.60/1.49  ------                               Statistics
% 7.60/1.49  
% 7.60/1.49  ------ General
% 7.60/1.49  
% 7.60/1.49  abstr_ref_over_cycles:                  0
% 7.60/1.49  abstr_ref_under_cycles:                 0
% 7.60/1.49  gc_basic_clause_elim:                   0
% 7.60/1.49  forced_gc_time:                         0
% 7.60/1.49  parsing_time:                           0.019
% 7.60/1.49  unif_index_cands_time:                  0.
% 7.60/1.49  unif_index_add_time:                    0.
% 7.60/1.49  orderings_time:                         0.
% 7.60/1.49  out_proof_time:                         0.016
% 7.60/1.49  total_time:                             0.51
% 7.60/1.49  num_of_symbols:                         51
% 7.60/1.49  num_of_terms:                           16225
% 7.60/1.49  
% 7.60/1.49  ------ Preprocessing
% 7.60/1.49  
% 7.60/1.49  num_of_splits:                          0
% 7.60/1.49  num_of_split_atoms:                     0
% 7.60/1.49  num_of_reused_defs:                     0
% 7.60/1.49  num_eq_ax_congr_red:                    0
% 7.60/1.49  num_of_sem_filtered_clauses:            1
% 7.60/1.49  num_of_subtypes:                        0
% 7.60/1.49  monotx_restored_types:                  0
% 7.60/1.49  sat_num_of_epr_types:                   0
% 7.60/1.49  sat_num_of_non_cyclic_types:            0
% 7.60/1.49  sat_guarded_non_collapsed_types:        0
% 7.60/1.49  num_pure_diseq_elim:                    0
% 7.60/1.49  simp_replaced_by:                       0
% 7.60/1.49  res_preprocessed:                       190
% 7.60/1.49  prep_upred:                             0
% 7.60/1.49  prep_unflattend:                        12
% 7.60/1.49  smt_new_axioms:                         0
% 7.60/1.49  pred_elim_cands:                        5
% 7.60/1.49  pred_elim:                              1
% 7.60/1.49  pred_elim_cl:                           1
% 7.60/1.49  pred_elim_cycles:                       3
% 7.60/1.49  merged_defs:                            0
% 7.60/1.49  merged_defs_ncl:                        0
% 7.60/1.49  bin_hyper_res:                          0
% 7.60/1.49  prep_cycles:                            4
% 7.60/1.49  pred_elim_time:                         0.005
% 7.60/1.49  splitting_time:                         0.
% 7.60/1.49  sem_filter_time:                        0.
% 7.60/1.49  monotx_time:                            0.
% 7.60/1.49  subtype_inf_time:                       0.
% 7.60/1.49  
% 7.60/1.49  ------ Problem properties
% 7.60/1.49  
% 7.60/1.49  clauses:                                39
% 7.60/1.49  conjectures:                            11
% 7.60/1.49  epr:                                    7
% 7.60/1.49  horn:                                   35
% 7.60/1.49  ground:                                 12
% 7.60/1.49  unary:                                  16
% 7.60/1.49  binary:                                 5
% 7.60/1.49  lits:                                   135
% 7.60/1.49  lits_eq:                                32
% 7.60/1.49  fd_pure:                                0
% 7.60/1.49  fd_pseudo:                              0
% 7.60/1.49  fd_cond:                                4
% 7.60/1.49  fd_pseudo_cond:                         0
% 7.60/1.49  ac_symbols:                             0
% 7.60/1.49  
% 7.60/1.49  ------ Propositional Solver
% 7.60/1.49  
% 7.60/1.49  prop_solver_calls:                      29
% 7.60/1.49  prop_fast_solver_calls:                 1816
% 7.60/1.49  smt_solver_calls:                       0
% 7.60/1.49  smt_fast_solver_calls:                  0
% 7.60/1.49  prop_num_of_clauses:                    5418
% 7.60/1.49  prop_preprocess_simplified:             13740
% 7.60/1.49  prop_fo_subsumed:                       116
% 7.60/1.49  prop_solver_time:                       0.
% 7.60/1.49  smt_solver_time:                        0.
% 7.60/1.49  smt_fast_solver_time:                   0.
% 7.60/1.49  prop_fast_solver_time:                  0.
% 7.60/1.49  prop_unsat_core_time:                   0.
% 7.60/1.49  
% 7.60/1.49  ------ QBF
% 7.60/1.49  
% 7.60/1.49  qbf_q_res:                              0
% 7.60/1.49  qbf_num_tautologies:                    0
% 7.60/1.49  qbf_prep_cycles:                        0
% 7.60/1.49  
% 7.60/1.49  ------ BMC1
% 7.60/1.49  
% 7.60/1.49  bmc1_current_bound:                     -1
% 7.60/1.49  bmc1_last_solved_bound:                 -1
% 7.60/1.49  bmc1_unsat_core_size:                   -1
% 7.60/1.49  bmc1_unsat_core_parents_size:           -1
% 7.60/1.49  bmc1_merge_next_fun:                    0
% 7.60/1.49  bmc1_unsat_core_clauses_time:           0.
% 7.60/1.49  
% 7.60/1.49  ------ Instantiation
% 7.60/1.49  
% 7.60/1.49  inst_num_of_clauses:                    1297
% 7.60/1.49  inst_num_in_passive:                    466
% 7.60/1.49  inst_num_in_active:                     717
% 7.60/1.49  inst_num_in_unprocessed:                114
% 7.60/1.49  inst_num_of_loops:                      790
% 7.60/1.49  inst_num_of_learning_restarts:          0
% 7.60/1.49  inst_num_moves_active_passive:          72
% 7.60/1.49  inst_lit_activity:                      0
% 7.60/1.49  inst_lit_activity_moves:                1
% 7.60/1.49  inst_num_tautologies:                   0
% 7.60/1.49  inst_num_prop_implied:                  0
% 7.60/1.49  inst_num_existing_simplified:           0
% 7.60/1.49  inst_num_eq_res_simplified:             0
% 7.60/1.49  inst_num_child_elim:                    0
% 7.60/1.49  inst_num_of_dismatching_blockings:      145
% 7.60/1.49  inst_num_of_non_proper_insts:           1140
% 7.60/1.49  inst_num_of_duplicates:                 0
% 7.60/1.49  inst_inst_num_from_inst_to_res:         0
% 7.60/1.49  inst_dismatching_checking_time:         0.
% 7.60/1.49  
% 7.60/1.49  ------ Resolution
% 7.60/1.49  
% 7.60/1.49  res_num_of_clauses:                     0
% 7.60/1.49  res_num_in_passive:                     0
% 7.60/1.49  res_num_in_active:                      0
% 7.60/1.49  res_num_of_loops:                       194
% 7.60/1.49  res_forward_subset_subsumed:            56
% 7.60/1.49  res_backward_subset_subsumed:           0
% 7.60/1.49  res_forward_subsumed:                   0
% 7.60/1.49  res_backward_subsumed:                  0
% 7.60/1.49  res_forward_subsumption_resolution:     2
% 7.60/1.49  res_backward_subsumption_resolution:    0
% 7.60/1.49  res_clause_to_clause_subsumption:       545
% 7.60/1.49  res_orphan_elimination:                 0
% 7.60/1.49  res_tautology_del:                      20
% 7.60/1.49  res_num_eq_res_simplified:              1
% 7.60/1.49  res_num_sel_changes:                    0
% 7.60/1.49  res_moves_from_active_to_pass:          0
% 7.60/1.49  
% 7.60/1.49  ------ Superposition
% 7.60/1.49  
% 7.60/1.49  sup_time_total:                         0.
% 7.60/1.49  sup_time_generating:                    0.
% 7.60/1.49  sup_time_sim_full:                      0.
% 7.60/1.49  sup_time_sim_immed:                     0.
% 7.60/1.49  
% 7.60/1.49  sup_num_of_clauses:                     266
% 7.60/1.49  sup_num_in_active:                      148
% 7.60/1.49  sup_num_in_passive:                     118
% 7.60/1.49  sup_num_of_loops:                       157
% 7.60/1.49  sup_fw_superposition:                   156
% 7.60/1.49  sup_bw_superposition:                   110
% 7.60/1.49  sup_immediate_simplified:               61
% 7.60/1.49  sup_given_eliminated:                   1
% 7.60/1.49  comparisons_done:                       0
% 7.60/1.49  comparisons_avoided:                    4
% 7.60/1.49  
% 7.60/1.49  ------ Simplifications
% 7.60/1.49  
% 7.60/1.49  
% 7.60/1.49  sim_fw_subset_subsumed:                 4
% 7.60/1.49  sim_bw_subset_subsumed:                 12
% 7.60/1.49  sim_fw_subsumed:                        5
% 7.60/1.49  sim_bw_subsumed:                        0
% 7.60/1.49  sim_fw_subsumption_res:                 0
% 7.60/1.49  sim_bw_subsumption_res:                 0
% 7.60/1.49  sim_tautology_del:                      2
% 7.60/1.49  sim_eq_tautology_del:                   4
% 7.60/1.49  sim_eq_res_simp:                        0
% 7.60/1.49  sim_fw_demodulated:                     6
% 7.60/1.49  sim_bw_demodulated:                     10
% 7.60/1.49  sim_light_normalised:                   54
% 7.60/1.49  sim_joinable_taut:                      0
% 7.60/1.49  sim_joinable_simp:                      0
% 7.60/1.49  sim_ac_normalised:                      0
% 7.60/1.49  sim_smt_subsumption:                    0
% 7.60/1.49  
%------------------------------------------------------------------------------
