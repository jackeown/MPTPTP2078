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
% DateTime   : Thu Dec  3 12:02:19 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.67s
% Verified   : 
% Statistics : Number of formulae       :  198 (4609 expanded)
%              Number of clauses        :  128 (1581 expanded)
%              Number of leaves         :   18 ( 867 expanded)
%              Depth                    :   24
%              Number of atoms          :  604 (23729 expanded)
%              Number of equality atoms :  256 (4551 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f49,plain,(
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

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f47,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f50,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
      & k2_relset_1(sK0,sK1,sK2) = sK1
      & v2_funct_1(sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f50])).

fof(f84,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f51])).

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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f67,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f86,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f63,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f87,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f51])).

fof(f66,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f64,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f65,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f88,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f92,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f77])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f40])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f75])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_relat_1(k4_relat_1(X0))
        & v1_xboole_0(k4_relat_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f56,plain,(
    ! [X0] :
      ( v1_xboole_0(k4_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1261,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_1262,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1261])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1264,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1262,c_34])).

cnf(c_2311,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_2314,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3860,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2311,c_2314])).

cnf(c_3983,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1264,c_3860])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2315,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3230,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2311,c_2315])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_479,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_33])).

cnf(c_480,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_482,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_480,c_36])).

cnf(c_2305,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_482])).

cnf(c_3237,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3230,c_2305])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_493,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_33])).

cnf(c_494,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_493])).

cnf(c_496,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_36])).

cnf(c_2304,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_496])).

cnf(c_3238,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3230,c_2304])).

cnf(c_3241,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3237,c_3238])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2312,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_4468,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3241,c_2312])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2313,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3763,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2311,c_2313])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_3765,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3763,c_32])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_465,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_33])).

cnf(c_466,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_465])).

cnf(c_468,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_466,c_36])).

cnf(c_2306,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_3236,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3230,c_2306])).

cnf(c_3244,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3236,c_3238])).

cnf(c_3771,plain,
    ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3765,c_3244])).

cnf(c_4481,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4468,c_3771])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2601,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2759,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2601])).

cnf(c_2760,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2759])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2316,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3870,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k4_relat_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3238,c_2316])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_2317,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4401,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3238,c_2317])).

cnf(c_4825,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4481,c_37,c_39,c_2760,c_3870,c_4401])).

cnf(c_4832,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4825,c_2314])).

cnf(c_4838,plain,
    ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_4832,c_3771])).

cnf(c_4846,plain,
    ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3983,c_4838])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1378,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) != sK1
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != sK0 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_1379,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(unflattening,[status(thm)],[c_1378])).

cnf(c_1391,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1379,c_16])).

cnf(c_2293,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1391])).

cnf(c_1380,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1379])).

cnf(c_2594,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2595,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2594])).

cnf(c_2909,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2910,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2909])).

cnf(c_2918,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2293,c_37,c_39,c_1380,c_2595,c_2760,c_2910])).

cnf(c_2919,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2918])).

cnf(c_3339,plain,
    ( k1_relat_1(k4_relat_1(sK2)) != sK1
    | k2_relat_1(k4_relat_1(sK2)) != sK0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3238,c_2919])).

cnf(c_4293,plain,
    ( k2_relat_1(k4_relat_1(sK2)) != sK0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3339,c_3771])).

cnf(c_4297,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4293,c_3241])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1347,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_1348,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1347])).

cnf(c_21,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_388,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_21,c_19])).

cnf(c_392,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_388,c_21,c_19])).

cnf(c_393,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_392])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1183,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1)
    | X3 != X0
    | X4 != X2
    | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_393,c_26])).

cnf(c_1184,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1183])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1188,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1184,c_0])).

cnf(c_1189,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1188])).

cnf(c_1355,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK1 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1348,c_1189])).

cnf(c_2295,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1355])).

cnf(c_124,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1710,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2609,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1710])).

cnf(c_2610,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2609])).

cnf(c_2612,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2610])).

cnf(c_1232,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_xboole_0(X1)
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_393,c_31])).

cnf(c_1233,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1232])).

cnf(c_2300,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_1234,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1233])).

cnf(c_2794,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2300,c_37,c_39,c_1234,c_2595,c_2760])).

cnf(c_2976,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2295,c_124,c_2612,c_2794])).

cnf(c_3337,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3238,c_2976])).

cnf(c_4301,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4297,c_3337,c_3983])).

cnf(c_4830,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3983,c_4825])).

cnf(c_4857,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4846,c_3337,c_3983,c_4297,c_4830])).

cnf(c_4872,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4857,c_3337])).

cnf(c_4911,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4872])).

cnf(c_2325,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k4_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2320,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f53])).

cnf(c_2324,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3136,plain,
    ( k4_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_2324])).

cnf(c_5198,plain,
    ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2325,c_3136])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | v1_xboole_0(X0)
    | ~ v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2319,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4445,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3765,c_2319])).

cnf(c_4627,plain,
    ( v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4445,c_39,c_2760])).

cnf(c_4864,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4857,c_4627])).

cnf(c_5355,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4864,c_39,c_124,c_2612,c_2760,c_3337,c_3983,c_4297,c_4445,c_4830])).

cnf(c_5363,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5355,c_2324])).

cnf(c_6142,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4911,c_5198,c_5363])).

cnf(c_2,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_2323,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_6144,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6142,c_2323])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:07:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.67/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.02  
% 2.67/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.67/1.02  
% 2.67/1.02  ------  iProver source info
% 2.67/1.02  
% 2.67/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.67/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.67/1.02  git: non_committed_changes: false
% 2.67/1.02  git: last_make_outside_of_git: false
% 2.67/1.02  
% 2.67/1.02  ------ 
% 2.67/1.02  
% 2.67/1.02  ------ Input Options
% 2.67/1.02  
% 2.67/1.02  --out_options                           all
% 2.67/1.02  --tptp_safe_out                         true
% 2.67/1.02  --problem_path                          ""
% 2.67/1.02  --include_path                          ""
% 2.67/1.02  --clausifier                            res/vclausify_rel
% 2.67/1.02  --clausifier_options                    --mode clausify
% 2.67/1.02  --stdin                                 false
% 2.67/1.02  --stats_out                             all
% 2.67/1.02  
% 2.67/1.02  ------ General Options
% 2.67/1.02  
% 2.67/1.02  --fof                                   false
% 2.67/1.02  --time_out_real                         305.
% 2.67/1.02  --time_out_virtual                      -1.
% 2.67/1.02  --symbol_type_check                     false
% 2.67/1.02  --clausify_out                          false
% 2.67/1.02  --sig_cnt_out                           false
% 2.67/1.02  --trig_cnt_out                          false
% 2.67/1.02  --trig_cnt_out_tolerance                1.
% 2.67/1.02  --trig_cnt_out_sk_spl                   false
% 2.67/1.02  --abstr_cl_out                          false
% 2.67/1.02  
% 2.67/1.02  ------ Global Options
% 2.67/1.02  
% 2.67/1.02  --schedule                              default
% 2.67/1.02  --add_important_lit                     false
% 2.67/1.02  --prop_solver_per_cl                    1000
% 2.67/1.02  --min_unsat_core                        false
% 2.67/1.02  --soft_assumptions                      false
% 2.67/1.02  --soft_lemma_size                       3
% 2.67/1.02  --prop_impl_unit_size                   0
% 2.67/1.02  --prop_impl_unit                        []
% 2.67/1.02  --share_sel_clauses                     true
% 2.67/1.02  --reset_solvers                         false
% 2.67/1.02  --bc_imp_inh                            [conj_cone]
% 2.67/1.02  --conj_cone_tolerance                   3.
% 2.67/1.02  --extra_neg_conj                        none
% 2.67/1.02  --large_theory_mode                     true
% 2.67/1.02  --prolific_symb_bound                   200
% 2.67/1.02  --lt_threshold                          2000
% 2.67/1.02  --clause_weak_htbl                      true
% 2.67/1.02  --gc_record_bc_elim                     false
% 2.67/1.02  
% 2.67/1.02  ------ Preprocessing Options
% 2.67/1.02  
% 2.67/1.02  --preprocessing_flag                    true
% 2.67/1.02  --time_out_prep_mult                    0.1
% 2.67/1.02  --splitting_mode                        input
% 2.67/1.02  --splitting_grd                         true
% 2.67/1.02  --splitting_cvd                         false
% 2.67/1.02  --splitting_cvd_svl                     false
% 2.67/1.02  --splitting_nvd                         32
% 2.67/1.02  --sub_typing                            true
% 2.67/1.02  --prep_gs_sim                           true
% 2.67/1.02  --prep_unflatten                        true
% 2.67/1.02  --prep_res_sim                          true
% 2.67/1.02  --prep_upred                            true
% 2.67/1.02  --prep_sem_filter                       exhaustive
% 2.67/1.02  --prep_sem_filter_out                   false
% 2.67/1.02  --pred_elim                             true
% 2.67/1.02  --res_sim_input                         true
% 2.67/1.02  --eq_ax_congr_red                       true
% 2.67/1.02  --pure_diseq_elim                       true
% 2.67/1.02  --brand_transform                       false
% 2.67/1.02  --non_eq_to_eq                          false
% 2.67/1.02  --prep_def_merge                        true
% 2.67/1.02  --prep_def_merge_prop_impl              false
% 2.67/1.02  --prep_def_merge_mbd                    true
% 2.67/1.02  --prep_def_merge_tr_red                 false
% 2.67/1.02  --prep_def_merge_tr_cl                  false
% 2.67/1.02  --smt_preprocessing                     true
% 2.67/1.02  --smt_ac_axioms                         fast
% 2.67/1.02  --preprocessed_out                      false
% 2.67/1.02  --preprocessed_stats                    false
% 2.67/1.02  
% 2.67/1.02  ------ Abstraction refinement Options
% 2.67/1.02  
% 2.67/1.02  --abstr_ref                             []
% 2.67/1.02  --abstr_ref_prep                        false
% 2.67/1.02  --abstr_ref_until_sat                   false
% 2.67/1.02  --abstr_ref_sig_restrict                funpre
% 2.67/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.02  --abstr_ref_under                       []
% 2.67/1.02  
% 2.67/1.02  ------ SAT Options
% 2.67/1.02  
% 2.67/1.02  --sat_mode                              false
% 2.67/1.02  --sat_fm_restart_options                ""
% 2.67/1.02  --sat_gr_def                            false
% 2.67/1.02  --sat_epr_types                         true
% 2.67/1.02  --sat_non_cyclic_types                  false
% 2.67/1.02  --sat_finite_models                     false
% 2.67/1.02  --sat_fm_lemmas                         false
% 2.67/1.02  --sat_fm_prep                           false
% 2.67/1.02  --sat_fm_uc_incr                        true
% 2.67/1.02  --sat_out_model                         small
% 2.67/1.02  --sat_out_clauses                       false
% 2.67/1.02  
% 2.67/1.02  ------ QBF Options
% 2.67/1.02  
% 2.67/1.02  --qbf_mode                              false
% 2.67/1.02  --qbf_elim_univ                         false
% 2.67/1.02  --qbf_dom_inst                          none
% 2.67/1.02  --qbf_dom_pre_inst                      false
% 2.67/1.02  --qbf_sk_in                             false
% 2.67/1.02  --qbf_pred_elim                         true
% 2.67/1.02  --qbf_split                             512
% 2.67/1.02  
% 2.67/1.02  ------ BMC1 Options
% 2.67/1.02  
% 2.67/1.02  --bmc1_incremental                      false
% 2.67/1.02  --bmc1_axioms                           reachable_all
% 2.67/1.02  --bmc1_min_bound                        0
% 2.67/1.02  --bmc1_max_bound                        -1
% 2.67/1.02  --bmc1_max_bound_default                -1
% 2.67/1.02  --bmc1_symbol_reachability              true
% 2.67/1.02  --bmc1_property_lemmas                  false
% 2.67/1.02  --bmc1_k_induction                      false
% 2.67/1.02  --bmc1_non_equiv_states                 false
% 2.67/1.02  --bmc1_deadlock                         false
% 2.67/1.02  --bmc1_ucm                              false
% 2.67/1.02  --bmc1_add_unsat_core                   none
% 2.67/1.02  --bmc1_unsat_core_children              false
% 2.67/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.02  --bmc1_out_stat                         full
% 2.67/1.02  --bmc1_ground_init                      false
% 2.67/1.02  --bmc1_pre_inst_next_state              false
% 2.67/1.02  --bmc1_pre_inst_state                   false
% 2.67/1.02  --bmc1_pre_inst_reach_state             false
% 2.67/1.02  --bmc1_out_unsat_core                   false
% 2.67/1.02  --bmc1_aig_witness_out                  false
% 2.67/1.02  --bmc1_verbose                          false
% 2.67/1.02  --bmc1_dump_clauses_tptp                false
% 2.67/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.02  --bmc1_dump_file                        -
% 2.67/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.02  --bmc1_ucm_extend_mode                  1
% 2.67/1.02  --bmc1_ucm_init_mode                    2
% 2.67/1.02  --bmc1_ucm_cone_mode                    none
% 2.67/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.02  --bmc1_ucm_relax_model                  4
% 2.67/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.02  --bmc1_ucm_layered_model                none
% 2.67/1.02  --bmc1_ucm_max_lemma_size               10
% 2.67/1.02  
% 2.67/1.02  ------ AIG Options
% 2.67/1.02  
% 2.67/1.02  --aig_mode                              false
% 2.67/1.02  
% 2.67/1.02  ------ Instantiation Options
% 2.67/1.02  
% 2.67/1.02  --instantiation_flag                    true
% 2.67/1.02  --inst_sos_flag                         false
% 2.67/1.02  --inst_sos_phase                        true
% 2.67/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.02  --inst_lit_sel_side                     num_symb
% 2.67/1.02  --inst_solver_per_active                1400
% 2.67/1.02  --inst_solver_calls_frac                1.
% 2.67/1.02  --inst_passive_queue_type               priority_queues
% 2.67/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.02  --inst_passive_queues_freq              [25;2]
% 2.67/1.02  --inst_dismatching                      true
% 2.67/1.02  --inst_eager_unprocessed_to_passive     true
% 2.67/1.02  --inst_prop_sim_given                   true
% 2.67/1.02  --inst_prop_sim_new                     false
% 2.67/1.02  --inst_subs_new                         false
% 2.67/1.02  --inst_eq_res_simp                      false
% 2.67/1.02  --inst_subs_given                       false
% 2.67/1.02  --inst_orphan_elimination               true
% 2.67/1.02  --inst_learning_loop_flag               true
% 2.67/1.02  --inst_learning_start                   3000
% 2.67/1.02  --inst_learning_factor                  2
% 2.67/1.02  --inst_start_prop_sim_after_learn       3
% 2.67/1.02  --inst_sel_renew                        solver
% 2.67/1.02  --inst_lit_activity_flag                true
% 2.67/1.02  --inst_restr_to_given                   false
% 2.67/1.02  --inst_activity_threshold               500
% 2.67/1.02  --inst_out_proof                        true
% 2.67/1.02  
% 2.67/1.02  ------ Resolution Options
% 2.67/1.02  
% 2.67/1.02  --resolution_flag                       true
% 2.67/1.02  --res_lit_sel                           adaptive
% 2.67/1.02  --res_lit_sel_side                      none
% 2.67/1.02  --res_ordering                          kbo
% 2.67/1.02  --res_to_prop_solver                    active
% 2.67/1.02  --res_prop_simpl_new                    false
% 2.67/1.02  --res_prop_simpl_given                  true
% 2.67/1.02  --res_passive_queue_type                priority_queues
% 2.67/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.02  --res_passive_queues_freq               [15;5]
% 2.67/1.02  --res_forward_subs                      full
% 2.67/1.02  --res_backward_subs                     full
% 2.67/1.02  --res_forward_subs_resolution           true
% 2.67/1.02  --res_backward_subs_resolution          true
% 2.67/1.02  --res_orphan_elimination                true
% 2.67/1.02  --res_time_limit                        2.
% 2.67/1.02  --res_out_proof                         true
% 2.67/1.02  
% 2.67/1.02  ------ Superposition Options
% 2.67/1.02  
% 2.67/1.02  --superposition_flag                    true
% 2.67/1.02  --sup_passive_queue_type                priority_queues
% 2.67/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.02  --demod_completeness_check              fast
% 2.67/1.02  --demod_use_ground                      true
% 2.67/1.02  --sup_to_prop_solver                    passive
% 2.67/1.02  --sup_prop_simpl_new                    true
% 2.67/1.02  --sup_prop_simpl_given                  true
% 2.67/1.02  --sup_fun_splitting                     false
% 2.67/1.02  --sup_smt_interval                      50000
% 2.67/1.02  
% 2.67/1.02  ------ Superposition Simplification Setup
% 2.67/1.02  
% 2.67/1.02  --sup_indices_passive                   []
% 2.67/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.02  --sup_full_bw                           [BwDemod]
% 2.67/1.02  --sup_immed_triv                        [TrivRules]
% 2.67/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.02  --sup_immed_bw_main                     []
% 2.67/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.02  
% 2.67/1.02  ------ Combination Options
% 2.67/1.02  
% 2.67/1.02  --comb_res_mult                         3
% 2.67/1.02  --comb_sup_mult                         2
% 2.67/1.02  --comb_inst_mult                        10
% 2.67/1.02  
% 2.67/1.02  ------ Debug Options
% 2.67/1.02  
% 2.67/1.02  --dbg_backtrace                         false
% 2.67/1.02  --dbg_dump_prop_clauses                 false
% 2.67/1.02  --dbg_dump_prop_clauses_file            -
% 2.67/1.02  --dbg_out_stat                          false
% 2.67/1.02  ------ Parsing...
% 2.67/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.67/1.02  
% 2.67/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.67/1.02  
% 2.67/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.67/1.02  
% 2.67/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.67/1.02  ------ Proving...
% 2.67/1.02  ------ Problem Properties 
% 2.67/1.02  
% 2.67/1.02  
% 2.67/1.02  clauses                                 36
% 2.67/1.02  conjectures                             3
% 2.67/1.02  EPR                                     5
% 2.67/1.02  Horn                                    31
% 2.67/1.02  unary                                   5
% 2.67/1.02  binary                                  15
% 2.67/1.02  lits                                    95
% 2.67/1.02  lits eq                                 35
% 2.67/1.02  fd_pure                                 0
% 2.67/1.02  fd_pseudo                               0
% 2.67/1.02  fd_cond                                 2
% 2.67/1.02  fd_pseudo_cond                          0
% 2.67/1.02  AC symbols                              0
% 2.67/1.02  
% 2.67/1.02  ------ Schedule dynamic 5 is on 
% 2.67/1.02  
% 2.67/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.67/1.02  
% 2.67/1.02  
% 2.67/1.02  ------ 
% 2.67/1.02  Current options:
% 2.67/1.02  ------ 
% 2.67/1.02  
% 2.67/1.02  ------ Input Options
% 2.67/1.02  
% 2.67/1.02  --out_options                           all
% 2.67/1.02  --tptp_safe_out                         true
% 2.67/1.02  --problem_path                          ""
% 2.67/1.02  --include_path                          ""
% 2.67/1.02  --clausifier                            res/vclausify_rel
% 2.67/1.02  --clausifier_options                    --mode clausify
% 2.67/1.02  --stdin                                 false
% 2.67/1.02  --stats_out                             all
% 2.67/1.02  
% 2.67/1.02  ------ General Options
% 2.67/1.02  
% 2.67/1.02  --fof                                   false
% 2.67/1.02  --time_out_real                         305.
% 2.67/1.02  --time_out_virtual                      -1.
% 2.67/1.02  --symbol_type_check                     false
% 2.67/1.02  --clausify_out                          false
% 2.67/1.02  --sig_cnt_out                           false
% 2.67/1.02  --trig_cnt_out                          false
% 2.67/1.02  --trig_cnt_out_tolerance                1.
% 2.67/1.02  --trig_cnt_out_sk_spl                   false
% 2.67/1.02  --abstr_cl_out                          false
% 2.67/1.02  
% 2.67/1.02  ------ Global Options
% 2.67/1.02  
% 2.67/1.02  --schedule                              default
% 2.67/1.02  --add_important_lit                     false
% 2.67/1.02  --prop_solver_per_cl                    1000
% 2.67/1.02  --min_unsat_core                        false
% 2.67/1.02  --soft_assumptions                      false
% 2.67/1.02  --soft_lemma_size                       3
% 2.67/1.02  --prop_impl_unit_size                   0
% 2.67/1.02  --prop_impl_unit                        []
% 2.67/1.02  --share_sel_clauses                     true
% 2.67/1.02  --reset_solvers                         false
% 2.67/1.02  --bc_imp_inh                            [conj_cone]
% 2.67/1.02  --conj_cone_tolerance                   3.
% 2.67/1.02  --extra_neg_conj                        none
% 2.67/1.02  --large_theory_mode                     true
% 2.67/1.02  --prolific_symb_bound                   200
% 2.67/1.02  --lt_threshold                          2000
% 2.67/1.02  --clause_weak_htbl                      true
% 2.67/1.02  --gc_record_bc_elim                     false
% 2.67/1.02  
% 2.67/1.02  ------ Preprocessing Options
% 2.67/1.02  
% 2.67/1.02  --preprocessing_flag                    true
% 2.67/1.02  --time_out_prep_mult                    0.1
% 2.67/1.02  --splitting_mode                        input
% 2.67/1.02  --splitting_grd                         true
% 2.67/1.02  --splitting_cvd                         false
% 2.67/1.02  --splitting_cvd_svl                     false
% 2.67/1.02  --splitting_nvd                         32
% 2.67/1.02  --sub_typing                            true
% 2.67/1.02  --prep_gs_sim                           true
% 2.67/1.02  --prep_unflatten                        true
% 2.67/1.02  --prep_res_sim                          true
% 2.67/1.02  --prep_upred                            true
% 2.67/1.02  --prep_sem_filter                       exhaustive
% 2.67/1.02  --prep_sem_filter_out                   false
% 2.67/1.02  --pred_elim                             true
% 2.67/1.02  --res_sim_input                         true
% 2.67/1.02  --eq_ax_congr_red                       true
% 2.67/1.02  --pure_diseq_elim                       true
% 2.67/1.02  --brand_transform                       false
% 2.67/1.02  --non_eq_to_eq                          false
% 2.67/1.02  --prep_def_merge                        true
% 2.67/1.02  --prep_def_merge_prop_impl              false
% 2.67/1.02  --prep_def_merge_mbd                    true
% 2.67/1.02  --prep_def_merge_tr_red                 false
% 2.67/1.02  --prep_def_merge_tr_cl                  false
% 2.67/1.02  --smt_preprocessing                     true
% 2.67/1.02  --smt_ac_axioms                         fast
% 2.67/1.02  --preprocessed_out                      false
% 2.67/1.02  --preprocessed_stats                    false
% 2.67/1.02  
% 2.67/1.02  ------ Abstraction refinement Options
% 2.67/1.02  
% 2.67/1.02  --abstr_ref                             []
% 2.67/1.02  --abstr_ref_prep                        false
% 2.67/1.02  --abstr_ref_until_sat                   false
% 2.67/1.02  --abstr_ref_sig_restrict                funpre
% 2.67/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.67/1.02  --abstr_ref_under                       []
% 2.67/1.02  
% 2.67/1.02  ------ SAT Options
% 2.67/1.02  
% 2.67/1.02  --sat_mode                              false
% 2.67/1.02  --sat_fm_restart_options                ""
% 2.67/1.02  --sat_gr_def                            false
% 2.67/1.02  --sat_epr_types                         true
% 2.67/1.02  --sat_non_cyclic_types                  false
% 2.67/1.02  --sat_finite_models                     false
% 2.67/1.02  --sat_fm_lemmas                         false
% 2.67/1.02  --sat_fm_prep                           false
% 2.67/1.02  --sat_fm_uc_incr                        true
% 2.67/1.02  --sat_out_model                         small
% 2.67/1.02  --sat_out_clauses                       false
% 2.67/1.02  
% 2.67/1.02  ------ QBF Options
% 2.67/1.02  
% 2.67/1.02  --qbf_mode                              false
% 2.67/1.02  --qbf_elim_univ                         false
% 2.67/1.02  --qbf_dom_inst                          none
% 2.67/1.02  --qbf_dom_pre_inst                      false
% 2.67/1.02  --qbf_sk_in                             false
% 2.67/1.02  --qbf_pred_elim                         true
% 2.67/1.02  --qbf_split                             512
% 2.67/1.02  
% 2.67/1.02  ------ BMC1 Options
% 2.67/1.02  
% 2.67/1.02  --bmc1_incremental                      false
% 2.67/1.02  --bmc1_axioms                           reachable_all
% 2.67/1.02  --bmc1_min_bound                        0
% 2.67/1.02  --bmc1_max_bound                        -1
% 2.67/1.02  --bmc1_max_bound_default                -1
% 2.67/1.02  --bmc1_symbol_reachability              true
% 2.67/1.02  --bmc1_property_lemmas                  false
% 2.67/1.02  --bmc1_k_induction                      false
% 2.67/1.02  --bmc1_non_equiv_states                 false
% 2.67/1.02  --bmc1_deadlock                         false
% 2.67/1.02  --bmc1_ucm                              false
% 2.67/1.02  --bmc1_add_unsat_core                   none
% 2.67/1.02  --bmc1_unsat_core_children              false
% 2.67/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.67/1.02  --bmc1_out_stat                         full
% 2.67/1.02  --bmc1_ground_init                      false
% 2.67/1.02  --bmc1_pre_inst_next_state              false
% 2.67/1.02  --bmc1_pre_inst_state                   false
% 2.67/1.02  --bmc1_pre_inst_reach_state             false
% 2.67/1.02  --bmc1_out_unsat_core                   false
% 2.67/1.02  --bmc1_aig_witness_out                  false
% 2.67/1.02  --bmc1_verbose                          false
% 2.67/1.02  --bmc1_dump_clauses_tptp                false
% 2.67/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.67/1.02  --bmc1_dump_file                        -
% 2.67/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.67/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.67/1.02  --bmc1_ucm_extend_mode                  1
% 2.67/1.02  --bmc1_ucm_init_mode                    2
% 2.67/1.02  --bmc1_ucm_cone_mode                    none
% 2.67/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.67/1.02  --bmc1_ucm_relax_model                  4
% 2.67/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.67/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.67/1.02  --bmc1_ucm_layered_model                none
% 2.67/1.02  --bmc1_ucm_max_lemma_size               10
% 2.67/1.02  
% 2.67/1.02  ------ AIG Options
% 2.67/1.02  
% 2.67/1.02  --aig_mode                              false
% 2.67/1.02  
% 2.67/1.02  ------ Instantiation Options
% 2.67/1.02  
% 2.67/1.02  --instantiation_flag                    true
% 2.67/1.02  --inst_sos_flag                         false
% 2.67/1.02  --inst_sos_phase                        true
% 2.67/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.67/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.67/1.02  --inst_lit_sel_side                     none
% 2.67/1.02  --inst_solver_per_active                1400
% 2.67/1.02  --inst_solver_calls_frac                1.
% 2.67/1.02  --inst_passive_queue_type               priority_queues
% 2.67/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.67/1.02  --inst_passive_queues_freq              [25;2]
% 2.67/1.02  --inst_dismatching                      true
% 2.67/1.02  --inst_eager_unprocessed_to_passive     true
% 2.67/1.02  --inst_prop_sim_given                   true
% 2.67/1.02  --inst_prop_sim_new                     false
% 2.67/1.02  --inst_subs_new                         false
% 2.67/1.02  --inst_eq_res_simp                      false
% 2.67/1.02  --inst_subs_given                       false
% 2.67/1.02  --inst_orphan_elimination               true
% 2.67/1.02  --inst_learning_loop_flag               true
% 2.67/1.02  --inst_learning_start                   3000
% 2.67/1.02  --inst_learning_factor                  2
% 2.67/1.02  --inst_start_prop_sim_after_learn       3
% 2.67/1.02  --inst_sel_renew                        solver
% 2.67/1.02  --inst_lit_activity_flag                true
% 2.67/1.02  --inst_restr_to_given                   false
% 2.67/1.02  --inst_activity_threshold               500
% 2.67/1.02  --inst_out_proof                        true
% 2.67/1.02  
% 2.67/1.02  ------ Resolution Options
% 2.67/1.02  
% 2.67/1.02  --resolution_flag                       false
% 2.67/1.02  --res_lit_sel                           adaptive
% 2.67/1.02  --res_lit_sel_side                      none
% 2.67/1.02  --res_ordering                          kbo
% 2.67/1.02  --res_to_prop_solver                    active
% 2.67/1.02  --res_prop_simpl_new                    false
% 2.67/1.02  --res_prop_simpl_given                  true
% 2.67/1.02  --res_passive_queue_type                priority_queues
% 2.67/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.67/1.02  --res_passive_queues_freq               [15;5]
% 2.67/1.02  --res_forward_subs                      full
% 2.67/1.02  --res_backward_subs                     full
% 2.67/1.02  --res_forward_subs_resolution           true
% 2.67/1.02  --res_backward_subs_resolution          true
% 2.67/1.02  --res_orphan_elimination                true
% 2.67/1.02  --res_time_limit                        2.
% 2.67/1.02  --res_out_proof                         true
% 2.67/1.02  
% 2.67/1.02  ------ Superposition Options
% 2.67/1.02  
% 2.67/1.02  --superposition_flag                    true
% 2.67/1.02  --sup_passive_queue_type                priority_queues
% 2.67/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.67/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.67/1.02  --demod_completeness_check              fast
% 2.67/1.02  --demod_use_ground                      true
% 2.67/1.02  --sup_to_prop_solver                    passive
% 2.67/1.02  --sup_prop_simpl_new                    true
% 2.67/1.02  --sup_prop_simpl_given                  true
% 2.67/1.02  --sup_fun_splitting                     false
% 2.67/1.02  --sup_smt_interval                      50000
% 2.67/1.02  
% 2.67/1.02  ------ Superposition Simplification Setup
% 2.67/1.02  
% 2.67/1.02  --sup_indices_passive                   []
% 2.67/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.67/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.67/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.02  --sup_full_bw                           [BwDemod]
% 2.67/1.02  --sup_immed_triv                        [TrivRules]
% 2.67/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.67/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.02  --sup_immed_bw_main                     []
% 2.67/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.67/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.67/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.67/1.02  
% 2.67/1.02  ------ Combination Options
% 2.67/1.02  
% 2.67/1.02  --comb_res_mult                         3
% 2.67/1.02  --comb_sup_mult                         2
% 2.67/1.02  --comb_inst_mult                        10
% 2.67/1.02  
% 2.67/1.02  ------ Debug Options
% 2.67/1.02  
% 2.67/1.02  --dbg_backtrace                         false
% 2.67/1.02  --dbg_dump_prop_clauses                 false
% 2.67/1.02  --dbg_dump_prop_clauses_file            -
% 2.67/1.02  --dbg_out_stat                          false
% 2.67/1.02  
% 2.67/1.02  
% 2.67/1.02  
% 2.67/1.02  
% 2.67/1.02  ------ Proving...
% 2.67/1.02  
% 2.67/1.02  
% 2.67/1.02  % SZS status Theorem for theBenchmark.p
% 2.67/1.02  
% 2.67/1.02   Resolution empty clause
% 2.67/1.02  
% 2.67/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.67/1.02  
% 2.67/1.02  fof(f18,axiom,(
% 2.67/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f43,plain,(
% 2.67/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.02    inference(ennf_transformation,[],[f18])).
% 2.67/1.02  
% 2.67/1.02  fof(f44,plain,(
% 2.67/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.02    inference(flattening,[],[f43])).
% 2.67/1.02  
% 2.67/1.02  fof(f49,plain,(
% 2.67/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.02    inference(nnf_transformation,[],[f44])).
% 2.67/1.02  
% 2.67/1.02  fof(f74,plain,(
% 2.67/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.02    inference(cnf_transformation,[],[f49])).
% 2.67/1.02  
% 2.67/1.02  fof(f20,conjecture,(
% 2.67/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f21,negated_conjecture,(
% 2.67/1.02    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.67/1.02    inference(negated_conjecture,[],[f20])).
% 2.67/1.02  
% 2.67/1.02  fof(f47,plain,(
% 2.67/1.02    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.67/1.02    inference(ennf_transformation,[],[f21])).
% 2.67/1.02  
% 2.67/1.02  fof(f48,plain,(
% 2.67/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.67/1.02    inference(flattening,[],[f47])).
% 2.67/1.02  
% 2.67/1.02  fof(f50,plain,(
% 2.67/1.02    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.67/1.02    introduced(choice_axiom,[])).
% 2.67/1.02  
% 2.67/1.02  fof(f51,plain,(
% 2.67/1.02    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.67/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f50])).
% 2.67/1.02  
% 2.67/1.02  fof(f84,plain,(
% 2.67/1.02    v1_funct_2(sK2,sK0,sK1)),
% 2.67/1.02    inference(cnf_transformation,[],[f51])).
% 2.67/1.02  
% 2.67/1.02  fof(f85,plain,(
% 2.67/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.67/1.02    inference(cnf_transformation,[],[f51])).
% 2.67/1.02  
% 2.67/1.02  fof(f14,axiom,(
% 2.67/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f38,plain,(
% 2.67/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.02    inference(ennf_transformation,[],[f14])).
% 2.67/1.02  
% 2.67/1.02  fof(f69,plain,(
% 2.67/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.02    inference(cnf_transformation,[],[f38])).
% 2.67/1.02  
% 2.67/1.02  fof(f13,axiom,(
% 2.67/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f37,plain,(
% 2.67/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.02    inference(ennf_transformation,[],[f13])).
% 2.67/1.02  
% 2.67/1.02  fof(f68,plain,(
% 2.67/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.02    inference(cnf_transformation,[],[f37])).
% 2.67/1.02  
% 2.67/1.02  fof(f12,axiom,(
% 2.67/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f35,plain,(
% 2.67/1.02    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/1.02    inference(ennf_transformation,[],[f12])).
% 2.67/1.02  
% 2.67/1.02  fof(f36,plain,(
% 2.67/1.02    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/1.02    inference(flattening,[],[f35])).
% 2.67/1.02  
% 2.67/1.02  fof(f67,plain,(
% 2.67/1.02    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.02    inference(cnf_transformation,[],[f36])).
% 2.67/1.02  
% 2.67/1.02  fof(f86,plain,(
% 2.67/1.02    v2_funct_1(sK2)),
% 2.67/1.02    inference(cnf_transformation,[],[f51])).
% 2.67/1.02  
% 2.67/1.02  fof(f83,plain,(
% 2.67/1.02    v1_funct_1(sK2)),
% 2.67/1.02    inference(cnf_transformation,[],[f51])).
% 2.67/1.02  
% 2.67/1.02  fof(f10,axiom,(
% 2.67/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f31,plain,(
% 2.67/1.02    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/1.02    inference(ennf_transformation,[],[f10])).
% 2.67/1.02  
% 2.67/1.02  fof(f32,plain,(
% 2.67/1.02    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/1.02    inference(flattening,[],[f31])).
% 2.67/1.02  
% 2.67/1.02  fof(f63,plain,(
% 2.67/1.02    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.02    inference(cnf_transformation,[],[f32])).
% 2.67/1.02  
% 2.67/1.02  fof(f19,axiom,(
% 2.67/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f45,plain,(
% 2.67/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/1.02    inference(ennf_transformation,[],[f19])).
% 2.67/1.02  
% 2.67/1.02  fof(f46,plain,(
% 2.67/1.02    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/1.02    inference(flattening,[],[f45])).
% 2.67/1.02  
% 2.67/1.02  fof(f82,plain,(
% 2.67/1.02    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.02    inference(cnf_transformation,[],[f46])).
% 2.67/1.02  
% 2.67/1.02  fof(f15,axiom,(
% 2.67/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f39,plain,(
% 2.67/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.02    inference(ennf_transformation,[],[f15])).
% 2.67/1.02  
% 2.67/1.02  fof(f70,plain,(
% 2.67/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.02    inference(cnf_transformation,[],[f39])).
% 2.67/1.02  
% 2.67/1.02  fof(f87,plain,(
% 2.67/1.02    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.67/1.02    inference(cnf_transformation,[],[f51])).
% 2.67/1.02  
% 2.67/1.02  fof(f66,plain,(
% 2.67/1.02    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.02    inference(cnf_transformation,[],[f36])).
% 2.67/1.02  
% 2.67/1.02  fof(f11,axiom,(
% 2.67/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f33,plain,(
% 2.67/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.67/1.02    inference(ennf_transformation,[],[f11])).
% 2.67/1.02  
% 2.67/1.02  fof(f34,plain,(
% 2.67/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.67/1.02    inference(flattening,[],[f33])).
% 2.67/1.02  
% 2.67/1.02  fof(f64,plain,(
% 2.67/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.02    inference(cnf_transformation,[],[f34])).
% 2.67/1.02  
% 2.67/1.02  fof(f65,plain,(
% 2.67/1.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.02    inference(cnf_transformation,[],[f34])).
% 2.67/1.02  
% 2.67/1.02  fof(f81,plain,(
% 2.67/1.02    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.67/1.02    inference(cnf_transformation,[],[f46])).
% 2.67/1.02  
% 2.67/1.02  fof(f88,plain,(
% 2.67/1.02    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.67/1.02    inference(cnf_transformation,[],[f51])).
% 2.67/1.02  
% 2.67/1.02  fof(f77,plain,(
% 2.67/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.02    inference(cnf_transformation,[],[f49])).
% 2.67/1.02  
% 2.67/1.02  fof(f92,plain,(
% 2.67/1.02    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.67/1.02    inference(equality_resolution,[],[f77])).
% 2.67/1.02  
% 2.67/1.02  fof(f17,axiom,(
% 2.67/1.02    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f42,plain,(
% 2.67/1.02    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.67/1.02    inference(ennf_transformation,[],[f17])).
% 2.67/1.02  
% 2.67/1.02  fof(f73,plain,(
% 2.67/1.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.67/1.02    inference(cnf_transformation,[],[f42])).
% 2.67/1.02  
% 2.67/1.02  fof(f16,axiom,(
% 2.67/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f40,plain,(
% 2.67/1.02    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.02    inference(ennf_transformation,[],[f16])).
% 2.67/1.02  
% 2.67/1.02  fof(f41,plain,(
% 2.67/1.02    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.67/1.02    inference(flattening,[],[f40])).
% 2.67/1.02  
% 2.67/1.02  fof(f72,plain,(
% 2.67/1.02    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.02    inference(cnf_transformation,[],[f41])).
% 2.67/1.02  
% 2.67/1.02  fof(f75,plain,(
% 2.67/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.67/1.02    inference(cnf_transformation,[],[f49])).
% 2.67/1.02  
% 2.67/1.02  fof(f93,plain,(
% 2.67/1.02    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.67/1.02    inference(equality_resolution,[],[f75])).
% 2.67/1.02  
% 2.67/1.02  fof(f1,axiom,(
% 2.67/1.02    v1_xboole_0(k1_xboole_0)),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f52,plain,(
% 2.67/1.02    v1_xboole_0(k1_xboole_0)),
% 2.67/1.02    inference(cnf_transformation,[],[f1])).
% 2.67/1.02  
% 2.67/1.02  fof(f6,axiom,(
% 2.67/1.02    ! [X0] : (v1_xboole_0(X0) => (v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f25,plain,(
% 2.67/1.02    ! [X0] : ((v1_relat_1(k4_relat_1(X0)) & v1_xboole_0(k4_relat_1(X0))) | ~v1_xboole_0(X0))),
% 2.67/1.02    inference(ennf_transformation,[],[f6])).
% 2.67/1.02  
% 2.67/1.02  fof(f56,plain,(
% 2.67/1.02    ( ! [X0] : (v1_xboole_0(k4_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.67/1.02    inference(cnf_transformation,[],[f25])).
% 2.67/1.02  
% 2.67/1.02  fof(f2,axiom,(
% 2.67/1.02    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f23,plain,(
% 2.67/1.02    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.67/1.02    inference(ennf_transformation,[],[f2])).
% 2.67/1.02  
% 2.67/1.02  fof(f53,plain,(
% 2.67/1.02    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.67/1.02    inference(cnf_transformation,[],[f23])).
% 2.67/1.02  
% 2.67/1.02  fof(f7,axiom,(
% 2.67/1.02    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k2_relat_1(X0)))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f26,plain,(
% 2.67/1.02    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 2.67/1.02    inference(ennf_transformation,[],[f7])).
% 2.67/1.02  
% 2.67/1.02  fof(f27,plain,(
% 2.67/1.02    ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 2.67/1.02    inference(flattening,[],[f26])).
% 2.67/1.02  
% 2.67/1.02  fof(f58,plain,(
% 2.67/1.02    ( ! [X0] : (~v1_xboole_0(k2_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 2.67/1.02    inference(cnf_transformation,[],[f27])).
% 2.67/1.02  
% 2.67/1.02  fof(f3,axiom,(
% 2.67/1.02    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 2.67/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.67/1.02  
% 2.67/1.02  fof(f54,plain,(
% 2.67/1.02    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 2.67/1.02    inference(cnf_transformation,[],[f3])).
% 2.67/1.02  
% 2.67/1.02  cnf(c_27,plain,
% 2.67/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.67/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.67/1.02      | k1_xboole_0 = X2 ),
% 2.67/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_35,negated_conjecture,
% 2.67/1.02      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.67/1.02      inference(cnf_transformation,[],[f84]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1261,plain,
% 2.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.67/1.02      | sK0 != X1
% 2.67/1.02      | sK1 != X2
% 2.67/1.02      | sK2 != X0
% 2.67/1.02      | k1_xboole_0 = X2 ),
% 2.67/1.02      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1262,plain,
% 2.67/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.67/1.02      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.67/1.02      | k1_xboole_0 = sK1 ),
% 2.67/1.02      inference(unflattening,[status(thm)],[c_1261]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_34,negated_conjecture,
% 2.67/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.67/1.02      inference(cnf_transformation,[],[f85]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1264,plain,
% 2.67/1.02      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.67/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1262,c_34]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2311,plain,
% 2.67/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_17,plain,
% 2.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.67/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2314,plain,
% 2.67/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.67/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3860,plain,
% 2.67/1.02      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_2311,c_2314]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3983,plain,
% 2.67/1.02      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_1264,c_3860]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_16,plain,
% 2.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.67/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2315,plain,
% 2.67/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.67/1.02      | v1_relat_1(X0) = iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3230,plain,
% 2.67/1.02      ( v1_relat_1(sK2) = iProver_top ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_2311,c_2315]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_14,plain,
% 2.67/1.02      ( ~ v2_funct_1(X0)
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_relat_1(X0)
% 2.67/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.67/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_33,negated_conjecture,
% 2.67/1.02      ( v2_funct_1(sK2) ),
% 2.67/1.02      inference(cnf_transformation,[],[f86]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_479,plain,
% 2.67/1.02      ( ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_relat_1(X0)
% 2.67/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.67/1.02      | sK2 != X0 ),
% 2.67/1.02      inference(resolution_lifted,[status(thm)],[c_14,c_33]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_480,plain,
% 2.67/1.02      ( ~ v1_funct_1(sK2)
% 2.67/1.02      | ~ v1_relat_1(sK2)
% 2.67/1.02      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.02      inference(unflattening,[status(thm)],[c_479]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_36,negated_conjecture,
% 2.67/1.02      ( v1_funct_1(sK2) ),
% 2.67/1.02      inference(cnf_transformation,[],[f83]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_482,plain,
% 2.67/1.02      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.02      inference(global_propositional_subsumption,[status(thm)],[c_480,c_36]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2305,plain,
% 2.67/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.67/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_482]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3237,plain,
% 2.67/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_3230,c_2305]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_11,plain,
% 2.67/1.02      ( ~ v2_funct_1(X0)
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_relat_1(X0)
% 2.67/1.02      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 2.67/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_493,plain,
% 2.67/1.02      ( ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_relat_1(X0)
% 2.67/1.02      | k2_funct_1(X0) = k4_relat_1(X0)
% 2.67/1.02      | sK2 != X0 ),
% 2.67/1.02      inference(resolution_lifted,[status(thm)],[c_11,c_33]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_494,plain,
% 2.67/1.02      ( ~ v1_funct_1(sK2)
% 2.67/1.02      | ~ v1_relat_1(sK2)
% 2.67/1.02      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.67/1.02      inference(unflattening,[status(thm)],[c_493]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_496,plain,
% 2.67/1.02      ( ~ v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.67/1.02      inference(global_propositional_subsumption,[status(thm)],[c_494,c_36]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2304,plain,
% 2.67/1.02      ( k2_funct_1(sK2) = k4_relat_1(sK2) | v1_relat_1(sK2) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_496]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3238,plain,
% 2.67/1.02      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_3230,c_2304]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3241,plain,
% 2.67/1.02      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.67/1.02      inference(light_normalisation,[status(thm)],[c_3237,c_3238]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_28,plain,
% 2.67/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_relat_1(X0) ),
% 2.67/1.02      inference(cnf_transformation,[],[f82]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2312,plain,
% 2.67/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.67/1.02      | v1_funct_1(X0) != iProver_top
% 2.67/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4468,plain,
% 2.67/1.02      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k4_relat_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 2.67/1.02      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.67/1.02      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_3241,c_2312]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_18,plain,
% 2.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.67/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2313,plain,
% 2.67/1.02      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.67/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3763,plain,
% 2.67/1.02      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_2311,c_2313]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_32,negated_conjecture,
% 2.67/1.02      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.67/1.02      inference(cnf_transformation,[],[f87]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3765,plain,
% 2.67/1.02      ( k2_relat_1(sK2) = sK1 ),
% 2.67/1.02      inference(light_normalisation,[status(thm)],[c_3763,c_32]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_15,plain,
% 2.67/1.02      ( ~ v2_funct_1(X0)
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_relat_1(X0)
% 2.67/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.67/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_465,plain,
% 2.67/1.02      ( ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_relat_1(X0)
% 2.67/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.67/1.02      | sK2 != X0 ),
% 2.67/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_33]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_466,plain,
% 2.67/1.02      ( ~ v1_funct_1(sK2)
% 2.67/1.02      | ~ v1_relat_1(sK2)
% 2.67/1.02      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/1.02      inference(unflattening,[status(thm)],[c_465]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_468,plain,
% 2.67/1.02      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/1.02      inference(global_propositional_subsumption,[status(thm)],[c_466,c_36]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2306,plain,
% 2.67/1.02      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.67/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3236,plain,
% 2.67/1.02      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_3230,c_2306]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3244,plain,
% 2.67/1.02      ( k1_relat_1(k4_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.67/1.02      inference(light_normalisation,[status(thm)],[c_3236,c_3238]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3771,plain,
% 2.67/1.02      ( k1_relat_1(k4_relat_1(sK2)) = sK1 ),
% 2.67/1.02      inference(demodulation,[status(thm)],[c_3765,c_3244]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4481,plain,
% 2.67/1.02      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.67/1.02      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 2.67/1.02      | v1_relat_1(k4_relat_1(sK2)) != iProver_top ),
% 2.67/1.02      inference(light_normalisation,[status(thm)],[c_4468,c_3771]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_37,plain,
% 2.67/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_39,plain,
% 2.67/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2601,plain,
% 2.67/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(sK2) ),
% 2.67/1.02      inference(instantiation,[status(thm)],[c_16]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2759,plain,
% 2.67/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.67/1.02      | v1_relat_1(sK2) ),
% 2.67/1.02      inference(instantiation,[status(thm)],[c_2601]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2760,plain,
% 2.67/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.67/1.02      | v1_relat_1(sK2) = iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_2759]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_13,plain,
% 2.67/1.02      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.67/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2316,plain,
% 2.67/1.02      ( v1_funct_1(X0) != iProver_top
% 2.67/1.02      | v1_relat_1(X0) != iProver_top
% 2.67/1.02      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3870,plain,
% 2.67/1.02      ( v1_funct_1(sK2) != iProver_top
% 2.67/1.02      | v1_relat_1(k4_relat_1(sK2)) = iProver_top
% 2.67/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_3238,c_2316]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_12,plain,
% 2.67/1.02      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.67/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2317,plain,
% 2.67/1.02      ( v1_funct_1(X0) != iProver_top
% 2.67/1.02      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 2.67/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4401,plain,
% 2.67/1.02      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top
% 2.67/1.02      | v1_funct_1(sK2) != iProver_top
% 2.67/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_3238,c_2317]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4825,plain,
% 2.67/1.02      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 2.67/1.02      inference(global_propositional_subsumption,
% 2.67/1.02                [status(thm)],
% 2.67/1.02                [c_4481,c_37,c_39,c_2760,c_3870,c_4401]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4832,plain,
% 2.67/1.02      ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(k4_relat_1(sK2)) ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_4825,c_2314]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4838,plain,
% 2.67/1.02      ( k1_relset_1(sK1,k1_relat_1(sK2),k4_relat_1(sK2)) = sK1 ),
% 2.67/1.02      inference(light_normalisation,[status(thm)],[c_4832,c_3771]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4846,plain,
% 2.67/1.02      ( k1_relset_1(sK1,sK0,k4_relat_1(sK2)) = sK1 | sK1 = k1_xboole_0 ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_3983,c_4838]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_29,plain,
% 2.67/1.02      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_relat_1(X0) ),
% 2.67/1.02      inference(cnf_transformation,[],[f81]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_31,negated_conjecture,
% 2.67/1.02      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.67/1.02      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/1.02      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.67/1.02      inference(cnf_transformation,[],[f88]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1378,plain,
% 2.67/1.02      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/1.02      | ~ v1_relat_1(X0)
% 2.67/1.02      | k1_relat_1(X0) != sK1
% 2.67/1.02      | k2_funct_1(sK2) != X0
% 2.67/1.02      | k2_relat_1(X0) != sK0 ),
% 2.67/1.02      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1379,plain,
% 2.67/1.02      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/1.02      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.67/1.02      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/1.02      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.67/1.02      inference(unflattening,[status(thm)],[c_1378]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1391,plain,
% 2.67/1.02      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/1.02      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/1.02      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.67/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_1379,c_16]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2293,plain,
% 2.67/1.02      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/1.02      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.67/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_1391]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1380,plain,
% 2.67/1.02      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/1.02      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.67/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.67/1.02      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_1379]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2594,plain,
% 2.67/1.02      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 2.67/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2595,plain,
% 2.67/1.02      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.67/1.02      | v1_funct_1(sK2) != iProver_top
% 2.67/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_2594]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2909,plain,
% 2.67/1.02      ( ~ v1_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) ),
% 2.67/1.02      inference(instantiation,[status(thm)],[c_13]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2910,plain,
% 2.67/1.02      ( v1_funct_1(sK2) != iProver_top
% 2.67/1.02      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.67/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_2909]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2918,plain,
% 2.67/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/1.02      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.67/1.02      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.67/1.02      inference(global_propositional_subsumption,
% 2.67/1.02                [status(thm)],
% 2.67/1.02                [c_2293,c_37,c_39,c_1380,c_2595,c_2760,c_2910]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2919,plain,
% 2.67/1.02      ( k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.67/1.02      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.67/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/1.02      inference(renaming,[status(thm)],[c_2918]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3339,plain,
% 2.67/1.02      ( k1_relat_1(k4_relat_1(sK2)) != sK1
% 2.67/1.02      | k2_relat_1(k4_relat_1(sK2)) != sK0
% 2.67/1.02      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/1.02      inference(demodulation,[status(thm)],[c_3238,c_2919]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4293,plain,
% 2.67/1.02      ( k2_relat_1(k4_relat_1(sK2)) != sK0
% 2.67/1.02      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/1.02      inference(global_propositional_subsumption,[status(thm)],[c_3339,c_3771]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4297,plain,
% 2.67/1.02      ( k1_relat_1(sK2) != sK0
% 2.67/1.02      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/1.02      inference(light_normalisation,[status(thm)],[c_4293,c_3241]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_24,plain,
% 2.67/1.02      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.67/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.67/1.02      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.67/1.02      inference(cnf_transformation,[],[f92]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1347,plain,
% 2.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.67/1.02      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/1.02      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.67/1.02      | k2_funct_1(sK2) != X0
% 2.67/1.02      | sK0 != X1
% 2.67/1.02      | sK1 != k1_xboole_0 ),
% 2.67/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1348,plain,
% 2.67/1.02      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/1.02      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.67/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/1.02      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.67/1.02      | sK1 != k1_xboole_0 ),
% 2.67/1.02      inference(unflattening,[status(thm)],[c_1347]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_21,plain,
% 2.67/1.02      ( v1_partfun1(X0,X1)
% 2.67/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.02      | ~ v1_xboole_0(X1) ),
% 2.67/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_19,plain,
% 2.67/1.02      ( v1_funct_2(X0,X1,X2)
% 2.67/1.02      | ~ v1_partfun1(X0,X1)
% 2.67/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.02      | ~ v1_funct_1(X0) ),
% 2.67/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_388,plain,
% 2.67/1.02      ( v1_funct_2(X0,X1,X2)
% 2.67/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_xboole_0(X1) ),
% 2.67/1.02      inference(resolution,[status(thm)],[c_21,c_19]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_392,plain,
% 2.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.02      | v1_funct_2(X0,X1,X2)
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_xboole_0(X1) ),
% 2.67/1.02      inference(global_propositional_subsumption,
% 2.67/1.02                [status(thm)],
% 2.67/1.02                [c_388,c_21,c_19]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_393,plain,
% 2.67/1.02      ( v1_funct_2(X0,X1,X2)
% 2.67/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_xboole_0(X1) ),
% 2.67/1.02      inference(renaming,[status(thm)],[c_392]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_26,plain,
% 2.67/1.02      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.67/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.67/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.67/1.02      inference(cnf_transformation,[],[f93]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1183,plain,
% 2.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_xboole_0(X1)
% 2.67/1.02      | X3 != X0
% 2.67/1.02      | X4 != X2
% 2.67/1.02      | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
% 2.67/1.02      | k1_xboole_0 != X1 ),
% 2.67/1.02      inference(resolution_lifted,[status(thm)],[c_393,c_26]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1184,plain,
% 2.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_xboole_0(k1_xboole_0)
% 2.67/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.67/1.02      inference(unflattening,[status(thm)],[c_1183]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_0,plain,
% 2.67/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 2.67/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1188,plain,
% 2.67/1.02      ( ~ v1_funct_1(X0)
% 2.67/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.67/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.67/1.02      inference(global_propositional_subsumption,[status(thm)],[c_1184,c_0]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1189,plain,
% 2.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.67/1.02      inference(renaming,[status(thm)],[c_1188]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1355,plain,
% 2.67/1.02      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/1.02      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.67/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/1.02      | sK1 != k1_xboole_0 ),
% 2.67/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_1348,c_1189]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2295,plain,
% 2.67/1.02      ( sK1 != k1_xboole_0
% 2.67/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.67/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_1355]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_124,plain,
% 2.67/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1710,plain,
% 2.67/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.67/1.02      theory(equality) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2609,plain,
% 2.67/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 2.67/1.02      inference(instantiation,[status(thm)],[c_1710]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2610,plain,
% 2.67/1.02      ( sK1 != X0
% 2.67/1.02      | v1_xboole_0(X0) != iProver_top
% 2.67/1.02      | v1_xboole_0(sK1) = iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_2609]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2612,plain,
% 2.67/1.02      ( sK1 != k1_xboole_0
% 2.67/1.02      | v1_xboole_0(sK1) = iProver_top
% 2.67/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.67/1.02      inference(instantiation,[status(thm)],[c_2610]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1232,plain,
% 2.67/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.67/1.02      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/1.02      | ~ v1_funct_1(X0)
% 2.67/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/1.02      | ~ v1_xboole_0(X1)
% 2.67/1.02      | k2_funct_1(sK2) != X0
% 2.67/1.02      | sK0 != X2
% 2.67/1.02      | sK1 != X1 ),
% 2.67/1.02      inference(resolution_lifted,[status(thm)],[c_393,c_31]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1233,plain,
% 2.67/1.02      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.67/1.02      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.67/1.02      | ~ v1_xboole_0(sK1) ),
% 2.67/1.02      inference(unflattening,[status(thm)],[c_1232]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2300,plain,
% 2.67/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.67/1.02      | v1_xboole_0(sK1) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1234,plain,
% 2.67/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.67/1.02      | v1_xboole_0(sK1) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_1233]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2794,plain,
% 2.67/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.67/1.02      | v1_xboole_0(sK1) != iProver_top ),
% 2.67/1.02      inference(global_propositional_subsumption,
% 2.67/1.02                [status(thm)],
% 2.67/1.02                [c_2300,c_37,c_39,c_1234,c_2595,c_2760]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2976,plain,
% 2.67/1.02      ( sK1 != k1_xboole_0
% 2.67/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/1.02      inference(global_propositional_subsumption,
% 2.67/1.02                [status(thm)],
% 2.67/1.02                [c_2295,c_124,c_2612,c_2794]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3337,plain,
% 2.67/1.02      ( sK1 != k1_xboole_0
% 2.67/1.02      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/1.02      inference(demodulation,[status(thm)],[c_3238,c_2976]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4301,plain,
% 2.67/1.02      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.67/1.02      inference(global_propositional_subsumption,
% 2.67/1.02                [status(thm)],
% 2.67/1.02                [c_4297,c_3337,c_3983]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4830,plain,
% 2.67/1.02      ( sK1 = k1_xboole_0
% 2.67/1.02      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_3983,c_4825]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4857,plain,
% 2.67/1.02      ( sK1 = k1_xboole_0 ),
% 2.67/1.02      inference(global_propositional_subsumption,
% 2.67/1.02                [status(thm)],
% 2.67/1.02                [c_4846,c_3337,c_3983,c_4297,c_4830]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4872,plain,
% 2.67/1.02      ( k1_xboole_0 != k1_xboole_0
% 2.67/1.02      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.67/1.02      inference(demodulation,[status(thm)],[c_4857,c_3337]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4911,plain,
% 2.67/1.02      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.67/1.02      inference(equality_resolution_simp,[status(thm)],[c_4872]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2325,plain,
% 2.67/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_5,plain,
% 2.67/1.02      ( ~ v1_xboole_0(X0) | v1_xboole_0(k4_relat_1(X0)) ),
% 2.67/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2320,plain,
% 2.67/1.02      ( v1_xboole_0(X0) != iProver_top
% 2.67/1.02      | v1_xboole_0(k4_relat_1(X0)) = iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_1,plain,
% 2.67/1.02      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.67/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2324,plain,
% 2.67/1.02      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_3136,plain,
% 2.67/1.02      ( k4_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_2320,c_2324]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_5198,plain,
% 2.67/1.02      ( k4_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_2325,c_3136]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_6,plain,
% 2.67/1.02      ( ~ v1_relat_1(X0) | v1_xboole_0(X0) | ~ v1_xboole_0(k2_relat_1(X0)) ),
% 2.67/1.02      inference(cnf_transformation,[],[f58]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2319,plain,
% 2.67/1.02      ( v1_relat_1(X0) != iProver_top
% 2.67/1.02      | v1_xboole_0(X0) = iProver_top
% 2.67/1.02      | v1_xboole_0(k2_relat_1(X0)) != iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4445,plain,
% 2.67/1.02      ( v1_relat_1(sK2) != iProver_top
% 2.67/1.02      | v1_xboole_0(sK1) != iProver_top
% 2.67/1.02      | v1_xboole_0(sK2) = iProver_top ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_3765,c_2319]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4627,plain,
% 2.67/1.02      ( v1_xboole_0(sK1) != iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 2.67/1.02      inference(global_propositional_subsumption,
% 2.67/1.02                [status(thm)],
% 2.67/1.02                [c_4445,c_39,c_2760]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_4864,plain,
% 2.67/1.02      ( v1_xboole_0(sK2) = iProver_top
% 2.67/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.67/1.02      inference(demodulation,[status(thm)],[c_4857,c_4627]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_5355,plain,
% 2.67/1.02      ( v1_xboole_0(sK2) = iProver_top ),
% 2.67/1.02      inference(global_propositional_subsumption,
% 2.67/1.02                [status(thm)],
% 2.67/1.02                [c_4864,c_39,c_124,c_2612,c_2760,c_3337,c_3983,c_4297,c_4445,
% 2.67/1.02                 c_4830]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_5363,plain,
% 2.67/1.02      ( sK2 = k1_xboole_0 ),
% 2.67/1.02      inference(superposition,[status(thm)],[c_5355,c_2324]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_6142,plain,
% 2.67/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.67/1.02      inference(light_normalisation,[status(thm)],[c_4911,c_5198,c_5363]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2,plain,
% 2.67/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 2.67/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_2323,plain,
% 2.67/1.02      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 2.67/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.67/1.02  
% 2.67/1.02  cnf(c_6144,plain,
% 2.67/1.02      ( $false ),
% 2.67/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_6142,c_2323]) ).
% 2.67/1.02  
% 2.67/1.02  
% 2.67/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.67/1.02  
% 2.67/1.02  ------                               Statistics
% 2.67/1.02  
% 2.67/1.02  ------ General
% 2.67/1.02  
% 2.67/1.02  abstr_ref_over_cycles:                  0
% 2.67/1.02  abstr_ref_under_cycles:                 0
% 2.67/1.02  gc_basic_clause_elim:                   0
% 2.67/1.02  forced_gc_time:                         0
% 2.67/1.02  parsing_time:                           0.027
% 2.67/1.02  unif_index_cands_time:                  0.
% 2.67/1.02  unif_index_add_time:                    0.
% 2.67/1.02  orderings_time:                         0.
% 2.67/1.02  out_proof_time:                         0.017
% 2.67/1.02  total_time:                             0.285
% 2.67/1.02  num_of_symbols:                         50
% 2.67/1.02  num_of_terms:                           4719
% 2.67/1.02  
% 2.67/1.02  ------ Preprocessing
% 2.67/1.02  
% 2.67/1.02  num_of_splits:                          0
% 2.67/1.02  num_of_split_atoms:                     0
% 2.67/1.02  num_of_reused_defs:                     0
% 2.67/1.02  num_eq_ax_congr_red:                    5
% 2.67/1.02  num_of_sem_filtered_clauses:            1
% 2.67/1.02  num_of_subtypes:                        0
% 2.67/1.02  monotx_restored_types:                  0
% 2.67/1.02  sat_num_of_epr_types:                   0
% 2.67/1.02  sat_num_of_non_cyclic_types:            0
% 2.67/1.02  sat_guarded_non_collapsed_types:        0
% 2.67/1.02  num_pure_diseq_elim:                    0
% 2.67/1.02  simp_replaced_by:                       0
% 2.67/1.02  res_preprocessed:                       170
% 2.67/1.02  prep_upred:                             0
% 2.67/1.02  prep_unflattend:                        82
% 2.67/1.02  smt_new_axioms:                         0
% 2.67/1.02  pred_elim_cands:                        4
% 2.67/1.02  pred_elim:                              3
% 2.67/1.02  pred_elim_cl:                           -3
% 2.67/1.02  pred_elim_cycles:                       6
% 2.67/1.02  merged_defs:                            0
% 2.67/1.02  merged_defs_ncl:                        0
% 2.67/1.02  bin_hyper_res:                          0
% 2.67/1.02  prep_cycles:                            4
% 2.67/1.02  pred_elim_time:                         0.053
% 2.67/1.02  splitting_time:                         0.
% 2.67/1.02  sem_filter_time:                        0.
% 2.67/1.02  monotx_time:                            0.
% 2.67/1.02  subtype_inf_time:                       0.
% 2.67/1.02  
% 2.67/1.02  ------ Problem properties
% 2.67/1.02  
% 2.67/1.02  clauses:                                36
% 2.67/1.02  conjectures:                            3
% 2.67/1.02  epr:                                    5
% 2.67/1.02  horn:                                   31
% 2.67/1.02  ground:                                 16
% 2.67/1.02  unary:                                  5
% 2.67/1.02  binary:                                 15
% 2.67/1.02  lits:                                   95
% 2.67/1.02  lits_eq:                                35
% 2.67/1.02  fd_pure:                                0
% 2.67/1.02  fd_pseudo:                              0
% 2.67/1.02  fd_cond:                                2
% 2.67/1.02  fd_pseudo_cond:                         0
% 2.67/1.02  ac_symbols:                             0
% 2.67/1.02  
% 2.67/1.02  ------ Propositional Solver
% 2.67/1.02  
% 2.67/1.02  prop_solver_calls:                      28
% 2.67/1.02  prop_fast_solver_calls:                 1377
% 2.67/1.02  smt_solver_calls:                       0
% 2.67/1.02  smt_fast_solver_calls:                  0
% 2.67/1.02  prop_num_of_clauses:                    1993
% 2.67/1.02  prop_preprocess_simplified:             6714
% 2.67/1.02  prop_fo_subsumed:                       48
% 2.67/1.02  prop_solver_time:                       0.
% 2.67/1.02  smt_solver_time:                        0.
% 2.67/1.02  smt_fast_solver_time:                   0.
% 2.67/1.02  prop_fast_solver_time:                  0.
% 2.67/1.02  prop_unsat_core_time:                   0.
% 2.67/1.02  
% 2.67/1.02  ------ QBF
% 2.67/1.02  
% 2.67/1.02  qbf_q_res:                              0
% 2.67/1.02  qbf_num_tautologies:                    0
% 2.67/1.02  qbf_prep_cycles:                        0
% 2.67/1.02  
% 2.67/1.02  ------ BMC1
% 2.67/1.02  
% 2.67/1.02  bmc1_current_bound:                     -1
% 2.67/1.02  bmc1_last_solved_bound:                 -1
% 2.67/1.02  bmc1_unsat_core_size:                   -1
% 2.67/1.02  bmc1_unsat_core_parents_size:           -1
% 2.67/1.02  bmc1_merge_next_fun:                    0
% 2.67/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.67/1.02  
% 2.67/1.02  ------ Instantiation
% 2.67/1.02  
% 2.67/1.02  inst_num_of_clauses:                    649
% 2.67/1.02  inst_num_in_passive:                    80
% 2.67/1.02  inst_num_in_active:                     353
% 2.67/1.02  inst_num_in_unprocessed:                216
% 2.67/1.02  inst_num_of_loops:                      430
% 2.67/1.02  inst_num_of_learning_restarts:          0
% 2.67/1.02  inst_num_moves_active_passive:          74
% 2.67/1.02  inst_lit_activity:                      0
% 2.67/1.02  inst_lit_activity_moves:                0
% 2.67/1.02  inst_num_tautologies:                   0
% 2.67/1.02  inst_num_prop_implied:                  0
% 2.67/1.02  inst_num_existing_simplified:           0
% 2.67/1.02  inst_num_eq_res_simplified:             0
% 2.67/1.02  inst_num_child_elim:                    0
% 2.67/1.02  inst_num_of_dismatching_blockings:      181
% 2.67/1.02  inst_num_of_non_proper_insts:           549
% 2.67/1.02  inst_num_of_duplicates:                 0
% 2.67/1.02  inst_inst_num_from_inst_to_res:         0
% 2.67/1.02  inst_dismatching_checking_time:         0.
% 2.67/1.02  
% 2.67/1.02  ------ Resolution
% 2.67/1.02  
% 2.67/1.02  res_num_of_clauses:                     0
% 2.67/1.02  res_num_in_passive:                     0
% 2.67/1.02  res_num_in_active:                      0
% 2.67/1.02  res_num_of_loops:                       174
% 2.67/1.02  res_forward_subset_subsumed:            31
% 2.67/1.02  res_backward_subset_subsumed:           4
% 2.67/1.02  res_forward_subsumed:                   3
% 2.67/1.02  res_backward_subsumed:                  0
% 2.67/1.02  res_forward_subsumption_resolution:     4
% 2.67/1.02  res_backward_subsumption_resolution:    0
% 2.67/1.02  res_clause_to_clause_subsumption:       215
% 2.67/1.02  res_orphan_elimination:                 0
% 2.67/1.02  res_tautology_del:                      95
% 2.67/1.02  res_num_eq_res_simplified:              0
% 2.67/1.02  res_num_sel_changes:                    0
% 2.67/1.02  res_moves_from_active_to_pass:          0
% 2.67/1.02  
% 2.67/1.02  ------ Superposition
% 2.67/1.02  
% 2.67/1.02  sup_time_total:                         0.
% 2.67/1.02  sup_time_generating:                    0.
% 2.67/1.02  sup_time_sim_full:                      0.
% 2.67/1.02  sup_time_sim_immed:                     0.
% 2.67/1.02  
% 2.67/1.02  sup_num_of_clauses:                     55
% 2.67/1.02  sup_num_in_active:                      36
% 2.67/1.02  sup_num_in_passive:                     19
% 2.67/1.02  sup_num_of_loops:                       85
% 2.67/1.02  sup_fw_superposition:                   42
% 2.67/1.02  sup_bw_superposition:                   46
% 2.67/1.02  sup_immediate_simplified:               43
% 2.67/1.02  sup_given_eliminated:                   1
% 2.67/1.02  comparisons_done:                       0
% 2.67/1.02  comparisons_avoided:                    5
% 2.67/1.02  
% 2.67/1.02  ------ Simplifications
% 2.67/1.02  
% 2.67/1.02  
% 2.67/1.02  sim_fw_subset_subsumed:                 16
% 2.67/1.02  sim_bw_subset_subsumed:                 5
% 2.67/1.02  sim_fw_subsumed:                        11
% 2.67/1.02  sim_bw_subsumed:                        2
% 2.67/1.02  sim_fw_subsumption_res:                 2
% 2.67/1.02  sim_bw_subsumption_res:                 1
% 2.67/1.02  sim_tautology_del:                      5
% 2.67/1.02  sim_eq_tautology_del:                   12
% 2.67/1.02  sim_eq_res_simp:                        3
% 2.67/1.02  sim_fw_demodulated:                     1
% 2.67/1.02  sim_bw_demodulated:                     47
% 2.67/1.02  sim_light_normalised:                   29
% 2.67/1.02  sim_joinable_taut:                      0
% 2.67/1.02  sim_joinable_simp:                      0
% 2.67/1.02  sim_ac_normalised:                      0
% 2.67/1.02  sim_smt_subsumption:                    0
% 2.67/1.02  
%------------------------------------------------------------------------------
