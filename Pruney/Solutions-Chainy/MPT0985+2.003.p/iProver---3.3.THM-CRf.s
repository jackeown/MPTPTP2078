%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:19 EST 2020

% Result     : Theorem 2.90s
% Output     : CNFRefutation 2.90s
% Verified   : 
% Statistics : Number of formulae       :  160 (1374 expanded)
%              Number of clauses        :   95 ( 422 expanded)
%              Number of leaves         :   16 ( 269 expanded)
%              Depth                    :   21
%              Number of atoms          :  519 (7411 expanded)
%              Number of equality atoms :  216 (1468 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,axiom,(
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

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f19])).

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
    inference(flattening,[],[f42])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f46,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

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
    inference(flattening,[],[f46])).

fof(f51,plain,
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

fof(f52,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f51])).

fof(f85,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f87,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f83,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f91,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f56])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f95,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f39])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_funct_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f61,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f96,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1251,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_35])).

cnf(c_1252,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_1251])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1254,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1252,c_34])).

cnf(c_2195,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2198,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4666,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2195,c_2198])).

cnf(c_4826,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1254,c_4666])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2197,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3495,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2195,c_2197])).

cnf(c_32,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_3507,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3495,c_32])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_388,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_33])).

cnf(c_389,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_391,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_389,c_36])).

cnf(c_2193,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_391])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2478,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2491,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2193,c_36,c_34,c_389,c_2478])).

cnf(c_3599,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3507,c_2491])).

cnf(c_28,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2196,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3619,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3599,c_2196])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_402,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_33])).

cnf(c_403,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_405,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_403,c_36])).

cnf(c_2192,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_405])).

cnf(c_2487,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2192,c_36,c_34,c_403,c_2478])).

cnf(c_3620,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3619,c_2487])).

cnf(c_37,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_2479,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2478])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2543,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2544,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2543])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3246,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_3247,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3246])).

cnf(c_4183,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3620,c_37,c_39,c_2479,c_2544,c_3247])).

cnf(c_4886,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4826,c_4183])).

cnf(c_29,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_31,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1358,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != sK0
    | k1_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_29,c_31])).

cnf(c_1359,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_1358])).

cnf(c_1371,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1359,c_14])).

cnf(c_2181,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_1376,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1371])).

cnf(c_2649,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2181,c_37,c_39,c_1376,c_2479,c_2544])).

cnf(c_2650,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2649])).

cnf(c_2653,plain,
    ( k2_relat_1(sK2) != sK1
    | k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2650,c_2487,c_2491])).

cnf(c_3598,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3507,c_2653])).

cnf(c_3602,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3598])).

cnf(c_4887,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4826,c_3602])).

cnf(c_4901,plain,
    ( sK1 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4886,c_4887])).

cnf(c_5032,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4901,c_4183])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_5111,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5032,c_3])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1337,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_1338,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1337])).

cnf(c_21,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_19,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_364,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_21,c_19])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_8,plain,
    ( v1_funct_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_368,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_364,c_21,c_19,c_15,c_8])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1176,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_xboole_0(X1)
    | X3 != X0
    | X4 != X2
    | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_368,c_26])).

cnf(c_1177,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1176])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1181,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1177,c_0])).

cnf(c_1345,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | sK1 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1338,c_1181])).

cnf(c_2182,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1345])).

cnf(c_2385,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2182,c_3])).

cnf(c_117,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1222,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_xboole_0(X1)
    | k2_funct_1(sK2) != X0
    | sK0 != X2
    | sK1 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_368,c_31])).

cnf(c_1223,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_xboole_0(sK1) ),
    inference(unflattening,[status(thm)],[c_1222])).

cnf(c_1224,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1223])).

cnf(c_1658,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2481,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_1658])).

cnf(c_2482,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2481])).

cnf(c_2484,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2482])).

cnf(c_2724,plain,
    ( sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2385,c_37,c_39,c_117,c_1224,c_2479,c_2484,c_2544])).

cnf(c_5040,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4901,c_2724])).

cnf(c_5091,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5040])).

cnf(c_5093,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5091,c_3])).

cnf(c_5113,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5111,c_5093])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.90/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.90/1.00  
% 2.90/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.90/1.00  
% 2.90/1.00  ------  iProver source info
% 2.90/1.00  
% 2.90/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.90/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.90/1.00  git: non_committed_changes: false
% 2.90/1.00  git: last_make_outside_of_git: false
% 2.90/1.00  
% 2.90/1.00  ------ 
% 2.90/1.00  
% 2.90/1.00  ------ Input Options
% 2.90/1.00  
% 2.90/1.00  --out_options                           all
% 2.90/1.00  --tptp_safe_out                         true
% 2.90/1.00  --problem_path                          ""
% 2.90/1.00  --include_path                          ""
% 2.90/1.00  --clausifier                            res/vclausify_rel
% 2.90/1.00  --clausifier_options                    --mode clausify
% 2.90/1.00  --stdin                                 false
% 2.90/1.00  --stats_out                             all
% 2.90/1.00  
% 2.90/1.00  ------ General Options
% 2.90/1.00  
% 2.90/1.00  --fof                                   false
% 2.90/1.00  --time_out_real                         305.
% 2.90/1.00  --time_out_virtual                      -1.
% 2.90/1.00  --symbol_type_check                     false
% 2.90/1.00  --clausify_out                          false
% 2.90/1.00  --sig_cnt_out                           false
% 2.90/1.00  --trig_cnt_out                          false
% 2.90/1.00  --trig_cnt_out_tolerance                1.
% 2.90/1.00  --trig_cnt_out_sk_spl                   false
% 2.90/1.00  --abstr_cl_out                          false
% 2.90/1.00  
% 2.90/1.00  ------ Global Options
% 2.90/1.00  
% 2.90/1.00  --schedule                              default
% 2.90/1.00  --add_important_lit                     false
% 2.90/1.00  --prop_solver_per_cl                    1000
% 2.90/1.00  --min_unsat_core                        false
% 2.90/1.00  --soft_assumptions                      false
% 2.90/1.00  --soft_lemma_size                       3
% 2.90/1.00  --prop_impl_unit_size                   0
% 2.90/1.00  --prop_impl_unit                        []
% 2.90/1.00  --share_sel_clauses                     true
% 2.90/1.00  --reset_solvers                         false
% 2.90/1.00  --bc_imp_inh                            [conj_cone]
% 2.90/1.00  --conj_cone_tolerance                   3.
% 2.90/1.00  --extra_neg_conj                        none
% 2.90/1.00  --large_theory_mode                     true
% 2.90/1.00  --prolific_symb_bound                   200
% 2.90/1.00  --lt_threshold                          2000
% 2.90/1.00  --clause_weak_htbl                      true
% 2.90/1.00  --gc_record_bc_elim                     false
% 2.90/1.00  
% 2.90/1.00  ------ Preprocessing Options
% 2.90/1.00  
% 2.90/1.00  --preprocessing_flag                    true
% 2.90/1.00  --time_out_prep_mult                    0.1
% 2.90/1.00  --splitting_mode                        input
% 2.90/1.00  --splitting_grd                         true
% 2.90/1.00  --splitting_cvd                         false
% 2.90/1.00  --splitting_cvd_svl                     false
% 2.90/1.00  --splitting_nvd                         32
% 2.90/1.00  --sub_typing                            true
% 2.90/1.00  --prep_gs_sim                           true
% 2.90/1.00  --prep_unflatten                        true
% 2.90/1.00  --prep_res_sim                          true
% 2.90/1.00  --prep_upred                            true
% 2.90/1.00  --prep_sem_filter                       exhaustive
% 2.90/1.00  --prep_sem_filter_out                   false
% 2.90/1.00  --pred_elim                             true
% 2.90/1.00  --res_sim_input                         true
% 2.90/1.00  --eq_ax_congr_red                       true
% 2.90/1.00  --pure_diseq_elim                       true
% 2.90/1.00  --brand_transform                       false
% 2.90/1.00  --non_eq_to_eq                          false
% 2.90/1.00  --prep_def_merge                        true
% 2.90/1.00  --prep_def_merge_prop_impl              false
% 2.90/1.00  --prep_def_merge_mbd                    true
% 2.90/1.00  --prep_def_merge_tr_red                 false
% 2.90/1.00  --prep_def_merge_tr_cl                  false
% 2.90/1.00  --smt_preprocessing                     true
% 2.90/1.00  --smt_ac_axioms                         fast
% 2.90/1.00  --preprocessed_out                      false
% 2.90/1.00  --preprocessed_stats                    false
% 2.90/1.00  
% 2.90/1.00  ------ Abstraction refinement Options
% 2.90/1.00  
% 2.90/1.00  --abstr_ref                             []
% 2.90/1.00  --abstr_ref_prep                        false
% 2.90/1.00  --abstr_ref_until_sat                   false
% 2.90/1.00  --abstr_ref_sig_restrict                funpre
% 2.90/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/1.00  --abstr_ref_under                       []
% 2.90/1.00  
% 2.90/1.00  ------ SAT Options
% 2.90/1.00  
% 2.90/1.00  --sat_mode                              false
% 2.90/1.00  --sat_fm_restart_options                ""
% 2.90/1.00  --sat_gr_def                            false
% 2.90/1.00  --sat_epr_types                         true
% 2.90/1.00  --sat_non_cyclic_types                  false
% 2.90/1.00  --sat_finite_models                     false
% 2.90/1.00  --sat_fm_lemmas                         false
% 2.90/1.00  --sat_fm_prep                           false
% 2.90/1.00  --sat_fm_uc_incr                        true
% 2.90/1.00  --sat_out_model                         small
% 2.90/1.00  --sat_out_clauses                       false
% 2.90/1.00  
% 2.90/1.00  ------ QBF Options
% 2.90/1.00  
% 2.90/1.00  --qbf_mode                              false
% 2.90/1.00  --qbf_elim_univ                         false
% 2.90/1.00  --qbf_dom_inst                          none
% 2.90/1.00  --qbf_dom_pre_inst                      false
% 2.90/1.00  --qbf_sk_in                             false
% 2.90/1.00  --qbf_pred_elim                         true
% 2.90/1.00  --qbf_split                             512
% 2.90/1.00  
% 2.90/1.00  ------ BMC1 Options
% 2.90/1.00  
% 2.90/1.00  --bmc1_incremental                      false
% 2.90/1.00  --bmc1_axioms                           reachable_all
% 2.90/1.00  --bmc1_min_bound                        0
% 2.90/1.00  --bmc1_max_bound                        -1
% 2.90/1.00  --bmc1_max_bound_default                -1
% 2.90/1.00  --bmc1_symbol_reachability              true
% 2.90/1.00  --bmc1_property_lemmas                  false
% 2.90/1.00  --bmc1_k_induction                      false
% 2.90/1.00  --bmc1_non_equiv_states                 false
% 2.90/1.00  --bmc1_deadlock                         false
% 2.90/1.00  --bmc1_ucm                              false
% 2.90/1.00  --bmc1_add_unsat_core                   none
% 2.90/1.00  --bmc1_unsat_core_children              false
% 2.90/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/1.00  --bmc1_out_stat                         full
% 2.90/1.00  --bmc1_ground_init                      false
% 2.90/1.00  --bmc1_pre_inst_next_state              false
% 2.90/1.00  --bmc1_pre_inst_state                   false
% 2.90/1.00  --bmc1_pre_inst_reach_state             false
% 2.90/1.00  --bmc1_out_unsat_core                   false
% 2.90/1.00  --bmc1_aig_witness_out                  false
% 2.90/1.00  --bmc1_verbose                          false
% 2.90/1.00  --bmc1_dump_clauses_tptp                false
% 2.90/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.90/1.00  --bmc1_dump_file                        -
% 2.90/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.90/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.90/1.00  --bmc1_ucm_extend_mode                  1
% 2.90/1.00  --bmc1_ucm_init_mode                    2
% 2.90/1.00  --bmc1_ucm_cone_mode                    none
% 2.90/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.90/1.00  --bmc1_ucm_relax_model                  4
% 2.90/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.90/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/1.00  --bmc1_ucm_layered_model                none
% 2.90/1.00  --bmc1_ucm_max_lemma_size               10
% 2.90/1.00  
% 2.90/1.00  ------ AIG Options
% 2.90/1.00  
% 2.90/1.00  --aig_mode                              false
% 2.90/1.00  
% 2.90/1.00  ------ Instantiation Options
% 2.90/1.00  
% 2.90/1.00  --instantiation_flag                    true
% 2.90/1.00  --inst_sos_flag                         false
% 2.90/1.00  --inst_sos_phase                        true
% 2.90/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/1.00  --inst_lit_sel_side                     num_symb
% 2.90/1.00  --inst_solver_per_active                1400
% 2.90/1.00  --inst_solver_calls_frac                1.
% 2.90/1.00  --inst_passive_queue_type               priority_queues
% 2.90/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/1.00  --inst_passive_queues_freq              [25;2]
% 2.90/1.00  --inst_dismatching                      true
% 2.90/1.00  --inst_eager_unprocessed_to_passive     true
% 2.90/1.00  --inst_prop_sim_given                   true
% 2.90/1.00  --inst_prop_sim_new                     false
% 2.90/1.00  --inst_subs_new                         false
% 2.90/1.00  --inst_eq_res_simp                      false
% 2.90/1.00  --inst_subs_given                       false
% 2.90/1.00  --inst_orphan_elimination               true
% 2.90/1.00  --inst_learning_loop_flag               true
% 2.90/1.00  --inst_learning_start                   3000
% 2.90/1.00  --inst_learning_factor                  2
% 2.90/1.00  --inst_start_prop_sim_after_learn       3
% 2.90/1.00  --inst_sel_renew                        solver
% 2.90/1.00  --inst_lit_activity_flag                true
% 2.90/1.00  --inst_restr_to_given                   false
% 2.90/1.00  --inst_activity_threshold               500
% 2.90/1.00  --inst_out_proof                        true
% 2.90/1.00  
% 2.90/1.00  ------ Resolution Options
% 2.90/1.00  
% 2.90/1.00  --resolution_flag                       true
% 2.90/1.00  --res_lit_sel                           adaptive
% 2.90/1.00  --res_lit_sel_side                      none
% 2.90/1.00  --res_ordering                          kbo
% 2.90/1.00  --res_to_prop_solver                    active
% 2.90/1.00  --res_prop_simpl_new                    false
% 2.90/1.00  --res_prop_simpl_given                  true
% 2.90/1.00  --res_passive_queue_type                priority_queues
% 2.90/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/1.00  --res_passive_queues_freq               [15;5]
% 2.90/1.00  --res_forward_subs                      full
% 2.90/1.00  --res_backward_subs                     full
% 2.90/1.00  --res_forward_subs_resolution           true
% 2.90/1.00  --res_backward_subs_resolution          true
% 2.90/1.00  --res_orphan_elimination                true
% 2.90/1.00  --res_time_limit                        2.
% 2.90/1.00  --res_out_proof                         true
% 2.90/1.00  
% 2.90/1.00  ------ Superposition Options
% 2.90/1.00  
% 2.90/1.00  --superposition_flag                    true
% 2.90/1.00  --sup_passive_queue_type                priority_queues
% 2.90/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.90/1.00  --demod_completeness_check              fast
% 2.90/1.00  --demod_use_ground                      true
% 2.90/1.00  --sup_to_prop_solver                    passive
% 2.90/1.00  --sup_prop_simpl_new                    true
% 2.90/1.00  --sup_prop_simpl_given                  true
% 2.90/1.00  --sup_fun_splitting                     false
% 2.90/1.00  --sup_smt_interval                      50000
% 2.90/1.00  
% 2.90/1.00  ------ Superposition Simplification Setup
% 2.90/1.00  
% 2.90/1.00  --sup_indices_passive                   []
% 2.90/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/1.00  --sup_full_bw                           [BwDemod]
% 2.90/1.00  --sup_immed_triv                        [TrivRules]
% 2.90/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/1.00  --sup_immed_bw_main                     []
% 2.90/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/1.00  
% 2.90/1.00  ------ Combination Options
% 2.90/1.00  
% 2.90/1.00  --comb_res_mult                         3
% 2.90/1.00  --comb_sup_mult                         2
% 2.90/1.00  --comb_inst_mult                        10
% 2.90/1.00  
% 2.90/1.00  ------ Debug Options
% 2.90/1.00  
% 2.90/1.00  --dbg_backtrace                         false
% 2.90/1.00  --dbg_dump_prop_clauses                 false
% 2.90/1.00  --dbg_dump_prop_clauses_file            -
% 2.90/1.00  --dbg_out_stat                          false
% 2.90/1.00  ------ Parsing...
% 2.90/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.90/1.00  
% 2.90/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.90/1.00  
% 2.90/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.90/1.00  
% 2.90/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.90/1.00  ------ Proving...
% 2.90/1.00  ------ Problem Properties 
% 2.90/1.00  
% 2.90/1.00  
% 2.90/1.00  clauses                                 35
% 2.90/1.00  conjectures                             3
% 2.90/1.00  EPR                                     4
% 2.90/1.00  Horn                                    29
% 2.90/1.00  unary                                   7
% 2.90/1.00  binary                                  12
% 2.90/1.00  lits                                    90
% 2.90/1.00  lits eq                                 37
% 2.90/1.00  fd_pure                                 0
% 2.90/1.00  fd_pseudo                               0
% 2.90/1.00  fd_cond                                 3
% 2.90/1.00  fd_pseudo_cond                          0
% 2.90/1.00  AC symbols                              0
% 2.90/1.00  
% 2.90/1.00  ------ Schedule dynamic 5 is on 
% 2.90/1.00  
% 2.90/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.90/1.00  
% 2.90/1.00  
% 2.90/1.00  ------ 
% 2.90/1.00  Current options:
% 2.90/1.00  ------ 
% 2.90/1.00  
% 2.90/1.00  ------ Input Options
% 2.90/1.00  
% 2.90/1.00  --out_options                           all
% 2.90/1.00  --tptp_safe_out                         true
% 2.90/1.00  --problem_path                          ""
% 2.90/1.00  --include_path                          ""
% 2.90/1.00  --clausifier                            res/vclausify_rel
% 2.90/1.00  --clausifier_options                    --mode clausify
% 2.90/1.00  --stdin                                 false
% 2.90/1.00  --stats_out                             all
% 2.90/1.00  
% 2.90/1.00  ------ General Options
% 2.90/1.00  
% 2.90/1.00  --fof                                   false
% 2.90/1.00  --time_out_real                         305.
% 2.90/1.00  --time_out_virtual                      -1.
% 2.90/1.00  --symbol_type_check                     false
% 2.90/1.00  --clausify_out                          false
% 2.90/1.00  --sig_cnt_out                           false
% 2.90/1.00  --trig_cnt_out                          false
% 2.90/1.00  --trig_cnt_out_tolerance                1.
% 2.90/1.00  --trig_cnt_out_sk_spl                   false
% 2.90/1.00  --abstr_cl_out                          false
% 2.90/1.00  
% 2.90/1.00  ------ Global Options
% 2.90/1.00  
% 2.90/1.00  --schedule                              default
% 2.90/1.00  --add_important_lit                     false
% 2.90/1.00  --prop_solver_per_cl                    1000
% 2.90/1.00  --min_unsat_core                        false
% 2.90/1.00  --soft_assumptions                      false
% 2.90/1.00  --soft_lemma_size                       3
% 2.90/1.00  --prop_impl_unit_size                   0
% 2.90/1.00  --prop_impl_unit                        []
% 2.90/1.00  --share_sel_clauses                     true
% 2.90/1.00  --reset_solvers                         false
% 2.90/1.00  --bc_imp_inh                            [conj_cone]
% 2.90/1.00  --conj_cone_tolerance                   3.
% 2.90/1.00  --extra_neg_conj                        none
% 2.90/1.00  --large_theory_mode                     true
% 2.90/1.00  --prolific_symb_bound                   200
% 2.90/1.00  --lt_threshold                          2000
% 2.90/1.00  --clause_weak_htbl                      true
% 2.90/1.00  --gc_record_bc_elim                     false
% 2.90/1.00  
% 2.90/1.00  ------ Preprocessing Options
% 2.90/1.00  
% 2.90/1.00  --preprocessing_flag                    true
% 2.90/1.00  --time_out_prep_mult                    0.1
% 2.90/1.00  --splitting_mode                        input
% 2.90/1.00  --splitting_grd                         true
% 2.90/1.00  --splitting_cvd                         false
% 2.90/1.00  --splitting_cvd_svl                     false
% 2.90/1.00  --splitting_nvd                         32
% 2.90/1.00  --sub_typing                            true
% 2.90/1.00  --prep_gs_sim                           true
% 2.90/1.00  --prep_unflatten                        true
% 2.90/1.00  --prep_res_sim                          true
% 2.90/1.00  --prep_upred                            true
% 2.90/1.00  --prep_sem_filter                       exhaustive
% 2.90/1.00  --prep_sem_filter_out                   false
% 2.90/1.00  --pred_elim                             true
% 2.90/1.00  --res_sim_input                         true
% 2.90/1.00  --eq_ax_congr_red                       true
% 2.90/1.00  --pure_diseq_elim                       true
% 2.90/1.00  --brand_transform                       false
% 2.90/1.00  --non_eq_to_eq                          false
% 2.90/1.00  --prep_def_merge                        true
% 2.90/1.00  --prep_def_merge_prop_impl              false
% 2.90/1.00  --prep_def_merge_mbd                    true
% 2.90/1.00  --prep_def_merge_tr_red                 false
% 2.90/1.00  --prep_def_merge_tr_cl                  false
% 2.90/1.00  --smt_preprocessing                     true
% 2.90/1.00  --smt_ac_axioms                         fast
% 2.90/1.00  --preprocessed_out                      false
% 2.90/1.00  --preprocessed_stats                    false
% 2.90/1.00  
% 2.90/1.00  ------ Abstraction refinement Options
% 2.90/1.00  
% 2.90/1.00  --abstr_ref                             []
% 2.90/1.00  --abstr_ref_prep                        false
% 2.90/1.00  --abstr_ref_until_sat                   false
% 2.90/1.00  --abstr_ref_sig_restrict                funpre
% 2.90/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.90/1.00  --abstr_ref_under                       []
% 2.90/1.00  
% 2.90/1.00  ------ SAT Options
% 2.90/1.00  
% 2.90/1.00  --sat_mode                              false
% 2.90/1.00  --sat_fm_restart_options                ""
% 2.90/1.00  --sat_gr_def                            false
% 2.90/1.00  --sat_epr_types                         true
% 2.90/1.00  --sat_non_cyclic_types                  false
% 2.90/1.00  --sat_finite_models                     false
% 2.90/1.00  --sat_fm_lemmas                         false
% 2.90/1.00  --sat_fm_prep                           false
% 2.90/1.00  --sat_fm_uc_incr                        true
% 2.90/1.00  --sat_out_model                         small
% 2.90/1.00  --sat_out_clauses                       false
% 2.90/1.00  
% 2.90/1.00  ------ QBF Options
% 2.90/1.00  
% 2.90/1.00  --qbf_mode                              false
% 2.90/1.00  --qbf_elim_univ                         false
% 2.90/1.00  --qbf_dom_inst                          none
% 2.90/1.00  --qbf_dom_pre_inst                      false
% 2.90/1.00  --qbf_sk_in                             false
% 2.90/1.00  --qbf_pred_elim                         true
% 2.90/1.00  --qbf_split                             512
% 2.90/1.00  
% 2.90/1.00  ------ BMC1 Options
% 2.90/1.00  
% 2.90/1.00  --bmc1_incremental                      false
% 2.90/1.00  --bmc1_axioms                           reachable_all
% 2.90/1.00  --bmc1_min_bound                        0
% 2.90/1.00  --bmc1_max_bound                        -1
% 2.90/1.00  --bmc1_max_bound_default                -1
% 2.90/1.00  --bmc1_symbol_reachability              true
% 2.90/1.00  --bmc1_property_lemmas                  false
% 2.90/1.00  --bmc1_k_induction                      false
% 2.90/1.00  --bmc1_non_equiv_states                 false
% 2.90/1.00  --bmc1_deadlock                         false
% 2.90/1.00  --bmc1_ucm                              false
% 2.90/1.00  --bmc1_add_unsat_core                   none
% 2.90/1.00  --bmc1_unsat_core_children              false
% 2.90/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.90/1.00  --bmc1_out_stat                         full
% 2.90/1.00  --bmc1_ground_init                      false
% 2.90/1.00  --bmc1_pre_inst_next_state              false
% 2.90/1.00  --bmc1_pre_inst_state                   false
% 2.90/1.00  --bmc1_pre_inst_reach_state             false
% 2.90/1.00  --bmc1_out_unsat_core                   false
% 2.90/1.00  --bmc1_aig_witness_out                  false
% 2.90/1.00  --bmc1_verbose                          false
% 2.90/1.00  --bmc1_dump_clauses_tptp                false
% 2.90/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.90/1.00  --bmc1_dump_file                        -
% 2.90/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.90/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.90/1.00  --bmc1_ucm_extend_mode                  1
% 2.90/1.00  --bmc1_ucm_init_mode                    2
% 2.90/1.00  --bmc1_ucm_cone_mode                    none
% 2.90/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.90/1.00  --bmc1_ucm_relax_model                  4
% 2.90/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.90/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.90/1.00  --bmc1_ucm_layered_model                none
% 2.90/1.00  --bmc1_ucm_max_lemma_size               10
% 2.90/1.00  
% 2.90/1.00  ------ AIG Options
% 2.90/1.00  
% 2.90/1.00  --aig_mode                              false
% 2.90/1.00  
% 2.90/1.00  ------ Instantiation Options
% 2.90/1.00  
% 2.90/1.00  --instantiation_flag                    true
% 2.90/1.00  --inst_sos_flag                         false
% 2.90/1.00  --inst_sos_phase                        true
% 2.90/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.90/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.90/1.00  --inst_lit_sel_side                     none
% 2.90/1.00  --inst_solver_per_active                1400
% 2.90/1.00  --inst_solver_calls_frac                1.
% 2.90/1.00  --inst_passive_queue_type               priority_queues
% 2.90/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.90/1.01  --inst_passive_queues_freq              [25;2]
% 2.90/1.01  --inst_dismatching                      true
% 2.90/1.01  --inst_eager_unprocessed_to_passive     true
% 2.90/1.01  --inst_prop_sim_given                   true
% 2.90/1.01  --inst_prop_sim_new                     false
% 2.90/1.01  --inst_subs_new                         false
% 2.90/1.01  --inst_eq_res_simp                      false
% 2.90/1.01  --inst_subs_given                       false
% 2.90/1.01  --inst_orphan_elimination               true
% 2.90/1.01  --inst_learning_loop_flag               true
% 2.90/1.01  --inst_learning_start                   3000
% 2.90/1.01  --inst_learning_factor                  2
% 2.90/1.01  --inst_start_prop_sim_after_learn       3
% 2.90/1.01  --inst_sel_renew                        solver
% 2.90/1.01  --inst_lit_activity_flag                true
% 2.90/1.01  --inst_restr_to_given                   false
% 2.90/1.01  --inst_activity_threshold               500
% 2.90/1.01  --inst_out_proof                        true
% 2.90/1.01  
% 2.90/1.01  ------ Resolution Options
% 2.90/1.01  
% 2.90/1.01  --resolution_flag                       false
% 2.90/1.01  --res_lit_sel                           adaptive
% 2.90/1.01  --res_lit_sel_side                      none
% 2.90/1.01  --res_ordering                          kbo
% 2.90/1.01  --res_to_prop_solver                    active
% 2.90/1.01  --res_prop_simpl_new                    false
% 2.90/1.01  --res_prop_simpl_given                  true
% 2.90/1.01  --res_passive_queue_type                priority_queues
% 2.90/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.90/1.01  --res_passive_queues_freq               [15;5]
% 2.90/1.01  --res_forward_subs                      full
% 2.90/1.01  --res_backward_subs                     full
% 2.90/1.01  --res_forward_subs_resolution           true
% 2.90/1.01  --res_backward_subs_resolution          true
% 2.90/1.01  --res_orphan_elimination                true
% 2.90/1.01  --res_time_limit                        2.
% 2.90/1.01  --res_out_proof                         true
% 2.90/1.01  
% 2.90/1.01  ------ Superposition Options
% 2.90/1.01  
% 2.90/1.01  --superposition_flag                    true
% 2.90/1.01  --sup_passive_queue_type                priority_queues
% 2.90/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.90/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.90/1.01  --demod_completeness_check              fast
% 2.90/1.01  --demod_use_ground                      true
% 2.90/1.01  --sup_to_prop_solver                    passive
% 2.90/1.01  --sup_prop_simpl_new                    true
% 2.90/1.01  --sup_prop_simpl_given                  true
% 2.90/1.01  --sup_fun_splitting                     false
% 2.90/1.01  --sup_smt_interval                      50000
% 2.90/1.01  
% 2.90/1.01  ------ Superposition Simplification Setup
% 2.90/1.01  
% 2.90/1.01  --sup_indices_passive                   []
% 2.90/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.90/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.90/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/1.01  --sup_full_bw                           [BwDemod]
% 2.90/1.01  --sup_immed_triv                        [TrivRules]
% 2.90/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.90/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/1.01  --sup_immed_bw_main                     []
% 2.90/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.90/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.90/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.90/1.01  
% 2.90/1.01  ------ Combination Options
% 2.90/1.01  
% 2.90/1.01  --comb_res_mult                         3
% 2.90/1.01  --comb_sup_mult                         2
% 2.90/1.01  --comb_inst_mult                        10
% 2.90/1.01  
% 2.90/1.01  ------ Debug Options
% 2.90/1.01  
% 2.90/1.01  --dbg_backtrace                         false
% 2.90/1.01  --dbg_dump_prop_clauses                 false
% 2.90/1.01  --dbg_dump_prop_clauses_file            -
% 2.90/1.01  --dbg_out_stat                          false
% 2.90/1.01  
% 2.90/1.01  
% 2.90/1.01  
% 2.90/1.01  
% 2.90/1.01  ------ Proving...
% 2.90/1.01  
% 2.90/1.01  
% 2.90/1.01  % SZS status Theorem for theBenchmark.p
% 2.90/1.01  
% 2.90/1.01   Resolution empty clause
% 2.90/1.01  
% 2.90/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.90/1.01  
% 2.90/1.01  fof(f19,axiom,(
% 2.90/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f42,plain,(
% 2.90/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/1.01    inference(ennf_transformation,[],[f19])).
% 2.90/1.01  
% 2.90/1.01  fof(f43,plain,(
% 2.90/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/1.01    inference(flattening,[],[f42])).
% 2.90/1.01  
% 2.90/1.01  fof(f50,plain,(
% 2.90/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/1.01    inference(nnf_transformation,[],[f43])).
% 2.90/1.01  
% 2.90/1.01  fof(f75,plain,(
% 2.90/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/1.01    inference(cnf_transformation,[],[f50])).
% 2.90/1.01  
% 2.90/1.01  fof(f21,conjecture,(
% 2.90/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f22,negated_conjecture,(
% 2.90/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.90/1.01    inference(negated_conjecture,[],[f21])).
% 2.90/1.01  
% 2.90/1.01  fof(f46,plain,(
% 2.90/1.01    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.90/1.01    inference(ennf_transformation,[],[f22])).
% 2.90/1.01  
% 2.90/1.01  fof(f47,plain,(
% 2.90/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.90/1.01    inference(flattening,[],[f46])).
% 2.90/1.01  
% 2.90/1.01  fof(f51,plain,(
% 2.90/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.90/1.01    introduced(choice_axiom,[])).
% 2.90/1.01  
% 2.90/1.01  fof(f52,plain,(
% 2.90/1.01    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.90/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f47,f51])).
% 2.90/1.01  
% 2.90/1.01  fof(f85,plain,(
% 2.90/1.01    v1_funct_2(sK2,sK0,sK1)),
% 2.90/1.01    inference(cnf_transformation,[],[f52])).
% 2.90/1.01  
% 2.90/1.01  fof(f86,plain,(
% 2.90/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.90/1.01    inference(cnf_transformation,[],[f52])).
% 2.90/1.01  
% 2.90/1.01  fof(f15,axiom,(
% 2.90/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f37,plain,(
% 2.90/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/1.01    inference(ennf_transformation,[],[f15])).
% 2.90/1.01  
% 2.90/1.01  fof(f70,plain,(
% 2.90/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/1.01    inference(cnf_transformation,[],[f37])).
% 2.90/1.01  
% 2.90/1.01  fof(f16,axiom,(
% 2.90/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f38,plain,(
% 2.90/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/1.01    inference(ennf_transformation,[],[f16])).
% 2.90/1.01  
% 2.90/1.01  fof(f71,plain,(
% 2.90/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/1.01    inference(cnf_transformation,[],[f38])).
% 2.90/1.01  
% 2.90/1.01  fof(f88,plain,(
% 2.90/1.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 2.90/1.01    inference(cnf_transformation,[],[f52])).
% 2.90/1.01  
% 2.90/1.01  fof(f11,axiom,(
% 2.90/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f32,plain,(
% 2.90/1.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/1.01    inference(ennf_transformation,[],[f11])).
% 2.90/1.01  
% 2.90/1.01  fof(f33,plain,(
% 2.90/1.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/1.01    inference(flattening,[],[f32])).
% 2.90/1.01  
% 2.90/1.01  fof(f65,plain,(
% 2.90/1.01    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/1.01    inference(cnf_transformation,[],[f33])).
% 2.90/1.01  
% 2.90/1.01  fof(f87,plain,(
% 2.90/1.01    v2_funct_1(sK2)),
% 2.90/1.01    inference(cnf_transformation,[],[f52])).
% 2.90/1.01  
% 2.90/1.01  fof(f84,plain,(
% 2.90/1.01    v1_funct_1(sK2)),
% 2.90/1.01    inference(cnf_transformation,[],[f52])).
% 2.90/1.01  
% 2.90/1.01  fof(f12,axiom,(
% 2.90/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f34,plain,(
% 2.90/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/1.01    inference(ennf_transformation,[],[f12])).
% 2.90/1.01  
% 2.90/1.01  fof(f67,plain,(
% 2.90/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/1.01    inference(cnf_transformation,[],[f34])).
% 2.90/1.01  
% 2.90/1.01  fof(f20,axiom,(
% 2.90/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f44,plain,(
% 2.90/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/1.01    inference(ennf_transformation,[],[f20])).
% 2.90/1.01  
% 2.90/1.01  fof(f45,plain,(
% 2.90/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/1.01    inference(flattening,[],[f44])).
% 2.90/1.01  
% 2.90/1.01  fof(f83,plain,(
% 2.90/1.01    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/1.01    inference(cnf_transformation,[],[f45])).
% 2.90/1.01  
% 2.90/1.01  fof(f66,plain,(
% 2.90/1.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/1.01    inference(cnf_transformation,[],[f33])).
% 2.90/1.01  
% 2.90/1.01  fof(f9,axiom,(
% 2.90/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f28,plain,(
% 2.90/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.90/1.01    inference(ennf_transformation,[],[f9])).
% 2.90/1.01  
% 2.90/1.01  fof(f29,plain,(
% 2.90/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.90/1.01    inference(flattening,[],[f28])).
% 2.90/1.01  
% 2.90/1.01  fof(f63,plain,(
% 2.90/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/1.01    inference(cnf_transformation,[],[f29])).
% 2.90/1.01  
% 2.90/1.01  fof(f62,plain,(
% 2.90/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/1.01    inference(cnf_transformation,[],[f29])).
% 2.90/1.01  
% 2.90/1.01  fof(f82,plain,(
% 2.90/1.01    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.90/1.01    inference(cnf_transformation,[],[f45])).
% 2.90/1.01  
% 2.90/1.01  fof(f89,plain,(
% 2.90/1.01    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 2.90/1.01    inference(cnf_transformation,[],[f52])).
% 2.90/1.01  
% 2.90/1.01  fof(f3,axiom,(
% 2.90/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f48,plain,(
% 2.90/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.90/1.01    inference(nnf_transformation,[],[f3])).
% 2.90/1.01  
% 2.90/1.01  fof(f49,plain,(
% 2.90/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.90/1.01    inference(flattening,[],[f48])).
% 2.90/1.01  
% 2.90/1.01  fof(f56,plain,(
% 2.90/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.90/1.01    inference(cnf_transformation,[],[f49])).
% 2.90/1.01  
% 2.90/1.01  fof(f91,plain,(
% 2.90/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.90/1.01    inference(equality_resolution,[],[f56])).
% 2.90/1.01  
% 2.90/1.01  fof(f78,plain,(
% 2.90/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/1.01    inference(cnf_transformation,[],[f50])).
% 2.90/1.01  
% 2.90/1.01  fof(f95,plain,(
% 2.90/1.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.90/1.01    inference(equality_resolution,[],[f78])).
% 2.90/1.01  
% 2.90/1.01  fof(f18,axiom,(
% 2.90/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f41,plain,(
% 2.90/1.01    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.90/1.01    inference(ennf_transformation,[],[f18])).
% 2.90/1.01  
% 2.90/1.01  fof(f74,plain,(
% 2.90/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.90/1.01    inference(cnf_transformation,[],[f41])).
% 2.90/1.01  
% 2.90/1.01  fof(f17,axiom,(
% 2.90/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f39,plain,(
% 2.90/1.01    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/1.01    inference(ennf_transformation,[],[f17])).
% 2.90/1.01  
% 2.90/1.01  fof(f40,plain,(
% 2.90/1.01    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.90/1.01    inference(flattening,[],[f39])).
% 2.90/1.01  
% 2.90/1.01  fof(f73,plain,(
% 2.90/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/1.01    inference(cnf_transformation,[],[f40])).
% 2.90/1.01  
% 2.90/1.01  fof(f13,axiom,(
% 2.90/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f35,plain,(
% 2.90/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.90/1.01    inference(ennf_transformation,[],[f13])).
% 2.90/1.01  
% 2.90/1.01  fof(f68,plain,(
% 2.90/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.90/1.01    inference(cnf_transformation,[],[f35])).
% 2.90/1.01  
% 2.90/1.01  fof(f8,axiom,(
% 2.90/1.01    ! [X0] : (v1_xboole_0(X0) => v1_funct_1(X0))),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f27,plain,(
% 2.90/1.01    ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0))),
% 2.90/1.01    inference(ennf_transformation,[],[f8])).
% 2.90/1.01  
% 2.90/1.01  fof(f61,plain,(
% 2.90/1.01    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 2.90/1.01    inference(cnf_transformation,[],[f27])).
% 2.90/1.01  
% 2.90/1.01  fof(f76,plain,(
% 2.90/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.90/1.01    inference(cnf_transformation,[],[f50])).
% 2.90/1.01  
% 2.90/1.01  fof(f96,plain,(
% 2.90/1.01    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.90/1.01    inference(equality_resolution,[],[f76])).
% 2.90/1.01  
% 2.90/1.01  fof(f1,axiom,(
% 2.90/1.01    v1_xboole_0(k1_xboole_0)),
% 2.90/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.90/1.01  
% 2.90/1.01  fof(f53,plain,(
% 2.90/1.01    v1_xboole_0(k1_xboole_0)),
% 2.90/1.01    inference(cnf_transformation,[],[f1])).
% 2.90/1.01  
% 2.90/1.01  cnf(c_27,plain,
% 2.90/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.90/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.90/1.01      | k1_xboole_0 = X2 ),
% 2.90/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_35,negated_conjecture,
% 2.90/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 2.90/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1251,plain,
% 2.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.90/1.01      | sK0 != X1
% 2.90/1.01      | sK1 != X2
% 2.90/1.01      | sK2 != X0
% 2.90/1.01      | k1_xboole_0 = X2 ),
% 2.90/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_35]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1252,plain,
% 2.90/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.90/1.01      | k1_relset_1(sK0,sK1,sK2) = sK0
% 2.90/1.01      | k1_xboole_0 = sK1 ),
% 2.90/1.01      inference(unflattening,[status(thm)],[c_1251]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_34,negated_conjecture,
% 2.90/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.90/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1254,plain,
% 2.90/1.01      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 2.90/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1252,c_34]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2195,plain,
% 2.90/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_17,plain,
% 2.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2198,plain,
% 2.90/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.90/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_4666,plain,
% 2.90/1.01      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 2.90/1.01      inference(superposition,[status(thm)],[c_2195,c_2198]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_4826,plain,
% 2.90/1.01      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 2.90/1.01      inference(superposition,[status(thm)],[c_1254,c_4666]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_18,plain,
% 2.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2197,plain,
% 2.90/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.90/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_3495,plain,
% 2.90/1.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 2.90/1.01      inference(superposition,[status(thm)],[c_2195,c_2197]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_32,negated_conjecture,
% 2.90/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 2.90/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_3507,plain,
% 2.90/1.01      ( k2_relat_1(sK2) = sK1 ),
% 2.90/1.01      inference(light_normalisation,[status(thm)],[c_3495,c_32]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_13,plain,
% 2.90/1.01      ( ~ v2_funct_1(X0)
% 2.90/1.01      | ~ v1_funct_1(X0)
% 2.90/1.01      | ~ v1_relat_1(X0)
% 2.90/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_33,negated_conjecture,
% 2.90/1.01      ( v2_funct_1(sK2) ),
% 2.90/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_388,plain,
% 2.90/1.01      ( ~ v1_funct_1(X0)
% 2.90/1.01      | ~ v1_relat_1(X0)
% 2.90/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.90/1.01      | sK2 != X0 ),
% 2.90/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_33]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_389,plain,
% 2.90/1.01      ( ~ v1_funct_1(sK2)
% 2.90/1.01      | ~ v1_relat_1(sK2)
% 2.90/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.90/1.01      inference(unflattening,[status(thm)],[c_388]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_36,negated_conjecture,
% 2.90/1.01      ( v1_funct_1(sK2) ),
% 2.90/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_391,plain,
% 2.90/1.01      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.90/1.01      inference(global_propositional_subsumption,[status(thm)],[c_389,c_36]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2193,plain,
% 2.90/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.90/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_391]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_14,plain,
% 2.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2478,plain,
% 2.90/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.90/1.01      | v1_relat_1(sK2) ),
% 2.90/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2491,plain,
% 2.90/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.90/1.01      inference(global_propositional_subsumption,
% 2.90/1.01                [status(thm)],
% 2.90/1.01                [c_2193,c_36,c_34,c_389,c_2478]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_3599,plain,
% 2.90/1.01      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 2.90/1.01      inference(demodulation,[status(thm)],[c_3507,c_2491]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_28,plain,
% 2.90/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.90/1.01      | ~ v1_funct_1(X0)
% 2.90/1.01      | ~ v1_relat_1(X0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2196,plain,
% 2.90/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.90/1.01      | v1_funct_1(X0) != iProver_top
% 2.90/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_3619,plain,
% 2.90/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 2.90/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.90/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/1.01      inference(superposition,[status(thm)],[c_3599,c_2196]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_12,plain,
% 2.90/1.01      ( ~ v2_funct_1(X0)
% 2.90/1.01      | ~ v1_funct_1(X0)
% 2.90/1.01      | ~ v1_relat_1(X0)
% 2.90/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_402,plain,
% 2.90/1.01      ( ~ v1_funct_1(X0)
% 2.90/1.01      | ~ v1_relat_1(X0)
% 2.90/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.90/1.01      | sK2 != X0 ),
% 2.90/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_33]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_403,plain,
% 2.90/1.01      ( ~ v1_funct_1(sK2)
% 2.90/1.01      | ~ v1_relat_1(sK2)
% 2.90/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.90/1.01      inference(unflattening,[status(thm)],[c_402]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_405,plain,
% 2.90/1.01      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.90/1.01      inference(global_propositional_subsumption,[status(thm)],[c_403,c_36]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2192,plain,
% 2.90/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.90/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_405]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2487,plain,
% 2.90/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.90/1.01      inference(global_propositional_subsumption,
% 2.90/1.01                [status(thm)],
% 2.90/1.01                [c_2192,c_36,c_34,c_403,c_2478]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_3620,plain,
% 2.90/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 2.90/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.90/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/1.01      inference(light_normalisation,[status(thm)],[c_3619,c_2487]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_37,plain,
% 2.90/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_39,plain,
% 2.90/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2479,plain,
% 2.90/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.90/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_2478]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_9,plain,
% 2.90/1.01      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2543,plain,
% 2.90/1.01      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 2.90/1.01      inference(instantiation,[status(thm)],[c_9]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2544,plain,
% 2.90/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.90/1.01      | v1_funct_1(sK2) != iProver_top
% 2.90/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_2543]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_10,plain,
% 2.90/1.01      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.90/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_3246,plain,
% 2.90/1.01      ( ~ v1_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) ),
% 2.90/1.01      inference(instantiation,[status(thm)],[c_10]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_3247,plain,
% 2.90/1.01      ( v1_funct_1(sK2) != iProver_top
% 2.90/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.90/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_3246]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_4183,plain,
% 2.90/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 2.90/1.01      inference(global_propositional_subsumption,
% 2.90/1.01                [status(thm)],
% 2.90/1.01                [c_3620,c_37,c_39,c_2479,c_2544,c_3247]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_4886,plain,
% 2.90/1.01      ( sK1 = k1_xboole_0
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 2.90/1.01      inference(superposition,[status(thm)],[c_4826,c_4183]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_29,plain,
% 2.90/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.90/1.01      | ~ v1_funct_1(X0)
% 2.90/1.01      | ~ v1_relat_1(X0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_31,negated_conjecture,
% 2.90/1.01      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 2.90/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/1.01      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 2.90/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1358,plain,
% 2.90/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/1.01      | ~ v1_funct_1(X0)
% 2.90/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/1.01      | ~ v1_relat_1(X0)
% 2.90/1.01      | k2_funct_1(sK2) != X0
% 2.90/1.01      | k2_relat_1(X0) != sK0
% 2.90/1.01      | k1_relat_1(X0) != sK1 ),
% 2.90/1.01      inference(resolution_lifted,[status(thm)],[c_29,c_31]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1359,plain,
% 2.90/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/1.01      | ~ v1_relat_1(k2_funct_1(sK2))
% 2.90/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.90/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.90/1.01      inference(unflattening,[status(thm)],[c_1358]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1371,plain,
% 2.90/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.90/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 2.90/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_1359,c_14]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2181,plain,
% 2.90/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.90/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.90/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_1371]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1376,plain,
% 2.90/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.90/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.90/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_1371]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2649,plain,
% 2.90/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.90/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.90/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 2.90/1.01      inference(global_propositional_subsumption,
% 2.90/1.01                [status(thm)],
% 2.90/1.01                [c_2181,c_37,c_39,c_1376,c_2479,c_2544]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2650,plain,
% 2.90/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 2.90/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.90/1.01      inference(renaming,[status(thm)],[c_2649]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2653,plain,
% 2.90/1.01      ( k2_relat_1(sK2) != sK1
% 2.90/1.01      | k1_relat_1(sK2) != sK0
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.90/1.01      inference(light_normalisation,[status(thm)],[c_2650,c_2487,c_2491]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_3598,plain,
% 2.90/1.01      ( k1_relat_1(sK2) != sK0
% 2.90/1.01      | sK1 != sK1
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.90/1.01      inference(demodulation,[status(thm)],[c_3507,c_2653]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_3602,plain,
% 2.90/1.01      ( k1_relat_1(sK2) != sK0
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.90/1.01      inference(equality_resolution_simp,[status(thm)],[c_3598]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_4887,plain,
% 2.90/1.01      ( sK1 = k1_xboole_0
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.90/1.01      inference(superposition,[status(thm)],[c_4826,c_3602]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_4901,plain,
% 2.90/1.01      ( sK1 = k1_xboole_0 ),
% 2.90/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_4886,c_4887]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_5032,plain,
% 2.90/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 2.90/1.01      inference(demodulation,[status(thm)],[c_4901,c_4183]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_3,plain,
% 2.90/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.90/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_5111,plain,
% 2.90/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.90/1.01      inference(demodulation,[status(thm)],[c_5032,c_3]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_24,plain,
% 2.90/1.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.90/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.90/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.90/1.01      inference(cnf_transformation,[],[f95]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1337,plain,
% 2.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.90/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.90/1.01      | k2_funct_1(sK2) != X0
% 2.90/1.01      | sK0 != X1
% 2.90/1.01      | sK1 != k1_xboole_0 ),
% 2.90/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1338,plain,
% 2.90/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.90/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/1.01      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 2.90/1.01      | sK1 != k1_xboole_0 ),
% 2.90/1.01      inference(unflattening,[status(thm)],[c_1337]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_21,plain,
% 2.90/1.01      ( v1_partfun1(X0,X1)
% 2.90/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.01      | ~ v1_xboole_0(X1) ),
% 2.90/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_19,plain,
% 2.90/1.01      ( v1_funct_2(X0,X1,X2)
% 2.90/1.01      | ~ v1_partfun1(X0,X1)
% 2.90/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.01      | ~ v1_funct_1(X0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_364,plain,
% 2.90/1.01      ( v1_funct_2(X0,X1,X2)
% 2.90/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.90/1.01      | ~ v1_funct_1(X0)
% 2.90/1.01      | ~ v1_xboole_0(X1) ),
% 2.90/1.01      inference(resolution,[status(thm)],[c_21,c_19]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_15,plain,
% 2.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.01      | ~ v1_xboole_0(X1)
% 2.90/1.01      | v1_xboole_0(X0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_8,plain,
% 2.90/1.01      ( v1_funct_1(X0) | ~ v1_xboole_0(X0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_368,plain,
% 2.90/1.01      ( v1_funct_2(X0,X1,X2)
% 2.90/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.01      | ~ v1_xboole_0(X1) ),
% 2.90/1.01      inference(global_propositional_subsumption,
% 2.90/1.01                [status(thm)],
% 2.90/1.01                [c_364,c_21,c_19,c_15,c_8]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_26,plain,
% 2.90/1.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.90/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.90/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.90/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1176,plain,
% 2.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 2.90/1.01      | ~ v1_xboole_0(X1)
% 2.90/1.01      | X3 != X0
% 2.90/1.01      | X4 != X2
% 2.90/1.01      | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
% 2.90/1.01      | k1_xboole_0 != X1 ),
% 2.90/1.01      inference(resolution_lifted,[status(thm)],[c_368,c_26]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1177,plain,
% 2.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.90/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 2.90/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.90/1.01      inference(unflattening,[status(thm)],[c_1176]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_0,plain,
% 2.90/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.90/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1181,plain,
% 2.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.90/1.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.90/1.01      inference(global_propositional_subsumption,[status(thm)],[c_1177,c_0]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1345,plain,
% 2.90/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 2.90/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/1.01      | sK1 != k1_xboole_0 ),
% 2.90/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_1338,c_1181]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2182,plain,
% 2.90/1.01      ( sK1 != k1_xboole_0
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 2.90/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_1345]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2385,plain,
% 2.90/1.01      ( sK1 != k1_xboole_0
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.90/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.90/1.01      inference(demodulation,[status(thm)],[c_2182,c_3]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_117,plain,
% 2.90/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1222,plain,
% 2.90/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.90/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/1.01      | ~ v1_xboole_0(X1)
% 2.90/1.01      | k2_funct_1(sK2) != X0
% 2.90/1.01      | sK0 != X2
% 2.90/1.01      | sK1 != X1 ),
% 2.90/1.01      inference(resolution_lifted,[status(thm)],[c_368,c_31]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1223,plain,
% 2.90/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 2.90/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 2.90/1.01      | ~ v1_xboole_0(sK1) ),
% 2.90/1.01      inference(unflattening,[status(thm)],[c_1222]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1224,plain,
% 2.90/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 2.90/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.90/1.01      | v1_xboole_0(sK1) != iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_1223]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_1658,plain,
% 2.90/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.90/1.01      theory(equality) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2481,plain,
% 2.90/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 2.90/1.01      inference(instantiation,[status(thm)],[c_1658]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2482,plain,
% 2.90/1.01      ( sK1 != X0
% 2.90/1.01      | v1_xboole_0(X0) != iProver_top
% 2.90/1.01      | v1_xboole_0(sK1) = iProver_top ),
% 2.90/1.01      inference(predicate_to_equality,[status(thm)],[c_2481]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2484,plain,
% 2.90/1.01      ( sK1 != k1_xboole_0
% 2.90/1.01      | v1_xboole_0(sK1) = iProver_top
% 2.90/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.90/1.01      inference(instantiation,[status(thm)],[c_2482]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_2724,plain,
% 2.90/1.01      ( sK1 != k1_xboole_0
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 2.90/1.01      inference(global_propositional_subsumption,
% 2.90/1.01                [status(thm)],
% 2.90/1.01                [c_2385,c_37,c_39,c_117,c_1224,c_2479,c_2484,c_2544]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_5040,plain,
% 2.90/1.01      ( k1_xboole_0 != k1_xboole_0
% 2.90/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.90/1.01      inference(demodulation,[status(thm)],[c_4901,c_2724]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_5091,plain,
% 2.90/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top ),
% 2.90/1.01      inference(equality_resolution_simp,[status(thm)],[c_5040]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_5093,plain,
% 2.90/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.90/1.01      inference(demodulation,[status(thm)],[c_5091,c_3]) ).
% 2.90/1.01  
% 2.90/1.01  cnf(c_5113,plain,
% 2.90/1.01      ( $false ),
% 2.90/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_5111,c_5093]) ).
% 2.90/1.01  
% 2.90/1.01  
% 2.90/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.90/1.01  
% 2.90/1.01  ------                               Statistics
% 2.90/1.01  
% 2.90/1.01  ------ General
% 2.90/1.01  
% 2.90/1.01  abstr_ref_over_cycles:                  0
% 2.90/1.01  abstr_ref_under_cycles:                 0
% 2.90/1.01  gc_basic_clause_elim:                   0
% 2.90/1.01  forced_gc_time:                         0
% 2.90/1.01  parsing_time:                           0.011
% 2.90/1.01  unif_index_cands_time:                  0.
% 2.90/1.01  unif_index_add_time:                    0.
% 2.90/1.01  orderings_time:                         0.
% 2.90/1.01  out_proof_time:                         0.01
% 2.90/1.01  total_time:                             0.166
% 2.90/1.01  num_of_symbols:                         51
% 2.90/1.01  num_of_terms:                           3745
% 2.90/1.01  
% 2.90/1.01  ------ Preprocessing
% 2.90/1.01  
% 2.90/1.01  num_of_splits:                          0
% 2.90/1.01  num_of_split_atoms:                     0
% 2.90/1.01  num_of_reused_defs:                     0
% 2.90/1.01  num_eq_ax_congr_red:                    5
% 2.90/1.01  num_of_sem_filtered_clauses:            1
% 2.90/1.01  num_of_subtypes:                        0
% 2.90/1.01  monotx_restored_types:                  0
% 2.90/1.01  sat_num_of_epr_types:                   0
% 2.90/1.01  sat_num_of_non_cyclic_types:            0
% 2.90/1.01  sat_guarded_non_collapsed_types:        0
% 2.90/1.01  num_pure_diseq_elim:                    0
% 2.90/1.01  simp_replaced_by:                       0
% 2.90/1.01  res_preprocessed:                       171
% 2.90/1.01  prep_upred:                             0
% 2.90/1.01  prep_unflattend:                        88
% 2.90/1.01  smt_new_axioms:                         0
% 2.90/1.01  pred_elim_cands:                        4
% 2.90/1.01  pred_elim:                              3
% 2.90/1.01  pred_elim_cl:                           0
% 2.90/1.01  pred_elim_cycles:                       6
% 2.90/1.01  merged_defs:                            0
% 2.90/1.01  merged_defs_ncl:                        0
% 2.90/1.01  bin_hyper_res:                          0
% 2.90/1.01  prep_cycles:                            4
% 2.90/1.01  pred_elim_time:                         0.021
% 2.90/1.01  splitting_time:                         0.
% 2.90/1.01  sem_filter_time:                        0.
% 2.90/1.01  monotx_time:                            0.
% 2.90/1.01  subtype_inf_time:                       0.
% 2.90/1.01  
% 2.90/1.01  ------ Problem properties
% 2.90/1.01  
% 2.90/1.01  clauses:                                35
% 2.90/1.01  conjectures:                            3
% 2.90/1.01  epr:                                    4
% 2.90/1.01  horn:                                   29
% 2.90/1.01  ground:                                 14
% 2.90/1.01  unary:                                  7
% 2.90/1.01  binary:                                 12
% 2.90/1.01  lits:                                   90
% 2.90/1.01  lits_eq:                                37
% 2.90/1.01  fd_pure:                                0
% 2.90/1.01  fd_pseudo:                              0
% 2.90/1.01  fd_cond:                                3
% 2.90/1.01  fd_pseudo_cond:                         0
% 2.90/1.01  ac_symbols:                             0
% 2.90/1.01  
% 2.90/1.01  ------ Propositional Solver
% 2.90/1.01  
% 2.90/1.01  prop_solver_calls:                      28
% 2.90/1.01  prop_fast_solver_calls:                 1256
% 2.90/1.01  smt_solver_calls:                       0
% 2.90/1.01  smt_fast_solver_calls:                  0
% 2.90/1.01  prop_num_of_clauses:                    1547
% 2.90/1.01  prop_preprocess_simplified:             6434
% 2.90/1.01  prop_fo_subsumed:                       26
% 2.90/1.01  prop_solver_time:                       0.
% 2.90/1.01  smt_solver_time:                        0.
% 2.90/1.01  smt_fast_solver_time:                   0.
% 2.90/1.01  prop_fast_solver_time:                  0.
% 2.90/1.01  prop_unsat_core_time:                   0.
% 2.90/1.01  
% 2.90/1.01  ------ QBF
% 2.90/1.01  
% 2.90/1.01  qbf_q_res:                              0
% 2.90/1.01  qbf_num_tautologies:                    0
% 2.90/1.01  qbf_prep_cycles:                        0
% 2.90/1.01  
% 2.90/1.01  ------ BMC1
% 2.90/1.01  
% 2.90/1.01  bmc1_current_bound:                     -1
% 2.90/1.01  bmc1_last_solved_bound:                 -1
% 2.90/1.01  bmc1_unsat_core_size:                   -1
% 2.90/1.01  bmc1_unsat_core_parents_size:           -1
% 2.90/1.01  bmc1_merge_next_fun:                    0
% 2.90/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.90/1.01  
% 2.90/1.01  ------ Instantiation
% 2.90/1.01  
% 2.90/1.01  inst_num_of_clauses:                    511
% 2.90/1.01  inst_num_in_passive:                    191
% 2.90/1.01  inst_num_in_active:                     246
% 2.90/1.01  inst_num_in_unprocessed:                74
% 2.90/1.01  inst_num_of_loops:                      290
% 2.90/1.01  inst_num_of_learning_restarts:          0
% 2.90/1.01  inst_num_moves_active_passive:          41
% 2.90/1.01  inst_lit_activity:                      0
% 2.90/1.01  inst_lit_activity_moves:                0
% 2.90/1.01  inst_num_tautologies:                   0
% 2.90/1.01  inst_num_prop_implied:                  0
% 2.90/1.01  inst_num_existing_simplified:           0
% 2.90/1.01  inst_num_eq_res_simplified:             0
% 2.90/1.01  inst_num_child_elim:                    0
% 2.90/1.01  inst_num_of_dismatching_blockings:      138
% 2.90/1.01  inst_num_of_non_proper_insts:           371
% 2.90/1.01  inst_num_of_duplicates:                 0
% 2.90/1.01  inst_inst_num_from_inst_to_res:         0
% 2.90/1.01  inst_dismatching_checking_time:         0.
% 2.90/1.01  
% 2.90/1.01  ------ Resolution
% 2.90/1.01  
% 2.90/1.01  res_num_of_clauses:                     0
% 2.90/1.01  res_num_in_passive:                     0
% 2.90/1.01  res_num_in_active:                      0
% 2.90/1.01  res_num_of_loops:                       175
% 2.90/1.01  res_forward_subset_subsumed:            24
% 2.90/1.01  res_backward_subset_subsumed:           2
% 2.90/1.01  res_forward_subsumed:                   4
% 2.90/1.01  res_backward_subsumed:                  0
% 2.90/1.01  res_forward_subsumption_resolution:     5
% 2.90/1.01  res_backward_subsumption_resolution:    0
% 2.90/1.01  res_clause_to_clause_subsumption:       160
% 2.90/1.01  res_orphan_elimination:                 0
% 2.90/1.01  res_tautology_del:                      59
% 2.90/1.01  res_num_eq_res_simplified:              0
% 2.90/1.01  res_num_sel_changes:                    0
% 2.90/1.01  res_moves_from_active_to_pass:          0
% 2.90/1.01  
% 2.90/1.01  ------ Superposition
% 2.90/1.01  
% 2.90/1.01  sup_time_total:                         0.
% 2.90/1.01  sup_time_generating:                    0.
% 2.90/1.01  sup_time_sim_full:                      0.
% 2.90/1.01  sup_time_sim_immed:                     0.
% 2.90/1.01  
% 2.90/1.01  sup_num_of_clauses:                     50
% 2.90/1.01  sup_num_in_active:                      27
% 2.90/1.01  sup_num_in_passive:                     23
% 2.90/1.01  sup_num_of_loops:                       56
% 2.90/1.01  sup_fw_superposition:                   36
% 2.90/1.01  sup_bw_superposition:                   19
% 2.90/1.01  sup_immediate_simplified:               15
% 2.90/1.01  sup_given_eliminated:                   1
% 2.90/1.01  comparisons_done:                       0
% 2.90/1.01  comparisons_avoided:                    11
% 2.90/1.01  
% 2.90/1.01  ------ Simplifications
% 2.90/1.01  
% 2.90/1.01  
% 2.90/1.01  sim_fw_subset_subsumed:                 10
% 2.90/1.01  sim_bw_subset_subsumed:                 3
% 2.90/1.01  sim_fw_subsumed:                        1
% 2.90/1.01  sim_bw_subsumed:                        5
% 2.90/1.01  sim_fw_subsumption_res:                 2
% 2.90/1.01  sim_bw_subsumption_res:                 1
% 2.90/1.01  sim_tautology_del:                      1
% 2.90/1.01  sim_eq_tautology_del:                   3
% 2.90/1.01  sim_eq_res_simp:                        3
% 2.90/1.01  sim_fw_demodulated:                     12
% 2.90/1.01  sim_bw_demodulated:                     27
% 2.90/1.01  sim_light_normalised:                   10
% 2.90/1.01  sim_joinable_taut:                      0
% 2.90/1.01  sim_joinable_simp:                      0
% 2.90/1.01  sim_ac_normalised:                      0
% 2.90/1.01  sim_smt_subsumption:                    0
% 2.90/1.01  
%------------------------------------------------------------------------------
