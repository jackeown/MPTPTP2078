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
% DateTime   : Thu Dec  3 12:02:27 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  154 (1361 expanded)
%              Number of clauses        :   95 ( 421 expanded)
%              Number of leaves         :   14 ( 265 expanded)
%              Depth                    :   21
%              Number of atoms          :  511 (7388 expanded)
%              Number of equality atoms :  217 (1469 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,axiom,(
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

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
        | ~ v1_funct_1(k2_funct_1(sK4)) )
      & k2_relset_1(sK2,sK3,sK4) = sK3
      & v2_funct_1(sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f45])).

fof(f77,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f46])).

fof(f78,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f76,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f75,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f58,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f56,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f55,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f74,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f83,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f70])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1271,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_1272,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_1271])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1274,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1272,c_32])).

cnf(c_2016,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_2019,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4691,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2016,c_2019])).

cnf(c_4967,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1274,c_4691])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2018,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3619,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2016,c_2018])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3631,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_3619,c_30])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_360,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_31])).

cnf(c_361,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_363,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_34])).

cnf(c_2014,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_363])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_2318,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2336,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2014,c_34,c_32,c_361,c_2318])).

cnf(c_3649,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_3631,c_2336])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2017,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3914,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k2_relat_1(k2_funct_1(sK4))))) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3649,c_2017])).

cnf(c_10,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_374,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_31])).

cnf(c_375,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_374])).

cnf(c_377,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_375,c_34])).

cnf(c_2013,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_2332,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2013,c_34,c_32,c_375,c_2318])).

cnf(c_3915,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3914,c_2332])).

cnf(c_35,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_37,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2319,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2318])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_2387,plain,
    ( ~ v1_relat_1(sK4)
    | v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2388,plain,
    ( v1_relat_1(sK4) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2387])).

cnf(c_9,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2386,plain,
    ( v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4)
    | ~ v1_funct_1(sK4) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2390,plain,
    ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2386])).

cnf(c_4309,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3915,c_35,c_37,c_2319,c_2388,c_2390])).

cnf(c_5110,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4967,c_4309])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_29,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1388,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(X0) != sK3
    | k2_relat_1(X0) != sK2
    | k2_funct_1(sK4) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_29])).

cnf(c_1389,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1388])).

cnf(c_1401,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1389,c_12])).

cnf(c_2001,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1401])).

cnf(c_1406,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1401])).

cnf(c_2401,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2001,c_35,c_37,c_1406,c_2319,c_2388])).

cnf(c_2402,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2401])).

cnf(c_2405,plain,
    ( k1_relat_1(sK4) != sK2
    | k2_relat_1(sK4) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2402,c_2332,c_2336])).

cnf(c_3648,plain,
    ( k1_relat_1(sK4) != sK2
    | sK3 != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3631,c_2405])).

cnf(c_3652,plain,
    ( k1_relat_1(sK4) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3648])).

cnf(c_5111,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4967,c_3652])).

cnf(c_5121,plain,
    ( sK3 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5110,c_5111])).

cnf(c_5161,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5121,c_4309])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_5246,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5161,c_4])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK4) != X0
    | sK2 != X1
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_1358,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1357])).

cnf(c_19,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_17,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_334,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_19,c_17])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_334,c_19,c_17])).

cnf(c_339,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_338])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1193,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1)
    | X3 != X0
    | X4 != X2
    | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_339,c_24])).

cnf(c_1194,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1193])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1198,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1194,c_0])).

cnf(c_1199,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1198])).

cnf(c_1365,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | sK3 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1358,c_1199])).

cnf(c_2003,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1365])).

cnf(c_2207,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2003,c_4])).

cnf(c_107,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1242,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_xboole_0(X1)
    | k2_funct_1(sK4) != X0
    | sK2 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_339,c_29])).

cnf(c_1243,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1242])).

cnf(c_1244,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1243])).

cnf(c_1494,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2321,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1494])).

cnf(c_2322,plain,
    ( sK3 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2321])).

cnf(c_2324,plain,
    ( sK3 != k1_xboole_0
    | v1_xboole_0(sK3) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2322])).

cnf(c_2797,plain,
    ( sK3 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2207,c_35,c_37,c_107,c_1244,c_2319,c_2324,c_2388])).

cnf(c_5168,plain,
    ( k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5121,c_2797])).

cnf(c_5228,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5168])).

cnf(c_5230,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5228,c_4])).

cnf(c_5248,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5246,c_5230])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:26:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 2.65/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.65/0.98  
% 2.65/0.98  ------  iProver source info
% 2.65/0.98  
% 2.65/0.98  git: date: 2020-06-30 10:37:57 +0100
% 2.65/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.65/0.98  git: non_committed_changes: false
% 2.65/0.98  git: last_make_outside_of_git: false
% 2.65/0.98  
% 2.65/0.98  ------ 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options
% 2.65/0.98  
% 2.65/0.98  --out_options                           all
% 2.65/0.98  --tptp_safe_out                         true
% 2.65/0.98  --problem_path                          ""
% 2.65/0.98  --include_path                          ""
% 2.65/0.98  --clausifier                            res/vclausify_rel
% 2.65/0.98  --clausifier_options                    --mode clausify
% 2.65/0.98  --stdin                                 false
% 2.65/0.98  --stats_out                             all
% 2.65/0.98  
% 2.65/0.98  ------ General Options
% 2.65/0.98  
% 2.65/0.98  --fof                                   false
% 2.65/0.98  --time_out_real                         305.
% 2.65/0.98  --time_out_virtual                      -1.
% 2.65/0.98  --symbol_type_check                     false
% 2.65/0.98  --clausify_out                          false
% 2.65/0.98  --sig_cnt_out                           false
% 2.65/0.98  --trig_cnt_out                          false
% 2.65/0.98  --trig_cnt_out_tolerance                1.
% 2.65/0.98  --trig_cnt_out_sk_spl                   false
% 2.65/0.98  --abstr_cl_out                          false
% 2.65/0.98  
% 2.65/0.98  ------ Global Options
% 2.65/0.98  
% 2.65/0.98  --schedule                              default
% 2.65/0.98  --add_important_lit                     false
% 2.65/0.98  --prop_solver_per_cl                    1000
% 2.65/0.98  --min_unsat_core                        false
% 2.65/0.98  --soft_assumptions                      false
% 2.65/0.98  --soft_lemma_size                       3
% 2.65/0.98  --prop_impl_unit_size                   0
% 2.65/0.98  --prop_impl_unit                        []
% 2.65/0.98  --share_sel_clauses                     true
% 2.65/0.98  --reset_solvers                         false
% 2.65/0.98  --bc_imp_inh                            [conj_cone]
% 2.65/0.98  --conj_cone_tolerance                   3.
% 2.65/0.98  --extra_neg_conj                        none
% 2.65/0.98  --large_theory_mode                     true
% 2.65/0.98  --prolific_symb_bound                   200
% 2.65/0.98  --lt_threshold                          2000
% 2.65/0.98  --clause_weak_htbl                      true
% 2.65/0.98  --gc_record_bc_elim                     false
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing Options
% 2.65/0.98  
% 2.65/0.98  --preprocessing_flag                    true
% 2.65/0.98  --time_out_prep_mult                    0.1
% 2.65/0.98  --splitting_mode                        input
% 2.65/0.98  --splitting_grd                         true
% 2.65/0.98  --splitting_cvd                         false
% 2.65/0.98  --splitting_cvd_svl                     false
% 2.65/0.98  --splitting_nvd                         32
% 2.65/0.98  --sub_typing                            true
% 2.65/0.98  --prep_gs_sim                           true
% 2.65/0.98  --prep_unflatten                        true
% 2.65/0.98  --prep_res_sim                          true
% 2.65/0.98  --prep_upred                            true
% 2.65/0.98  --prep_sem_filter                       exhaustive
% 2.65/0.98  --prep_sem_filter_out                   false
% 2.65/0.98  --pred_elim                             true
% 2.65/0.98  --res_sim_input                         true
% 2.65/0.98  --eq_ax_congr_red                       true
% 2.65/0.98  --pure_diseq_elim                       true
% 2.65/0.98  --brand_transform                       false
% 2.65/0.98  --non_eq_to_eq                          false
% 2.65/0.98  --prep_def_merge                        true
% 2.65/0.98  --prep_def_merge_prop_impl              false
% 2.65/0.98  --prep_def_merge_mbd                    true
% 2.65/0.98  --prep_def_merge_tr_red                 false
% 2.65/0.98  --prep_def_merge_tr_cl                  false
% 2.65/0.98  --smt_preprocessing                     true
% 2.65/0.98  --smt_ac_axioms                         fast
% 2.65/0.98  --preprocessed_out                      false
% 2.65/0.98  --preprocessed_stats                    false
% 2.65/0.98  
% 2.65/0.98  ------ Abstraction refinement Options
% 2.65/0.98  
% 2.65/0.98  --abstr_ref                             []
% 2.65/0.98  --abstr_ref_prep                        false
% 2.65/0.98  --abstr_ref_until_sat                   false
% 2.65/0.98  --abstr_ref_sig_restrict                funpre
% 2.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.98  --abstr_ref_under                       []
% 2.65/0.98  
% 2.65/0.98  ------ SAT Options
% 2.65/0.98  
% 2.65/0.98  --sat_mode                              false
% 2.65/0.98  --sat_fm_restart_options                ""
% 2.65/0.98  --sat_gr_def                            false
% 2.65/0.98  --sat_epr_types                         true
% 2.65/0.98  --sat_non_cyclic_types                  false
% 2.65/0.98  --sat_finite_models                     false
% 2.65/0.98  --sat_fm_lemmas                         false
% 2.65/0.98  --sat_fm_prep                           false
% 2.65/0.98  --sat_fm_uc_incr                        true
% 2.65/0.98  --sat_out_model                         small
% 2.65/0.98  --sat_out_clauses                       false
% 2.65/0.98  
% 2.65/0.98  ------ QBF Options
% 2.65/0.98  
% 2.65/0.98  --qbf_mode                              false
% 2.65/0.98  --qbf_elim_univ                         false
% 2.65/0.98  --qbf_dom_inst                          none
% 2.65/0.98  --qbf_dom_pre_inst                      false
% 2.65/0.98  --qbf_sk_in                             false
% 2.65/0.98  --qbf_pred_elim                         true
% 2.65/0.98  --qbf_split                             512
% 2.65/0.98  
% 2.65/0.98  ------ BMC1 Options
% 2.65/0.98  
% 2.65/0.98  --bmc1_incremental                      false
% 2.65/0.98  --bmc1_axioms                           reachable_all
% 2.65/0.98  --bmc1_min_bound                        0
% 2.65/0.98  --bmc1_max_bound                        -1
% 2.65/0.98  --bmc1_max_bound_default                -1
% 2.65/0.98  --bmc1_symbol_reachability              true
% 2.65/0.98  --bmc1_property_lemmas                  false
% 2.65/0.98  --bmc1_k_induction                      false
% 2.65/0.98  --bmc1_non_equiv_states                 false
% 2.65/0.98  --bmc1_deadlock                         false
% 2.65/0.98  --bmc1_ucm                              false
% 2.65/0.98  --bmc1_add_unsat_core                   none
% 2.65/0.98  --bmc1_unsat_core_children              false
% 2.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.98  --bmc1_out_stat                         full
% 2.65/0.98  --bmc1_ground_init                      false
% 2.65/0.98  --bmc1_pre_inst_next_state              false
% 2.65/0.98  --bmc1_pre_inst_state                   false
% 2.65/0.98  --bmc1_pre_inst_reach_state             false
% 2.65/0.98  --bmc1_out_unsat_core                   false
% 2.65/0.98  --bmc1_aig_witness_out                  false
% 2.65/0.98  --bmc1_verbose                          false
% 2.65/0.98  --bmc1_dump_clauses_tptp                false
% 2.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.98  --bmc1_dump_file                        -
% 2.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.98  --bmc1_ucm_extend_mode                  1
% 2.65/0.98  --bmc1_ucm_init_mode                    2
% 2.65/0.98  --bmc1_ucm_cone_mode                    none
% 2.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.98  --bmc1_ucm_relax_model                  4
% 2.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.98  --bmc1_ucm_layered_model                none
% 2.65/0.98  --bmc1_ucm_max_lemma_size               10
% 2.65/0.98  
% 2.65/0.98  ------ AIG Options
% 2.65/0.98  
% 2.65/0.98  --aig_mode                              false
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation Options
% 2.65/0.98  
% 2.65/0.98  --instantiation_flag                    true
% 2.65/0.98  --inst_sos_flag                         false
% 2.65/0.98  --inst_sos_phase                        true
% 2.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel_side                     num_symb
% 2.65/0.98  --inst_solver_per_active                1400
% 2.65/0.98  --inst_solver_calls_frac                1.
% 2.65/0.98  --inst_passive_queue_type               priority_queues
% 2.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.98  --inst_passive_queues_freq              [25;2]
% 2.65/0.98  --inst_dismatching                      true
% 2.65/0.98  --inst_eager_unprocessed_to_passive     true
% 2.65/0.98  --inst_prop_sim_given                   true
% 2.65/0.98  --inst_prop_sim_new                     false
% 2.65/0.98  --inst_subs_new                         false
% 2.65/0.98  --inst_eq_res_simp                      false
% 2.65/0.98  --inst_subs_given                       false
% 2.65/0.98  --inst_orphan_elimination               true
% 2.65/0.98  --inst_learning_loop_flag               true
% 2.65/0.98  --inst_learning_start                   3000
% 2.65/0.98  --inst_learning_factor                  2
% 2.65/0.98  --inst_start_prop_sim_after_learn       3
% 2.65/0.98  --inst_sel_renew                        solver
% 2.65/0.98  --inst_lit_activity_flag                true
% 2.65/0.98  --inst_restr_to_given                   false
% 2.65/0.98  --inst_activity_threshold               500
% 2.65/0.98  --inst_out_proof                        true
% 2.65/0.98  
% 2.65/0.98  ------ Resolution Options
% 2.65/0.98  
% 2.65/0.98  --resolution_flag                       true
% 2.65/0.98  --res_lit_sel                           adaptive
% 2.65/0.98  --res_lit_sel_side                      none
% 2.65/0.98  --res_ordering                          kbo
% 2.65/0.98  --res_to_prop_solver                    active
% 2.65/0.98  --res_prop_simpl_new                    false
% 2.65/0.98  --res_prop_simpl_given                  true
% 2.65/0.98  --res_passive_queue_type                priority_queues
% 2.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.98  --res_passive_queues_freq               [15;5]
% 2.65/0.98  --res_forward_subs                      full
% 2.65/0.98  --res_backward_subs                     full
% 2.65/0.98  --res_forward_subs_resolution           true
% 2.65/0.98  --res_backward_subs_resolution          true
% 2.65/0.98  --res_orphan_elimination                true
% 2.65/0.98  --res_time_limit                        2.
% 2.65/0.98  --res_out_proof                         true
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Options
% 2.65/0.98  
% 2.65/0.98  --superposition_flag                    true
% 2.65/0.98  --sup_passive_queue_type                priority_queues
% 2.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.98  --demod_completeness_check              fast
% 2.65/0.98  --demod_use_ground                      true
% 2.65/0.98  --sup_to_prop_solver                    passive
% 2.65/0.98  --sup_prop_simpl_new                    true
% 2.65/0.98  --sup_prop_simpl_given                  true
% 2.65/0.98  --sup_fun_splitting                     false
% 2.65/0.98  --sup_smt_interval                      50000
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Simplification Setup
% 2.65/0.98  
% 2.65/0.98  --sup_indices_passive                   []
% 2.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_full_bw                           [BwDemod]
% 2.65/0.98  --sup_immed_triv                        [TrivRules]
% 2.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_immed_bw_main                     []
% 2.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  
% 2.65/0.98  ------ Combination Options
% 2.65/0.98  
% 2.65/0.98  --comb_res_mult                         3
% 2.65/0.98  --comb_sup_mult                         2
% 2.65/0.98  --comb_inst_mult                        10
% 2.65/0.98  
% 2.65/0.98  ------ Debug Options
% 2.65/0.98  
% 2.65/0.98  --dbg_backtrace                         false
% 2.65/0.98  --dbg_dump_prop_clauses                 false
% 2.65/0.98  --dbg_dump_prop_clauses_file            -
% 2.65/0.98  --dbg_out_stat                          false
% 2.65/0.98  ------ Parsing...
% 2.65/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.65/0.98  ------ Proving...
% 2.65/0.98  ------ Problem Properties 
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  clauses                                 35
% 2.65/0.98  conjectures                             3
% 2.65/0.98  EPR                                     4
% 2.65/0.98  Horn                                    28
% 2.65/0.98  unary                                   9
% 2.65/0.98  binary                                  6
% 2.65/0.98  lits                                    96
% 2.65/0.98  lits eq                                 38
% 2.65/0.98  fd_pure                                 0
% 2.65/0.98  fd_pseudo                               0
% 2.65/0.98  fd_cond                                 3
% 2.65/0.98  fd_pseudo_cond                          1
% 2.65/0.98  AC symbols                              0
% 2.65/0.98  
% 2.65/0.98  ------ Schedule dynamic 5 is on 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  ------ 
% 2.65/0.98  Current options:
% 2.65/0.98  ------ 
% 2.65/0.98  
% 2.65/0.98  ------ Input Options
% 2.65/0.98  
% 2.65/0.98  --out_options                           all
% 2.65/0.98  --tptp_safe_out                         true
% 2.65/0.98  --problem_path                          ""
% 2.65/0.98  --include_path                          ""
% 2.65/0.98  --clausifier                            res/vclausify_rel
% 2.65/0.98  --clausifier_options                    --mode clausify
% 2.65/0.98  --stdin                                 false
% 2.65/0.98  --stats_out                             all
% 2.65/0.98  
% 2.65/0.98  ------ General Options
% 2.65/0.98  
% 2.65/0.98  --fof                                   false
% 2.65/0.98  --time_out_real                         305.
% 2.65/0.98  --time_out_virtual                      -1.
% 2.65/0.98  --symbol_type_check                     false
% 2.65/0.98  --clausify_out                          false
% 2.65/0.98  --sig_cnt_out                           false
% 2.65/0.98  --trig_cnt_out                          false
% 2.65/0.98  --trig_cnt_out_tolerance                1.
% 2.65/0.98  --trig_cnt_out_sk_spl                   false
% 2.65/0.98  --abstr_cl_out                          false
% 2.65/0.98  
% 2.65/0.98  ------ Global Options
% 2.65/0.98  
% 2.65/0.98  --schedule                              default
% 2.65/0.98  --add_important_lit                     false
% 2.65/0.98  --prop_solver_per_cl                    1000
% 2.65/0.98  --min_unsat_core                        false
% 2.65/0.98  --soft_assumptions                      false
% 2.65/0.98  --soft_lemma_size                       3
% 2.65/0.98  --prop_impl_unit_size                   0
% 2.65/0.98  --prop_impl_unit                        []
% 2.65/0.98  --share_sel_clauses                     true
% 2.65/0.98  --reset_solvers                         false
% 2.65/0.98  --bc_imp_inh                            [conj_cone]
% 2.65/0.98  --conj_cone_tolerance                   3.
% 2.65/0.98  --extra_neg_conj                        none
% 2.65/0.98  --large_theory_mode                     true
% 2.65/0.98  --prolific_symb_bound                   200
% 2.65/0.98  --lt_threshold                          2000
% 2.65/0.98  --clause_weak_htbl                      true
% 2.65/0.98  --gc_record_bc_elim                     false
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing Options
% 2.65/0.98  
% 2.65/0.98  --preprocessing_flag                    true
% 2.65/0.98  --time_out_prep_mult                    0.1
% 2.65/0.98  --splitting_mode                        input
% 2.65/0.98  --splitting_grd                         true
% 2.65/0.98  --splitting_cvd                         false
% 2.65/0.98  --splitting_cvd_svl                     false
% 2.65/0.98  --splitting_nvd                         32
% 2.65/0.98  --sub_typing                            true
% 2.65/0.98  --prep_gs_sim                           true
% 2.65/0.98  --prep_unflatten                        true
% 2.65/0.98  --prep_res_sim                          true
% 2.65/0.98  --prep_upred                            true
% 2.65/0.98  --prep_sem_filter                       exhaustive
% 2.65/0.98  --prep_sem_filter_out                   false
% 2.65/0.98  --pred_elim                             true
% 2.65/0.98  --res_sim_input                         true
% 2.65/0.98  --eq_ax_congr_red                       true
% 2.65/0.98  --pure_diseq_elim                       true
% 2.65/0.98  --brand_transform                       false
% 2.65/0.98  --non_eq_to_eq                          false
% 2.65/0.98  --prep_def_merge                        true
% 2.65/0.98  --prep_def_merge_prop_impl              false
% 2.65/0.98  --prep_def_merge_mbd                    true
% 2.65/0.98  --prep_def_merge_tr_red                 false
% 2.65/0.98  --prep_def_merge_tr_cl                  false
% 2.65/0.98  --smt_preprocessing                     true
% 2.65/0.98  --smt_ac_axioms                         fast
% 2.65/0.98  --preprocessed_out                      false
% 2.65/0.98  --preprocessed_stats                    false
% 2.65/0.98  
% 2.65/0.98  ------ Abstraction refinement Options
% 2.65/0.98  
% 2.65/0.98  --abstr_ref                             []
% 2.65/0.98  --abstr_ref_prep                        false
% 2.65/0.98  --abstr_ref_until_sat                   false
% 2.65/0.98  --abstr_ref_sig_restrict                funpre
% 2.65/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 2.65/0.98  --abstr_ref_under                       []
% 2.65/0.98  
% 2.65/0.98  ------ SAT Options
% 2.65/0.98  
% 2.65/0.98  --sat_mode                              false
% 2.65/0.98  --sat_fm_restart_options                ""
% 2.65/0.98  --sat_gr_def                            false
% 2.65/0.98  --sat_epr_types                         true
% 2.65/0.98  --sat_non_cyclic_types                  false
% 2.65/0.98  --sat_finite_models                     false
% 2.65/0.98  --sat_fm_lemmas                         false
% 2.65/0.98  --sat_fm_prep                           false
% 2.65/0.98  --sat_fm_uc_incr                        true
% 2.65/0.98  --sat_out_model                         small
% 2.65/0.98  --sat_out_clauses                       false
% 2.65/0.98  
% 2.65/0.98  ------ QBF Options
% 2.65/0.98  
% 2.65/0.98  --qbf_mode                              false
% 2.65/0.98  --qbf_elim_univ                         false
% 2.65/0.98  --qbf_dom_inst                          none
% 2.65/0.98  --qbf_dom_pre_inst                      false
% 2.65/0.98  --qbf_sk_in                             false
% 2.65/0.98  --qbf_pred_elim                         true
% 2.65/0.98  --qbf_split                             512
% 2.65/0.98  
% 2.65/0.98  ------ BMC1 Options
% 2.65/0.98  
% 2.65/0.98  --bmc1_incremental                      false
% 2.65/0.98  --bmc1_axioms                           reachable_all
% 2.65/0.98  --bmc1_min_bound                        0
% 2.65/0.98  --bmc1_max_bound                        -1
% 2.65/0.98  --bmc1_max_bound_default                -1
% 2.65/0.98  --bmc1_symbol_reachability              true
% 2.65/0.98  --bmc1_property_lemmas                  false
% 2.65/0.98  --bmc1_k_induction                      false
% 2.65/0.98  --bmc1_non_equiv_states                 false
% 2.65/0.98  --bmc1_deadlock                         false
% 2.65/0.98  --bmc1_ucm                              false
% 2.65/0.98  --bmc1_add_unsat_core                   none
% 2.65/0.98  --bmc1_unsat_core_children              false
% 2.65/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.65/0.98  --bmc1_out_stat                         full
% 2.65/0.98  --bmc1_ground_init                      false
% 2.65/0.98  --bmc1_pre_inst_next_state              false
% 2.65/0.98  --bmc1_pre_inst_state                   false
% 2.65/0.98  --bmc1_pre_inst_reach_state             false
% 2.65/0.98  --bmc1_out_unsat_core                   false
% 2.65/0.98  --bmc1_aig_witness_out                  false
% 2.65/0.98  --bmc1_verbose                          false
% 2.65/0.98  --bmc1_dump_clauses_tptp                false
% 2.65/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.65/0.98  --bmc1_dump_file                        -
% 2.65/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.65/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.65/0.98  --bmc1_ucm_extend_mode                  1
% 2.65/0.98  --bmc1_ucm_init_mode                    2
% 2.65/0.98  --bmc1_ucm_cone_mode                    none
% 2.65/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.65/0.98  --bmc1_ucm_relax_model                  4
% 2.65/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.65/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.65/0.98  --bmc1_ucm_layered_model                none
% 2.65/0.98  --bmc1_ucm_max_lemma_size               10
% 2.65/0.98  
% 2.65/0.98  ------ AIG Options
% 2.65/0.98  
% 2.65/0.98  --aig_mode                              false
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation Options
% 2.65/0.98  
% 2.65/0.98  --instantiation_flag                    true
% 2.65/0.98  --inst_sos_flag                         false
% 2.65/0.98  --inst_sos_phase                        true
% 2.65/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.65/0.98  --inst_lit_sel_side                     none
% 2.65/0.98  --inst_solver_per_active                1400
% 2.65/0.98  --inst_solver_calls_frac                1.
% 2.65/0.98  --inst_passive_queue_type               priority_queues
% 2.65/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.65/0.98  --inst_passive_queues_freq              [25;2]
% 2.65/0.98  --inst_dismatching                      true
% 2.65/0.98  --inst_eager_unprocessed_to_passive     true
% 2.65/0.98  --inst_prop_sim_given                   true
% 2.65/0.98  --inst_prop_sim_new                     false
% 2.65/0.98  --inst_subs_new                         false
% 2.65/0.98  --inst_eq_res_simp                      false
% 2.65/0.98  --inst_subs_given                       false
% 2.65/0.98  --inst_orphan_elimination               true
% 2.65/0.98  --inst_learning_loop_flag               true
% 2.65/0.98  --inst_learning_start                   3000
% 2.65/0.98  --inst_learning_factor                  2
% 2.65/0.98  --inst_start_prop_sim_after_learn       3
% 2.65/0.98  --inst_sel_renew                        solver
% 2.65/0.98  --inst_lit_activity_flag                true
% 2.65/0.98  --inst_restr_to_given                   false
% 2.65/0.98  --inst_activity_threshold               500
% 2.65/0.98  --inst_out_proof                        true
% 2.65/0.98  
% 2.65/0.98  ------ Resolution Options
% 2.65/0.98  
% 2.65/0.98  --resolution_flag                       false
% 2.65/0.98  --res_lit_sel                           adaptive
% 2.65/0.98  --res_lit_sel_side                      none
% 2.65/0.98  --res_ordering                          kbo
% 2.65/0.98  --res_to_prop_solver                    active
% 2.65/0.98  --res_prop_simpl_new                    false
% 2.65/0.98  --res_prop_simpl_given                  true
% 2.65/0.98  --res_passive_queue_type                priority_queues
% 2.65/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.65/0.98  --res_passive_queues_freq               [15;5]
% 2.65/0.98  --res_forward_subs                      full
% 2.65/0.98  --res_backward_subs                     full
% 2.65/0.98  --res_forward_subs_resolution           true
% 2.65/0.98  --res_backward_subs_resolution          true
% 2.65/0.98  --res_orphan_elimination                true
% 2.65/0.98  --res_time_limit                        2.
% 2.65/0.98  --res_out_proof                         true
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Options
% 2.65/0.98  
% 2.65/0.98  --superposition_flag                    true
% 2.65/0.98  --sup_passive_queue_type                priority_queues
% 2.65/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.65/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.65/0.98  --demod_completeness_check              fast
% 2.65/0.98  --demod_use_ground                      true
% 2.65/0.98  --sup_to_prop_solver                    passive
% 2.65/0.98  --sup_prop_simpl_new                    true
% 2.65/0.98  --sup_prop_simpl_given                  true
% 2.65/0.98  --sup_fun_splitting                     false
% 2.65/0.98  --sup_smt_interval                      50000
% 2.65/0.98  
% 2.65/0.98  ------ Superposition Simplification Setup
% 2.65/0.98  
% 2.65/0.98  --sup_indices_passive                   []
% 2.65/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.65/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.65/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_full_bw                           [BwDemod]
% 2.65/0.98  --sup_immed_triv                        [TrivRules]
% 2.65/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.65/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_immed_bw_main                     []
% 2.65/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.65/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.65/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.65/0.98  
% 2.65/0.98  ------ Combination Options
% 2.65/0.98  
% 2.65/0.98  --comb_res_mult                         3
% 2.65/0.98  --comb_sup_mult                         2
% 2.65/0.98  --comb_inst_mult                        10
% 2.65/0.98  
% 2.65/0.98  ------ Debug Options
% 2.65/0.98  
% 2.65/0.98  --dbg_backtrace                         false
% 2.65/0.98  --dbg_dump_prop_clauses                 false
% 2.65/0.98  --dbg_dump_prop_clauses_file            -
% 2.65/0.98  --dbg_out_stat                          false
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  ------ Proving...
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  % SZS status Theorem for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98   Resolution empty clause
% 2.65/0.98  
% 2.65/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  fof(f15,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f32,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(ennf_transformation,[],[f15])).
% 2.65/0.98  
% 2.65/0.98  fof(f33,plain,(
% 2.65/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(flattening,[],[f32])).
% 2.65/0.98  
% 2.65/0.98  fof(f44,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(nnf_transformation,[],[f33])).
% 2.65/0.98  
% 2.65/0.98  fof(f67,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f44])).
% 2.65/0.98  
% 2.65/0.98  fof(f17,conjecture,(
% 2.65/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f18,negated_conjecture,(
% 2.65/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.65/0.98    inference(negated_conjecture,[],[f17])).
% 2.65/0.98  
% 2.65/0.98  fof(f36,plain,(
% 2.65/0.98    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.65/0.98    inference(ennf_transformation,[],[f18])).
% 2.65/0.98  
% 2.65/0.98  fof(f37,plain,(
% 2.65/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.65/0.98    inference(flattening,[],[f36])).
% 2.65/0.98  
% 2.65/0.98  fof(f45,plain,(
% 2.65/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 2.65/0.98    introduced(choice_axiom,[])).
% 2.65/0.98  
% 2.65/0.98  fof(f46,plain,(
% 2.65/0.98    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 2.65/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f37,f45])).
% 2.65/0.98  
% 2.65/0.98  fof(f77,plain,(
% 2.65/0.98    v1_funct_2(sK4,sK2,sK3)),
% 2.65/0.98    inference(cnf_transformation,[],[f46])).
% 2.65/0.98  
% 2.65/0.98  fof(f78,plain,(
% 2.65/0.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 2.65/0.98    inference(cnf_transformation,[],[f46])).
% 2.65/0.98  
% 2.65/0.98  fof(f11,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f27,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(ennf_transformation,[],[f11])).
% 2.65/0.98  
% 2.65/0.98  fof(f62,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f27])).
% 2.65/0.98  
% 2.65/0.98  fof(f12,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f28,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(ennf_transformation,[],[f12])).
% 2.65/0.98  
% 2.65/0.98  fof(f63,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f28])).
% 2.65/0.98  
% 2.65/0.98  fof(f80,plain,(
% 2.65/0.98    k2_relset_1(sK2,sK3,sK4) = sK3),
% 2.65/0.98    inference(cnf_transformation,[],[f46])).
% 2.65/0.98  
% 2.65/0.98  fof(f7,axiom,(
% 2.65/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f22,plain,(
% 2.65/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/0.98    inference(ennf_transformation,[],[f7])).
% 2.65/0.98  
% 2.65/0.98  fof(f23,plain,(
% 2.65/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/0.98    inference(flattening,[],[f22])).
% 2.65/0.98  
% 2.65/0.98  fof(f57,plain,(
% 2.65/0.98    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f23])).
% 2.65/0.98  
% 2.65/0.98  fof(f79,plain,(
% 2.65/0.98    v2_funct_1(sK4)),
% 2.65/0.98    inference(cnf_transformation,[],[f46])).
% 2.65/0.98  
% 2.65/0.98  fof(f76,plain,(
% 2.65/0.98    v1_funct_1(sK4)),
% 2.65/0.98    inference(cnf_transformation,[],[f46])).
% 2.65/0.98  
% 2.65/0.98  fof(f8,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f24,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(ennf_transformation,[],[f8])).
% 2.65/0.98  
% 2.65/0.98  fof(f59,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f24])).
% 2.65/0.98  
% 2.65/0.98  fof(f16,axiom,(
% 2.65/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f34,plain,(
% 2.65/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/0.98    inference(ennf_transformation,[],[f16])).
% 2.65/0.98  
% 2.65/0.98  fof(f35,plain,(
% 2.65/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/0.98    inference(flattening,[],[f34])).
% 2.65/0.98  
% 2.65/0.98  fof(f75,plain,(
% 2.65/0.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f35])).
% 2.65/0.98  
% 2.65/0.98  fof(f58,plain,(
% 2.65/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f23])).
% 2.65/0.98  
% 2.65/0.98  fof(f6,axiom,(
% 2.65/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f20,plain,(
% 2.65/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.65/0.98    inference(ennf_transformation,[],[f6])).
% 2.65/0.98  
% 2.65/0.98  fof(f21,plain,(
% 2.65/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.65/0.98    inference(flattening,[],[f20])).
% 2.65/0.98  
% 2.65/0.98  fof(f56,plain,(
% 2.65/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f21])).
% 2.65/0.98  
% 2.65/0.98  fof(f55,plain,(
% 2.65/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f21])).
% 2.65/0.98  
% 2.65/0.98  fof(f74,plain,(
% 2.65/0.98    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f35])).
% 2.65/0.98  
% 2.65/0.98  fof(f81,plain,(
% 2.65/0.98    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 2.65/0.98    inference(cnf_transformation,[],[f46])).
% 2.65/0.98  
% 2.65/0.98  fof(f4,axiom,(
% 2.65/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f40,plain,(
% 2.65/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.65/0.98    inference(nnf_transformation,[],[f4])).
% 2.65/0.98  
% 2.65/0.98  fof(f41,plain,(
% 2.65/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 2.65/0.98    inference(flattening,[],[f40])).
% 2.65/0.98  
% 2.65/0.98  fof(f51,plain,(
% 2.65/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 2.65/0.98    inference(cnf_transformation,[],[f41])).
% 2.65/0.98  
% 2.65/0.98  fof(f83,plain,(
% 2.65/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 2.65/0.98    inference(equality_resolution,[],[f51])).
% 2.65/0.98  
% 2.65/0.98  fof(f70,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f44])).
% 2.65/0.98  
% 2.65/0.98  fof(f87,plain,(
% 2.65/0.98    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.65/0.98    inference(equality_resolution,[],[f70])).
% 2.65/0.98  
% 2.65/0.98  fof(f14,axiom,(
% 2.65/0.98    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f31,plain,(
% 2.65/0.98    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.65/0.98    inference(ennf_transformation,[],[f14])).
% 2.65/0.98  
% 2.65/0.98  fof(f66,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.65/0.98    inference(cnf_transformation,[],[f31])).
% 2.65/0.98  
% 2.65/0.98  fof(f13,axiom,(
% 2.65/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f29,plain,(
% 2.65/0.98    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(ennf_transformation,[],[f13])).
% 2.65/0.98  
% 2.65/0.98  fof(f30,plain,(
% 2.65/0.98    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.65/0.98    inference(flattening,[],[f29])).
% 2.65/0.98  
% 2.65/0.98  fof(f65,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f30])).
% 2.65/0.98  
% 2.65/0.98  fof(f68,plain,(
% 2.65/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.65/0.98    inference(cnf_transformation,[],[f44])).
% 2.65/0.98  
% 2.65/0.98  fof(f88,plain,(
% 2.65/0.98    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.65/0.98    inference(equality_resolution,[],[f68])).
% 2.65/0.98  
% 2.65/0.98  fof(f1,axiom,(
% 2.65/0.98    v1_xboole_0(k1_xboole_0)),
% 2.65/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.65/0.98  
% 2.65/0.98  fof(f47,plain,(
% 2.65/0.98    v1_xboole_0(k1_xboole_0)),
% 2.65/0.98    inference(cnf_transformation,[],[f1])).
% 2.65/0.98  
% 2.65/0.98  cnf(c_25,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.65/0.98      | k1_xboole_0 = X2 ),
% 2.65/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_33,negated_conjecture,
% 2.65/0.98      ( v1_funct_2(sK4,sK2,sK3) ),
% 2.65/0.98      inference(cnf_transformation,[],[f77]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1271,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | k1_relset_1(X1,X2,X0) = X1
% 2.65/0.98      | sK2 != X1
% 2.65/0.98      | sK3 != X2
% 2.65/0.98      | sK4 != X0
% 2.65/0.98      | k1_xboole_0 = X2 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1272,plain,
% 2.65/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.65/0.98      | k1_relset_1(sK2,sK3,sK4) = sK2
% 2.65/0.98      | k1_xboole_0 = sK3 ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_1271]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_32,negated_conjecture,
% 2.65/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 2.65/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1274,plain,
% 2.65/0.98      ( k1_relset_1(sK2,sK3,sK4) = sK2 | k1_xboole_0 = sK3 ),
% 2.65/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1272,c_32]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2016,plain,
% 2.65/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_15,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2019,plain,
% 2.65/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.65/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4691,plain,
% 2.65/0.98      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_2016,c_2019]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4967,plain,
% 2.65/0.98      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_1274,c_4691]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_16,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2018,plain,
% 2.65/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.65/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3619,plain,
% 2.65/0.98      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_2016,c_2018]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_30,negated_conjecture,
% 2.65/0.98      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 2.65/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3631,plain,
% 2.65/0.98      ( k2_relat_1(sK4) = sK3 ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_3619,c_30]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_11,plain,
% 2.65/0.98      ( ~ v2_funct_1(X0)
% 2.65/0.98      | ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f57]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_31,negated_conjecture,
% 2.65/0.98      ( v2_funct_1(sK4) ),
% 2.65/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_360,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.65/0.98      | sK4 != X0 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_31]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_361,plain,
% 2.65/0.98      ( ~ v1_relat_1(sK4)
% 2.65/0.98      | ~ v1_funct_1(sK4)
% 2.65/0.98      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_360]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_34,negated_conjecture,
% 2.65/0.98      ( v1_funct_1(sK4) ),
% 2.65/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_363,plain,
% 2.65/0.98      ( ~ v1_relat_1(sK4) | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.65/0.98      inference(global_propositional_subsumption,[status(thm)],[c_361,c_34]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2014,plain,
% 2.65/0.98      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 2.65/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_363]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_12,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2318,plain,
% 2.65/0.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 2.65/0.98      | v1_relat_1(sK4) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2336,plain,
% 2.65/0.98      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_2014,c_34,c_32,c_361,c_2318]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3649,plain,
% 2.65/0.98      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_3631,c_2336]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_26,plain,
% 2.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.65/0.98      | ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2017,plain,
% 2.65/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.65/0.98      | v1_relat_1(X0) != iProver_top
% 2.65/0.98      | v1_funct_1(X0) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3914,plain,
% 2.65/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k2_relat_1(k2_funct_1(sK4))))) = iProver_top
% 2.65/0.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_3649,c_2017]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_10,plain,
% 2.65/0.98      ( ~ v2_funct_1(X0)
% 2.65/0.98      | ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_374,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.65/0.98      | sK4 != X0 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_31]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_375,plain,
% 2.65/0.98      ( ~ v1_relat_1(sK4)
% 2.65/0.98      | ~ v1_funct_1(sK4)
% 2.65/0.98      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_374]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_377,plain,
% 2.65/0.98      ( ~ v1_relat_1(sK4) | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.65/0.98      inference(global_propositional_subsumption,[status(thm)],[c_375,c_34]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2013,plain,
% 2.65/0.98      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 2.65/0.98      | v1_relat_1(sK4) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2332,plain,
% 2.65/0.98      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_2013,c_34,c_32,c_375,c_2318]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3915,plain,
% 2.65/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 2.65/0.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_3914,c_2332]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_35,plain,
% 2.65/0.98      ( v1_funct_1(sK4) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_37,plain,
% 2.65/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2319,plain,
% 2.65/0.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 2.65/0.98      | v1_relat_1(sK4) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2318]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_8,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 2.65/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2387,plain,
% 2.65/0.98      ( ~ v1_relat_1(sK4) | v1_funct_1(k2_funct_1(sK4)) | ~ v1_funct_1(sK4) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2388,plain,
% 2.65/0.98      ( v1_relat_1(sK4) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 2.65/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2387]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_9,plain,
% 2.65/0.98      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2386,plain,
% 2.65/0.98      ( v1_relat_1(k2_funct_1(sK4)) | ~ v1_relat_1(sK4) | ~ v1_funct_1(sK4) ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2390,plain,
% 2.65/0.98      ( v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 2.65/0.98      | v1_relat_1(sK4) != iProver_top
% 2.65/0.98      | v1_funct_1(sK4) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2386]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4309,plain,
% 2.65/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_3915,c_35,c_37,c_2319,c_2388,c_2390]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5110,plain,
% 2.65/0.98      ( sK3 = k1_xboole_0
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_4967,c_4309]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_27,plain,
% 2.65/0.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 2.65/0.98      | ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_29,negated_conjecture,
% 2.65/0.98      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 2.65/0.98      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.65/0.98      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 2.65/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1388,plain,
% 2.65/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.65/0.98      | ~ v1_relat_1(X0)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.65/0.98      | k1_relat_1(X0) != sK3
% 2.65/0.98      | k2_relat_1(X0) != sK2
% 2.65/0.98      | k2_funct_1(sK4) != X0 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_27,c_29]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1389,plain,
% 2.65/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.65/0.98      | ~ v1_relat_1(k2_funct_1(sK4))
% 2.65/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.65/0.98      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.65/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_1388]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1401,plain,
% 2.65/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.65/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.65/0.98      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.65/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 2.65/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1389,c_12]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2001,plain,
% 2.65/0.98      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.65/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1401]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1406,plain,
% 2.65/0.98      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.65/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1401]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2401,plain,
% 2.65/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.65/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.65/0.98      | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_2001,c_35,c_37,c_1406,c_2319,c_2388]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2402,plain,
% 2.65/0.98      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 2.65/0.98      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.65/0.98      inference(renaming,[status(thm)],[c_2401]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2405,plain,
% 2.65/0.98      ( k1_relat_1(sK4) != sK2
% 2.65/0.98      | k2_relat_1(sK4) != sK3
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.65/0.98      inference(light_normalisation,[status(thm)],[c_2402,c_2332,c_2336]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3648,plain,
% 2.65/0.98      ( k1_relat_1(sK4) != sK2
% 2.65/0.98      | sK3 != sK3
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_3631,c_2405]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_3652,plain,
% 2.65/0.98      ( k1_relat_1(sK4) != sK2
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.65/0.98      inference(equality_resolution_simp,[status(thm)],[c_3648]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5111,plain,
% 2.65/0.98      ( sK3 = k1_xboole_0
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.65/0.98      inference(superposition,[status(thm)],[c_4967,c_3652]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5121,plain,
% 2.65/0.98      ( sK3 = k1_xboole_0 ),
% 2.65/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_5110,c_5111]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5161,plain,
% 2.65/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK4)))) = iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_5121,c_4309]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_4,plain,
% 2.65/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5246,plain,
% 2.65/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_5161,c_4]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_22,plain,
% 2.65/0.98      ( v1_funct_2(X0,k1_xboole_0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.65/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1357,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.65/0.98      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.65/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.65/0.98      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 2.65/0.98      | k2_funct_1(sK4) != X0
% 2.65/0.98      | sK2 != X1
% 2.65/0.98      | sK3 != k1_xboole_0 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1358,plain,
% 2.65/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.65/0.98      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.65/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.65/0.98      | k1_relset_1(k1_xboole_0,sK2,k2_funct_1(sK4)) != k1_xboole_0
% 2.65/0.98      | sK3 != k1_xboole_0 ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_1357]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_19,plain,
% 2.65/0.98      ( v1_partfun1(X0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_xboole_0(X1) ),
% 2.65/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_17,plain,
% 2.65/0.98      ( v1_funct_2(X0,X1,X2)
% 2.65/0.98      | ~ v1_partfun1(X0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_1(X0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_334,plain,
% 2.65/0.98      ( v1_funct_2(X0,X1,X2)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v1_xboole_0(X1) ),
% 2.65/0.98      inference(resolution,[status(thm)],[c_19,c_17]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_338,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | v1_funct_2(X0,X1,X2)
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v1_xboole_0(X1) ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_334,c_19,c_17]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_339,plain,
% 2.65/0.98      ( v1_funct_2(X0,X1,X2)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v1_xboole_0(X1) ),
% 2.65/0.98      inference(renaming,[status(thm)],[c_338]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_24,plain,
% 2.65/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.65/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.65/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1193,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X4)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v1_xboole_0(X1)
% 2.65/0.98      | X3 != X0
% 2.65/0.98      | X4 != X2
% 2.65/0.98      | k1_relset_1(k1_xboole_0,X4,X3) = k1_xboole_0
% 2.65/0.98      | k1_xboole_0 != X1 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_339,c_24]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1194,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v1_xboole_0(k1_xboole_0)
% 2.65/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_1193]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_0,plain,
% 2.65/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 2.65/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1198,plain,
% 2.65/0.98      ( ~ v1_funct_1(X0)
% 2.65/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.65/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.65/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1194,c_0]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1199,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.65/0.98      inference(renaming,[status(thm)],[c_1198]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1365,plain,
% 2.65/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.65/0.98      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 2.65/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.65/0.98      | sK3 != k1_xboole_0 ),
% 2.65/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1358,c_1199]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2003,plain,
% 2.65/0.98      ( sK3 != k1_xboole_0
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1365]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2207,plain,
% 2.65/0.98      ( sK3 != k1_xboole_0
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_2003,c_4]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_107,plain,
% 2.65/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1242,plain,
% 2.65/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.65/0.98      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.65/0.98      | ~ v1_funct_1(X0)
% 2.65/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.65/0.98      | ~ v1_xboole_0(X1)
% 2.65/0.98      | k2_funct_1(sK4) != X0
% 2.65/0.98      | sK2 != X2
% 2.65/0.98      | sK3 != X1 ),
% 2.65/0.98      inference(resolution_lifted,[status(thm)],[c_339,c_29]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1243,plain,
% 2.65/0.98      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 2.65/0.98      | ~ v1_funct_1(k2_funct_1(sK4))
% 2.65/0.98      | ~ v1_xboole_0(sK3) ),
% 2.65/0.98      inference(unflattening,[status(thm)],[c_1242]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1244,plain,
% 2.65/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 2.65/0.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 2.65/0.98      | v1_xboole_0(sK3) != iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_1243]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_1494,plain,
% 2.65/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.65/0.98      theory(equality) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2321,plain,
% 2.65/0.98      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_1494]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2322,plain,
% 2.65/0.98      ( sK3 != X0
% 2.65/0.98      | v1_xboole_0(X0) != iProver_top
% 2.65/0.98      | v1_xboole_0(sK3) = iProver_top ),
% 2.65/0.98      inference(predicate_to_equality,[status(thm)],[c_2321]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2324,plain,
% 2.65/0.98      ( sK3 != k1_xboole_0
% 2.65/0.98      | v1_xboole_0(sK3) = iProver_top
% 2.65/0.98      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.65/0.98      inference(instantiation,[status(thm)],[c_2322]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_2797,plain,
% 2.65/0.98      ( sK3 != k1_xboole_0
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 2.65/0.98      inference(global_propositional_subsumption,
% 2.65/0.98                [status(thm)],
% 2.65/0.98                [c_2207,c_35,c_37,c_107,c_1244,c_2319,c_2324,c_2388]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5168,plain,
% 2.65/0.98      ( k1_xboole_0 != k1_xboole_0
% 2.65/0.98      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_5121,c_2797]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5228,plain,
% 2.65/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 2.65/0.98      inference(equality_resolution_simp,[status(thm)],[c_5168]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5230,plain,
% 2.65/0.98      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 2.65/0.98      inference(demodulation,[status(thm)],[c_5228,c_4]) ).
% 2.65/0.98  
% 2.65/0.98  cnf(c_5248,plain,
% 2.65/0.98      ( $false ),
% 2.65/0.98      inference(backward_subsumption_resolution,[status(thm)],[c_5246,c_5230]) ).
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.65/0.98  
% 2.65/0.98  ------                               Statistics
% 2.65/0.98  
% 2.65/0.98  ------ General
% 2.65/0.98  
% 2.65/0.98  abstr_ref_over_cycles:                  0
% 2.65/0.98  abstr_ref_under_cycles:                 0
% 2.65/0.98  gc_basic_clause_elim:                   0
% 2.65/0.98  forced_gc_time:                         0
% 2.65/0.98  parsing_time:                           0.009
% 2.65/0.98  unif_index_cands_time:                  0.
% 2.65/0.98  unif_index_add_time:                    0.
% 2.65/0.98  orderings_time:                         0.
% 2.65/0.98  out_proof_time:                         0.008
% 2.65/0.98  total_time:                             0.152
% 2.65/0.98  num_of_symbols:                         51
% 2.65/0.98  num_of_terms:                           3865
% 2.65/0.98  
% 2.65/0.98  ------ Preprocessing
% 2.65/0.98  
% 2.65/0.98  num_of_splits:                          0
% 2.65/0.98  num_of_split_atoms:                     0
% 2.65/0.98  num_of_reused_defs:                     0
% 2.65/0.98  num_eq_ax_congr_red:                    6
% 2.65/0.98  num_of_sem_filtered_clauses:            1
% 2.65/0.98  num_of_subtypes:                        0
% 2.65/0.98  monotx_restored_types:                  0
% 2.65/0.98  sat_num_of_epr_types:                   0
% 2.65/0.98  sat_num_of_non_cyclic_types:            0
% 2.65/0.98  sat_guarded_non_collapsed_types:        0
% 2.65/0.98  num_pure_diseq_elim:                    0
% 2.65/0.98  simp_replaced_by:                       0
% 2.65/0.98  res_preprocessed:                       130
% 2.65/0.98  prep_upred:                             0
% 2.65/0.98  prep_unflattend:                        87
% 2.65/0.98  smt_new_axioms:                         0
% 2.65/0.98  pred_elim_cands:                        7
% 2.65/0.98  pred_elim:                              3
% 2.65/0.98  pred_elim_cl:                           -2
% 2.65/0.98  pred_elim_cycles:                       5
% 2.65/0.98  merged_defs:                            0
% 2.65/0.98  merged_defs_ncl:                        0
% 2.65/0.98  bin_hyper_res:                          0
% 2.65/0.98  prep_cycles:                            3
% 2.65/0.98  pred_elim_time:                         0.021
% 2.65/0.98  splitting_time:                         0.
% 2.65/0.98  sem_filter_time:                        0.
% 2.65/0.98  monotx_time:                            0.
% 2.65/0.98  subtype_inf_time:                       0.
% 2.65/0.98  
% 2.65/0.98  ------ Problem properties
% 2.65/0.98  
% 2.65/0.98  clauses:                                35
% 2.65/0.98  conjectures:                            3
% 2.65/0.98  epr:                                    4
% 2.65/0.98  horn:                                   28
% 2.65/0.98  ground:                                 16
% 2.65/0.98  unary:                                  9
% 2.65/0.98  binary:                                 6
% 2.65/0.98  lits:                                   96
% 2.65/0.98  lits_eq:                                38
% 2.65/0.98  fd_pure:                                0
% 2.65/0.98  fd_pseudo:                              0
% 2.65/0.98  fd_cond:                                3
% 2.65/0.98  fd_pseudo_cond:                         1
% 2.65/0.98  ac_symbols:                             0
% 2.65/0.98  
% 2.65/0.98  ------ Propositional Solver
% 2.65/0.98  
% 2.65/0.98  prop_solver_calls:                      23
% 2.65/0.98  prop_fast_solver_calls:                 1069
% 2.65/0.98  smt_solver_calls:                       0
% 2.65/0.98  smt_fast_solver_calls:                  0
% 2.65/0.98  prop_num_of_clauses:                    1620
% 2.65/0.98  prop_preprocess_simplified:             5628
% 2.65/0.98  prop_fo_subsumed:                       23
% 2.65/0.98  prop_solver_time:                       0.
% 2.65/0.98  smt_solver_time:                        0.
% 2.65/0.98  smt_fast_solver_time:                   0.
% 2.65/0.98  prop_fast_solver_time:                  0.
% 2.65/0.98  prop_unsat_core_time:                   0.
% 2.65/0.98  
% 2.65/0.98  ------ QBF
% 2.65/0.98  
% 2.65/0.98  qbf_q_res:                              0
% 2.65/0.98  qbf_num_tautologies:                    0
% 2.65/0.98  qbf_prep_cycles:                        0
% 2.65/0.98  
% 2.65/0.98  ------ BMC1
% 2.65/0.98  
% 2.65/0.98  bmc1_current_bound:                     -1
% 2.65/0.98  bmc1_last_solved_bound:                 -1
% 2.65/0.98  bmc1_unsat_core_size:                   -1
% 2.65/0.98  bmc1_unsat_core_parents_size:           -1
% 2.65/0.98  bmc1_merge_next_fun:                    0
% 2.65/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.65/0.98  
% 2.65/0.98  ------ Instantiation
% 2.65/0.98  
% 2.65/0.98  inst_num_of_clauses:                    547
% 2.65/0.98  inst_num_in_passive:                    166
% 2.65/0.98  inst_num_in_active:                     263
% 2.65/0.98  inst_num_in_unprocessed:                118
% 2.65/0.98  inst_num_of_loops:                      280
% 2.65/0.98  inst_num_of_learning_restarts:          0
% 2.65/0.98  inst_num_moves_active_passive:          15
% 2.65/0.98  inst_lit_activity:                      0
% 2.65/0.98  inst_lit_activity_moves:                0
% 2.65/0.98  inst_num_tautologies:                   0
% 2.65/0.98  inst_num_prop_implied:                  0
% 2.65/0.98  inst_num_existing_simplified:           0
% 2.65/0.98  inst_num_eq_res_simplified:             0
% 2.65/0.98  inst_num_child_elim:                    0
% 2.65/0.98  inst_num_of_dismatching_blockings:      116
% 2.65/0.98  inst_num_of_non_proper_insts:           437
% 2.65/0.98  inst_num_of_duplicates:                 0
% 2.65/0.98  inst_inst_num_from_inst_to_res:         0
% 2.65/0.98  inst_dismatching_checking_time:         0.
% 2.65/0.98  
% 2.65/0.98  ------ Resolution
% 2.65/0.98  
% 2.65/0.98  res_num_of_clauses:                     0
% 2.65/0.98  res_num_in_passive:                     0
% 2.65/0.98  res_num_in_active:                      0
% 2.65/0.98  res_num_of_loops:                       133
% 2.65/0.98  res_forward_subset_subsumed:            16
% 2.65/0.98  res_backward_subset_subsumed:           2
% 2.65/0.98  res_forward_subsumed:                   3
% 2.65/0.98  res_backward_subsumed:                  0
% 2.65/0.98  res_forward_subsumption_resolution:     3
% 2.65/0.98  res_backward_subsumption_resolution:    0
% 2.65/0.98  res_clause_to_clause_subsumption:       125
% 2.65/0.98  res_orphan_elimination:                 0
% 2.65/0.98  res_tautology_del:                      45
% 2.65/0.98  res_num_eq_res_simplified:              0
% 2.65/0.98  res_num_sel_changes:                    0
% 2.65/0.98  res_moves_from_active_to_pass:          0
% 2.65/0.98  
% 2.65/0.98  ------ Superposition
% 2.65/0.98  
% 2.65/0.98  sup_time_total:                         0.
% 2.65/0.98  sup_time_generating:                    0.
% 2.65/0.98  sup_time_sim_full:                      0.
% 2.65/0.98  sup_time_sim_immed:                     0.
% 2.65/0.98  
% 2.65/0.98  sup_num_of_clauses:                     45
% 2.65/0.98  sup_num_in_active:                      24
% 2.65/0.98  sup_num_in_passive:                     21
% 2.65/0.98  sup_num_of_loops:                       54
% 2.65/0.98  sup_fw_superposition:                   34
% 2.65/0.98  sup_bw_superposition:                   20
% 2.65/0.98  sup_immediate_simplified:               15
% 2.65/0.98  sup_given_eliminated:                   1
% 2.65/0.98  comparisons_done:                       0
% 2.65/0.98  comparisons_avoided:                    7
% 2.65/0.98  
% 2.65/0.98  ------ Simplifications
% 2.65/0.98  
% 2.65/0.98  
% 2.65/0.98  sim_fw_subset_subsumed:                 11
% 2.65/0.98  sim_bw_subset_subsumed:                 2
% 2.65/0.98  sim_fw_subsumed:                        1
% 2.65/0.98  sim_bw_subsumed:                        4
% 2.65/0.98  sim_fw_subsumption_res:                 3
% 2.65/0.98  sim_bw_subsumption_res:                 1
% 2.65/0.98  sim_tautology_del:                      1
% 2.65/0.98  sim_eq_tautology_del:                   3
% 2.65/0.98  sim_eq_res_simp:                        3
% 2.65/0.98  sim_fw_demodulated:                     15
% 2.65/0.98  sim_bw_demodulated:                     29
% 2.65/0.98  sim_light_normalised:                   10
% 2.65/0.98  sim_joinable_taut:                      0
% 2.65/0.98  sim_joinable_simp:                      0
% 2.65/0.98  sim_ac_normalised:                      0
% 2.65/0.98  sim_smt_subsumption:                    0
% 2.65/0.98  
%------------------------------------------------------------------------------
