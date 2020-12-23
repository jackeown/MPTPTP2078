%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:51 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  206 (4860 expanded)
%              Number of clauses        :  129 (1719 expanded)
%              Number of leaves         :   20 ( 915 expanded)
%              Depth                    :   27
%              Number of atoms          :  624 (24609 expanded)
%              Number of equality atoms :  302 (5485 expanded)
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

fof(f41,plain,(
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
    inference(flattening,[],[f41])).

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
    inference(nnf_transformation,[],[f42])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
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
    inference(flattening,[],[f45])).

fof(f52,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
        | ~ v1_funct_1(k2_funct_1(sK3)) )
      & k2_relset_1(sK1,sK2,sK3) = sK2
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
      & v1_funct_2(sK3,sK1,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f52])).

fof(f88,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f89,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f36])).

fof(f71,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f90,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f44,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f43])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f91,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f53])).

fof(f70,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f85,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f97,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f93,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f10,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f98,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f78])).

fof(f19,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_1(X2)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f24,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_1(X2)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(pure_predicate_removal,[],[f23])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_1(X2)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_1(sK0(X0,X1))
        & v1_relat_1(sK0(X0,X1))
        & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_funct_1(sK0(X0,X1))
      & v1_relat_1(sK0(X0,X1))
      & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f50])).

fof(f82,plain,(
    ! [X0,X1] : v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f83,plain,(
    ! [X0,X1] : v1_funct_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_funct_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_funct_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_594,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X1
    | sK2 != X2
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_37])).

cnf(c_595,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_594])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_597,plain,
    ( k1_relset_1(sK1,sK2,sK3) = sK1
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_595,c_36])).

cnf(c_1255,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1261,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3247,plain,
    ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1255,c_1261])).

cnf(c_3447,plain,
    ( k1_relat_1(sK3) = sK1
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_597,c_3247])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1269,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4162,plain,
    ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_1269])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1268,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4178,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4162,c_1268])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_35,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_382,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_35])).

cnf(c_383,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_382])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_385,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_383,c_38])).

cnf(c_1252,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_385])).

cnf(c_4186,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_4178,c_1252])).

cnf(c_30,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1256,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4438,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4186,c_1256])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1260,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2530,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1255,c_1260])).

cnf(c_34,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_2542,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_2530,c_34])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_368,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_35])).

cnf(c_369,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_368])).

cnf(c_371,plain,
    ( ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_369,c_38])).

cnf(c_1253,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_371])).

cnf(c_2566,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2
    | v1_relat_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2542,c_1253])).

cnf(c_4184,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(superposition,[status(thm)],[c_4178,c_2566])).

cnf(c_4439,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4438,c_4184])).

cnf(c_39,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1558,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1559,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1558])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1566,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1567,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1566])).

cnf(c_5093,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4439,c_39,c_1559,c_1567,c_4178])).

cnf(c_5098,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_5093])).

cnf(c_31,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_33,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_605,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK3) != X0
    | k2_relat_1(X0) != sK1
    | k1_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_33])).

cnf(c_606,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3))
    | k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_1242,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_4433,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | sK2 != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4184,c_1242])).

cnf(c_4893,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4433])).

cnf(c_607,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | k1_relat_1(k2_funct_1(sK3)) != sK2
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_4895,plain,
    ( k2_relat_1(k2_funct_1(sK3)) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4893,c_39,c_607,c_1559,c_1567,c_2566,c_4178])).

cnf(c_4899,plain,
    ( k1_relat_1(sK3) != sK1
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4895,c_4186])).

cnf(c_4903,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3447,c_4899])).

cnf(c_5133,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5098,c_4903])).

cnf(c_5136,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5133,c_5093])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k2_relat_1(X2) != k1_xboole_0
    | k1_relat_1(X2) != X1
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_31])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_457])).

cnf(c_1249,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = k1_relat_1(X0)
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_458])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1442,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | k1_xboole_0 = X0
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1249,c_2])).

cnf(c_4788,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2542,c_1442])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_699,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1780,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK2)
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_699])).

cnf(c_1782,plain,
    ( v1_xboole_0(sK2)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1780])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1875,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(sK3)
    | sK3 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1877,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1875])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1262,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2943,plain,
    ( v1_xboole_0(sK2) != iProver_top
    | v1_xboole_0(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1255,c_1262])).

cnf(c_2979,plain,
    ( ~ v1_xboole_0(sK2)
    | v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2943])).

cnf(c_4889,plain,
    ( sK3 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4788,c_0,c_1782,c_1877,c_2979])).

cnf(c_4890,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4889])).

cnf(c_5139,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5133,c_4890])).

cnf(c_5224,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_5139])).

cnf(c_5278,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5136,c_5224])).

cnf(c_11,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_5280,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5278,c_11])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_5281,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5280,c_3])).

cnf(c_23,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_522,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK3) != X0
    | sK1 != X1
    | sK2 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_33])).

cnf(c_523,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_522])).

cnf(c_1246,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_1465,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | sK2 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1246,c_3])).

cnf(c_5150,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5133,c_1465])).

cnf(c_5187,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5150])).

cnf(c_5192,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5187,c_3])).

cnf(c_5234,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5224,c_5192])).

cnf(c_5283,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0
    | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5281,c_5234])).

cnf(c_28,plain,
    ( v1_relat_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_54,plain,
    ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_27,plain,
    ( v1_funct_1(sK0(X0,X1)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_57,plain,
    ( v1_funct_1(sK0(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_97,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_99,plain,
    ( v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_97])).

cnf(c_107,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_109,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_107])).

cnf(c_1575,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1575])).

cnf(c_1578,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1576])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1660,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1663,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1660])).

cnf(c_1665,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1663])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_funct_1(X1)
    | v1_funct_1(X0)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1631,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0(X1,X2)))
    | v1_funct_1(X0)
    | ~ v1_funct_1(sK0(X1,X2))
    | ~ v1_relat_1(sK0(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2077,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0,X1)))
    | ~ v1_funct_1(sK0(X0,X1))
    | v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(sK0(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1631])).

cnf(c_2079,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0,X1))) != iProver_top
    | v1_funct_1(sK0(X0,X1)) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top
    | v1_relat_1(sK0(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2077])).

cnf(c_2078,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2081,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2078])).

cnf(c_6849,plain,
    ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5283,c_54,c_57,c_99,c_109,c_1578,c_1665,c_2079,c_2081])).

cnf(c_3250,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1261])).

cnf(c_5548,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
    inference(superposition,[status(thm)],[c_5281,c_3250])).

cnf(c_5142,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5133,c_4184])).

cnf(c_5228,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5224,c_5142])).

cnf(c_6201,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5548,c_5228])).

cnf(c_6851,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_6849,c_6201])).

cnf(c_6852,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_6851])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.09/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/0.99  
% 3.09/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.09/0.99  
% 3.09/0.99  ------  iProver source info
% 3.09/0.99  
% 3.09/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.09/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.09/0.99  git: non_committed_changes: false
% 3.09/0.99  git: last_make_outside_of_git: false
% 3.09/0.99  
% 3.09/0.99  ------ 
% 3.09/0.99  
% 3.09/0.99  ------ Input Options
% 3.09/0.99  
% 3.09/0.99  --out_options                           all
% 3.09/0.99  --tptp_safe_out                         true
% 3.09/0.99  --problem_path                          ""
% 3.09/0.99  --include_path                          ""
% 3.09/0.99  --clausifier                            res/vclausify_rel
% 3.09/0.99  --clausifier_options                    --mode clausify
% 3.09/0.99  --stdin                                 false
% 3.09/0.99  --stats_out                             all
% 3.09/0.99  
% 3.09/0.99  ------ General Options
% 3.09/0.99  
% 3.09/0.99  --fof                                   false
% 3.09/0.99  --time_out_real                         305.
% 3.09/0.99  --time_out_virtual                      -1.
% 3.09/0.99  --symbol_type_check                     false
% 3.09/0.99  --clausify_out                          false
% 3.09/0.99  --sig_cnt_out                           false
% 3.09/0.99  --trig_cnt_out                          false
% 3.09/0.99  --trig_cnt_out_tolerance                1.
% 3.09/0.99  --trig_cnt_out_sk_spl                   false
% 3.09/0.99  --abstr_cl_out                          false
% 3.09/0.99  
% 3.09/0.99  ------ Global Options
% 3.09/0.99  
% 3.09/0.99  --schedule                              default
% 3.09/0.99  --add_important_lit                     false
% 3.09/0.99  --prop_solver_per_cl                    1000
% 3.09/0.99  --min_unsat_core                        false
% 3.09/0.99  --soft_assumptions                      false
% 3.09/0.99  --soft_lemma_size                       3
% 3.09/0.99  --prop_impl_unit_size                   0
% 3.09/0.99  --prop_impl_unit                        []
% 3.09/0.99  --share_sel_clauses                     true
% 3.09/0.99  --reset_solvers                         false
% 3.09/0.99  --bc_imp_inh                            [conj_cone]
% 3.09/0.99  --conj_cone_tolerance                   3.
% 3.09/0.99  --extra_neg_conj                        none
% 3.09/0.99  --large_theory_mode                     true
% 3.09/0.99  --prolific_symb_bound                   200
% 3.09/0.99  --lt_threshold                          2000
% 3.09/0.99  --clause_weak_htbl                      true
% 3.09/0.99  --gc_record_bc_elim                     false
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing Options
% 3.09/0.99  
% 3.09/0.99  --preprocessing_flag                    true
% 3.09/0.99  --time_out_prep_mult                    0.1
% 3.09/0.99  --splitting_mode                        input
% 3.09/0.99  --splitting_grd                         true
% 3.09/0.99  --splitting_cvd                         false
% 3.09/0.99  --splitting_cvd_svl                     false
% 3.09/0.99  --splitting_nvd                         32
% 3.09/0.99  --sub_typing                            true
% 3.09/0.99  --prep_gs_sim                           true
% 3.09/0.99  --prep_unflatten                        true
% 3.09/0.99  --prep_res_sim                          true
% 3.09/0.99  --prep_upred                            true
% 3.09/0.99  --prep_sem_filter                       exhaustive
% 3.09/0.99  --prep_sem_filter_out                   false
% 3.09/0.99  --pred_elim                             true
% 3.09/0.99  --res_sim_input                         true
% 3.09/0.99  --eq_ax_congr_red                       true
% 3.09/0.99  --pure_diseq_elim                       true
% 3.09/0.99  --brand_transform                       false
% 3.09/0.99  --non_eq_to_eq                          false
% 3.09/0.99  --prep_def_merge                        true
% 3.09/0.99  --prep_def_merge_prop_impl              false
% 3.09/0.99  --prep_def_merge_mbd                    true
% 3.09/0.99  --prep_def_merge_tr_red                 false
% 3.09/0.99  --prep_def_merge_tr_cl                  false
% 3.09/0.99  --smt_preprocessing                     true
% 3.09/0.99  --smt_ac_axioms                         fast
% 3.09/0.99  --preprocessed_out                      false
% 3.09/0.99  --preprocessed_stats                    false
% 3.09/0.99  
% 3.09/0.99  ------ Abstraction refinement Options
% 3.09/0.99  
% 3.09/0.99  --abstr_ref                             []
% 3.09/0.99  --abstr_ref_prep                        false
% 3.09/0.99  --abstr_ref_until_sat                   false
% 3.09/0.99  --abstr_ref_sig_restrict                funpre
% 3.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/0.99  --abstr_ref_under                       []
% 3.09/0.99  
% 3.09/0.99  ------ SAT Options
% 3.09/0.99  
% 3.09/0.99  --sat_mode                              false
% 3.09/0.99  --sat_fm_restart_options                ""
% 3.09/0.99  --sat_gr_def                            false
% 3.09/0.99  --sat_epr_types                         true
% 3.09/0.99  --sat_non_cyclic_types                  false
% 3.09/0.99  --sat_finite_models                     false
% 3.09/0.99  --sat_fm_lemmas                         false
% 3.09/0.99  --sat_fm_prep                           false
% 3.09/0.99  --sat_fm_uc_incr                        true
% 3.09/0.99  --sat_out_model                         small
% 3.09/0.99  --sat_out_clauses                       false
% 3.09/0.99  
% 3.09/0.99  ------ QBF Options
% 3.09/0.99  
% 3.09/0.99  --qbf_mode                              false
% 3.09/0.99  --qbf_elim_univ                         false
% 3.09/0.99  --qbf_dom_inst                          none
% 3.09/0.99  --qbf_dom_pre_inst                      false
% 3.09/0.99  --qbf_sk_in                             false
% 3.09/0.99  --qbf_pred_elim                         true
% 3.09/0.99  --qbf_split                             512
% 3.09/0.99  
% 3.09/0.99  ------ BMC1 Options
% 3.09/0.99  
% 3.09/0.99  --bmc1_incremental                      false
% 3.09/0.99  --bmc1_axioms                           reachable_all
% 3.09/0.99  --bmc1_min_bound                        0
% 3.09/0.99  --bmc1_max_bound                        -1
% 3.09/0.99  --bmc1_max_bound_default                -1
% 3.09/0.99  --bmc1_symbol_reachability              true
% 3.09/0.99  --bmc1_property_lemmas                  false
% 3.09/0.99  --bmc1_k_induction                      false
% 3.09/0.99  --bmc1_non_equiv_states                 false
% 3.09/0.99  --bmc1_deadlock                         false
% 3.09/0.99  --bmc1_ucm                              false
% 3.09/0.99  --bmc1_add_unsat_core                   none
% 3.09/0.99  --bmc1_unsat_core_children              false
% 3.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/0.99  --bmc1_out_stat                         full
% 3.09/0.99  --bmc1_ground_init                      false
% 3.09/0.99  --bmc1_pre_inst_next_state              false
% 3.09/0.99  --bmc1_pre_inst_state                   false
% 3.09/0.99  --bmc1_pre_inst_reach_state             false
% 3.09/0.99  --bmc1_out_unsat_core                   false
% 3.09/0.99  --bmc1_aig_witness_out                  false
% 3.09/0.99  --bmc1_verbose                          false
% 3.09/0.99  --bmc1_dump_clauses_tptp                false
% 3.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.09/0.99  --bmc1_dump_file                        -
% 3.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.09/0.99  --bmc1_ucm_extend_mode                  1
% 3.09/0.99  --bmc1_ucm_init_mode                    2
% 3.09/0.99  --bmc1_ucm_cone_mode                    none
% 3.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.09/0.99  --bmc1_ucm_relax_model                  4
% 3.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/0.99  --bmc1_ucm_layered_model                none
% 3.09/0.99  --bmc1_ucm_max_lemma_size               10
% 3.09/0.99  
% 3.09/0.99  ------ AIG Options
% 3.09/0.99  
% 3.09/0.99  --aig_mode                              false
% 3.09/0.99  
% 3.09/0.99  ------ Instantiation Options
% 3.09/0.99  
% 3.09/0.99  --instantiation_flag                    true
% 3.09/0.99  --inst_sos_flag                         false
% 3.09/0.99  --inst_sos_phase                        true
% 3.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/0.99  --inst_lit_sel_side                     num_symb
% 3.09/0.99  --inst_solver_per_active                1400
% 3.09/0.99  --inst_solver_calls_frac                1.
% 3.09/0.99  --inst_passive_queue_type               priority_queues
% 3.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/0.99  --inst_passive_queues_freq              [25;2]
% 3.09/0.99  --inst_dismatching                      true
% 3.09/0.99  --inst_eager_unprocessed_to_passive     true
% 3.09/0.99  --inst_prop_sim_given                   true
% 3.09/0.99  --inst_prop_sim_new                     false
% 3.09/0.99  --inst_subs_new                         false
% 3.09/0.99  --inst_eq_res_simp                      false
% 3.09/0.99  --inst_subs_given                       false
% 3.09/0.99  --inst_orphan_elimination               true
% 3.09/0.99  --inst_learning_loop_flag               true
% 3.09/0.99  --inst_learning_start                   3000
% 3.09/0.99  --inst_learning_factor                  2
% 3.09/0.99  --inst_start_prop_sim_after_learn       3
% 3.09/0.99  --inst_sel_renew                        solver
% 3.09/0.99  --inst_lit_activity_flag                true
% 3.09/0.99  --inst_restr_to_given                   false
% 3.09/0.99  --inst_activity_threshold               500
% 3.09/0.99  --inst_out_proof                        true
% 3.09/0.99  
% 3.09/0.99  ------ Resolution Options
% 3.09/0.99  
% 3.09/0.99  --resolution_flag                       true
% 3.09/0.99  --res_lit_sel                           adaptive
% 3.09/0.99  --res_lit_sel_side                      none
% 3.09/0.99  --res_ordering                          kbo
% 3.09/0.99  --res_to_prop_solver                    active
% 3.09/0.99  --res_prop_simpl_new                    false
% 3.09/0.99  --res_prop_simpl_given                  true
% 3.09/0.99  --res_passive_queue_type                priority_queues
% 3.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/0.99  --res_passive_queues_freq               [15;5]
% 3.09/0.99  --res_forward_subs                      full
% 3.09/0.99  --res_backward_subs                     full
% 3.09/0.99  --res_forward_subs_resolution           true
% 3.09/0.99  --res_backward_subs_resolution          true
% 3.09/0.99  --res_orphan_elimination                true
% 3.09/0.99  --res_time_limit                        2.
% 3.09/0.99  --res_out_proof                         true
% 3.09/0.99  
% 3.09/0.99  ------ Superposition Options
% 3.09/0.99  
% 3.09/0.99  --superposition_flag                    true
% 3.09/0.99  --sup_passive_queue_type                priority_queues
% 3.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.09/0.99  --demod_completeness_check              fast
% 3.09/0.99  --demod_use_ground                      true
% 3.09/0.99  --sup_to_prop_solver                    passive
% 3.09/0.99  --sup_prop_simpl_new                    true
% 3.09/0.99  --sup_prop_simpl_given                  true
% 3.09/0.99  --sup_fun_splitting                     false
% 3.09/0.99  --sup_smt_interval                      50000
% 3.09/0.99  
% 3.09/0.99  ------ Superposition Simplification Setup
% 3.09/0.99  
% 3.09/0.99  --sup_indices_passive                   []
% 3.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_full_bw                           [BwDemod]
% 3.09/0.99  --sup_immed_triv                        [TrivRules]
% 3.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_immed_bw_main                     []
% 3.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.99  
% 3.09/0.99  ------ Combination Options
% 3.09/0.99  
% 3.09/0.99  --comb_res_mult                         3
% 3.09/0.99  --comb_sup_mult                         2
% 3.09/0.99  --comb_inst_mult                        10
% 3.09/0.99  
% 3.09/0.99  ------ Debug Options
% 3.09/0.99  
% 3.09/0.99  --dbg_backtrace                         false
% 3.09/0.99  --dbg_dump_prop_clauses                 false
% 3.09/0.99  --dbg_dump_prop_clauses_file            -
% 3.09/0.99  --dbg_out_stat                          false
% 3.09/0.99  ------ Parsing...
% 3.09/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.09/0.99  ------ Proving...
% 3.09/0.99  ------ Problem Properties 
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  clauses                                 39
% 3.09/0.99  conjectures                             3
% 3.09/0.99  EPR                                     3
% 3.09/0.99  Horn                                    34
% 3.09/0.99  unary                                   13
% 3.09/0.99  binary                                  8
% 3.09/0.99  lits                                    99
% 3.09/0.99  lits eq                                 41
% 3.09/0.99  fd_pure                                 0
% 3.09/0.99  fd_pseudo                               0
% 3.09/0.99  fd_cond                                 2
% 3.09/0.99  fd_pseudo_cond                          1
% 3.09/0.99  AC symbols                              0
% 3.09/0.99  
% 3.09/0.99  ------ Schedule dynamic 5 is on 
% 3.09/0.99  
% 3.09/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  ------ 
% 3.09/0.99  Current options:
% 3.09/0.99  ------ 
% 3.09/0.99  
% 3.09/0.99  ------ Input Options
% 3.09/0.99  
% 3.09/0.99  --out_options                           all
% 3.09/0.99  --tptp_safe_out                         true
% 3.09/0.99  --problem_path                          ""
% 3.09/0.99  --include_path                          ""
% 3.09/0.99  --clausifier                            res/vclausify_rel
% 3.09/0.99  --clausifier_options                    --mode clausify
% 3.09/0.99  --stdin                                 false
% 3.09/0.99  --stats_out                             all
% 3.09/0.99  
% 3.09/0.99  ------ General Options
% 3.09/0.99  
% 3.09/0.99  --fof                                   false
% 3.09/0.99  --time_out_real                         305.
% 3.09/0.99  --time_out_virtual                      -1.
% 3.09/0.99  --symbol_type_check                     false
% 3.09/0.99  --clausify_out                          false
% 3.09/0.99  --sig_cnt_out                           false
% 3.09/0.99  --trig_cnt_out                          false
% 3.09/0.99  --trig_cnt_out_tolerance                1.
% 3.09/0.99  --trig_cnt_out_sk_spl                   false
% 3.09/0.99  --abstr_cl_out                          false
% 3.09/0.99  
% 3.09/0.99  ------ Global Options
% 3.09/0.99  
% 3.09/0.99  --schedule                              default
% 3.09/0.99  --add_important_lit                     false
% 3.09/0.99  --prop_solver_per_cl                    1000
% 3.09/0.99  --min_unsat_core                        false
% 3.09/0.99  --soft_assumptions                      false
% 3.09/0.99  --soft_lemma_size                       3
% 3.09/0.99  --prop_impl_unit_size                   0
% 3.09/0.99  --prop_impl_unit                        []
% 3.09/0.99  --share_sel_clauses                     true
% 3.09/0.99  --reset_solvers                         false
% 3.09/0.99  --bc_imp_inh                            [conj_cone]
% 3.09/0.99  --conj_cone_tolerance                   3.
% 3.09/0.99  --extra_neg_conj                        none
% 3.09/0.99  --large_theory_mode                     true
% 3.09/0.99  --prolific_symb_bound                   200
% 3.09/0.99  --lt_threshold                          2000
% 3.09/0.99  --clause_weak_htbl                      true
% 3.09/0.99  --gc_record_bc_elim                     false
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing Options
% 3.09/0.99  
% 3.09/0.99  --preprocessing_flag                    true
% 3.09/0.99  --time_out_prep_mult                    0.1
% 3.09/0.99  --splitting_mode                        input
% 3.09/0.99  --splitting_grd                         true
% 3.09/0.99  --splitting_cvd                         false
% 3.09/0.99  --splitting_cvd_svl                     false
% 3.09/0.99  --splitting_nvd                         32
% 3.09/0.99  --sub_typing                            true
% 3.09/0.99  --prep_gs_sim                           true
% 3.09/0.99  --prep_unflatten                        true
% 3.09/0.99  --prep_res_sim                          true
% 3.09/0.99  --prep_upred                            true
% 3.09/0.99  --prep_sem_filter                       exhaustive
% 3.09/0.99  --prep_sem_filter_out                   false
% 3.09/0.99  --pred_elim                             true
% 3.09/0.99  --res_sim_input                         true
% 3.09/0.99  --eq_ax_congr_red                       true
% 3.09/0.99  --pure_diseq_elim                       true
% 3.09/0.99  --brand_transform                       false
% 3.09/0.99  --non_eq_to_eq                          false
% 3.09/0.99  --prep_def_merge                        true
% 3.09/0.99  --prep_def_merge_prop_impl              false
% 3.09/0.99  --prep_def_merge_mbd                    true
% 3.09/0.99  --prep_def_merge_tr_red                 false
% 3.09/0.99  --prep_def_merge_tr_cl                  false
% 3.09/0.99  --smt_preprocessing                     true
% 3.09/0.99  --smt_ac_axioms                         fast
% 3.09/0.99  --preprocessed_out                      false
% 3.09/0.99  --preprocessed_stats                    false
% 3.09/0.99  
% 3.09/0.99  ------ Abstraction refinement Options
% 3.09/0.99  
% 3.09/0.99  --abstr_ref                             []
% 3.09/0.99  --abstr_ref_prep                        false
% 3.09/0.99  --abstr_ref_until_sat                   false
% 3.09/0.99  --abstr_ref_sig_restrict                funpre
% 3.09/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.09/0.99  --abstr_ref_under                       []
% 3.09/0.99  
% 3.09/0.99  ------ SAT Options
% 3.09/0.99  
% 3.09/0.99  --sat_mode                              false
% 3.09/0.99  --sat_fm_restart_options                ""
% 3.09/0.99  --sat_gr_def                            false
% 3.09/0.99  --sat_epr_types                         true
% 3.09/0.99  --sat_non_cyclic_types                  false
% 3.09/0.99  --sat_finite_models                     false
% 3.09/0.99  --sat_fm_lemmas                         false
% 3.09/0.99  --sat_fm_prep                           false
% 3.09/0.99  --sat_fm_uc_incr                        true
% 3.09/0.99  --sat_out_model                         small
% 3.09/0.99  --sat_out_clauses                       false
% 3.09/0.99  
% 3.09/0.99  ------ QBF Options
% 3.09/0.99  
% 3.09/0.99  --qbf_mode                              false
% 3.09/0.99  --qbf_elim_univ                         false
% 3.09/0.99  --qbf_dom_inst                          none
% 3.09/0.99  --qbf_dom_pre_inst                      false
% 3.09/0.99  --qbf_sk_in                             false
% 3.09/0.99  --qbf_pred_elim                         true
% 3.09/0.99  --qbf_split                             512
% 3.09/0.99  
% 3.09/0.99  ------ BMC1 Options
% 3.09/0.99  
% 3.09/0.99  --bmc1_incremental                      false
% 3.09/0.99  --bmc1_axioms                           reachable_all
% 3.09/0.99  --bmc1_min_bound                        0
% 3.09/0.99  --bmc1_max_bound                        -1
% 3.09/0.99  --bmc1_max_bound_default                -1
% 3.09/0.99  --bmc1_symbol_reachability              true
% 3.09/0.99  --bmc1_property_lemmas                  false
% 3.09/0.99  --bmc1_k_induction                      false
% 3.09/0.99  --bmc1_non_equiv_states                 false
% 3.09/0.99  --bmc1_deadlock                         false
% 3.09/0.99  --bmc1_ucm                              false
% 3.09/0.99  --bmc1_add_unsat_core                   none
% 3.09/0.99  --bmc1_unsat_core_children              false
% 3.09/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.09/0.99  --bmc1_out_stat                         full
% 3.09/0.99  --bmc1_ground_init                      false
% 3.09/0.99  --bmc1_pre_inst_next_state              false
% 3.09/0.99  --bmc1_pre_inst_state                   false
% 3.09/0.99  --bmc1_pre_inst_reach_state             false
% 3.09/0.99  --bmc1_out_unsat_core                   false
% 3.09/0.99  --bmc1_aig_witness_out                  false
% 3.09/0.99  --bmc1_verbose                          false
% 3.09/0.99  --bmc1_dump_clauses_tptp                false
% 3.09/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.09/0.99  --bmc1_dump_file                        -
% 3.09/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.09/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.09/0.99  --bmc1_ucm_extend_mode                  1
% 3.09/0.99  --bmc1_ucm_init_mode                    2
% 3.09/0.99  --bmc1_ucm_cone_mode                    none
% 3.09/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.09/0.99  --bmc1_ucm_relax_model                  4
% 3.09/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.09/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.09/0.99  --bmc1_ucm_layered_model                none
% 3.09/0.99  --bmc1_ucm_max_lemma_size               10
% 3.09/0.99  
% 3.09/0.99  ------ AIG Options
% 3.09/0.99  
% 3.09/0.99  --aig_mode                              false
% 3.09/0.99  
% 3.09/0.99  ------ Instantiation Options
% 3.09/0.99  
% 3.09/0.99  --instantiation_flag                    true
% 3.09/0.99  --inst_sos_flag                         false
% 3.09/0.99  --inst_sos_phase                        true
% 3.09/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.09/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.09/0.99  --inst_lit_sel_side                     none
% 3.09/0.99  --inst_solver_per_active                1400
% 3.09/0.99  --inst_solver_calls_frac                1.
% 3.09/0.99  --inst_passive_queue_type               priority_queues
% 3.09/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.09/0.99  --inst_passive_queues_freq              [25;2]
% 3.09/0.99  --inst_dismatching                      true
% 3.09/0.99  --inst_eager_unprocessed_to_passive     true
% 3.09/0.99  --inst_prop_sim_given                   true
% 3.09/0.99  --inst_prop_sim_new                     false
% 3.09/0.99  --inst_subs_new                         false
% 3.09/0.99  --inst_eq_res_simp                      false
% 3.09/0.99  --inst_subs_given                       false
% 3.09/0.99  --inst_orphan_elimination               true
% 3.09/0.99  --inst_learning_loop_flag               true
% 3.09/0.99  --inst_learning_start                   3000
% 3.09/0.99  --inst_learning_factor                  2
% 3.09/0.99  --inst_start_prop_sim_after_learn       3
% 3.09/0.99  --inst_sel_renew                        solver
% 3.09/0.99  --inst_lit_activity_flag                true
% 3.09/0.99  --inst_restr_to_given                   false
% 3.09/0.99  --inst_activity_threshold               500
% 3.09/0.99  --inst_out_proof                        true
% 3.09/0.99  
% 3.09/0.99  ------ Resolution Options
% 3.09/0.99  
% 3.09/0.99  --resolution_flag                       false
% 3.09/0.99  --res_lit_sel                           adaptive
% 3.09/0.99  --res_lit_sel_side                      none
% 3.09/0.99  --res_ordering                          kbo
% 3.09/0.99  --res_to_prop_solver                    active
% 3.09/0.99  --res_prop_simpl_new                    false
% 3.09/0.99  --res_prop_simpl_given                  true
% 3.09/0.99  --res_passive_queue_type                priority_queues
% 3.09/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.09/0.99  --res_passive_queues_freq               [15;5]
% 3.09/0.99  --res_forward_subs                      full
% 3.09/0.99  --res_backward_subs                     full
% 3.09/0.99  --res_forward_subs_resolution           true
% 3.09/0.99  --res_backward_subs_resolution          true
% 3.09/0.99  --res_orphan_elimination                true
% 3.09/0.99  --res_time_limit                        2.
% 3.09/0.99  --res_out_proof                         true
% 3.09/0.99  
% 3.09/0.99  ------ Superposition Options
% 3.09/0.99  
% 3.09/0.99  --superposition_flag                    true
% 3.09/0.99  --sup_passive_queue_type                priority_queues
% 3.09/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.09/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.09/0.99  --demod_completeness_check              fast
% 3.09/0.99  --demod_use_ground                      true
% 3.09/0.99  --sup_to_prop_solver                    passive
% 3.09/0.99  --sup_prop_simpl_new                    true
% 3.09/0.99  --sup_prop_simpl_given                  true
% 3.09/0.99  --sup_fun_splitting                     false
% 3.09/0.99  --sup_smt_interval                      50000
% 3.09/0.99  
% 3.09/0.99  ------ Superposition Simplification Setup
% 3.09/0.99  
% 3.09/0.99  --sup_indices_passive                   []
% 3.09/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.09/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.09/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_full_bw                           [BwDemod]
% 3.09/0.99  --sup_immed_triv                        [TrivRules]
% 3.09/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.09/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_immed_bw_main                     []
% 3.09/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.09/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.09/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.09/0.99  
% 3.09/0.99  ------ Combination Options
% 3.09/0.99  
% 3.09/0.99  --comb_res_mult                         3
% 3.09/0.99  --comb_sup_mult                         2
% 3.09/0.99  --comb_inst_mult                        10
% 3.09/0.99  
% 3.09/0.99  ------ Debug Options
% 3.09/0.99  
% 3.09/0.99  --dbg_backtrace                         false
% 3.09/0.99  --dbg_dump_prop_clauses                 false
% 3.09/0.99  --dbg_dump_prop_clauses_file            -
% 3.09/0.99  --dbg_out_stat                          false
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  ------ Proving...
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  % SZS status Theorem for theBenchmark.p
% 3.09/0.99  
% 3.09/0.99   Resolution empty clause
% 3.09/0.99  
% 3.09/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.09/0.99  
% 3.09/0.99  fof(f18,axiom,(
% 3.09/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f41,plain,(
% 3.09/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.99    inference(ennf_transformation,[],[f18])).
% 3.09/0.99  
% 3.09/0.99  fof(f42,plain,(
% 3.09/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.99    inference(flattening,[],[f41])).
% 3.09/0.99  
% 3.09/0.99  fof(f49,plain,(
% 3.09/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.99    inference(nnf_transformation,[],[f42])).
% 3.09/0.99  
% 3.09/0.99  fof(f75,plain,(
% 3.09/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/0.99    inference(cnf_transformation,[],[f49])).
% 3.09/0.99  
% 3.09/0.99  fof(f21,conjecture,(
% 3.09/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f22,negated_conjecture,(
% 3.09/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.09/0.99    inference(negated_conjecture,[],[f21])).
% 3.09/0.99  
% 3.09/0.99  fof(f45,plain,(
% 3.09/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.09/0.99    inference(ennf_transformation,[],[f22])).
% 3.09/0.99  
% 3.09/0.99  fof(f46,plain,(
% 3.09/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.09/0.99    inference(flattening,[],[f45])).
% 3.09/0.99  
% 3.09/0.99  fof(f52,plain,(
% 3.09/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.09/0.99    introduced(choice_axiom,[])).
% 3.09/0.99  
% 3.09/0.99  fof(f53,plain,(
% 3.09/0.99    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f46,f52])).
% 3.09/0.99  
% 3.09/0.99  fof(f88,plain,(
% 3.09/0.99    v1_funct_2(sK3,sK1,sK2)),
% 3.09/0.99    inference(cnf_transformation,[],[f53])).
% 3.09/0.99  
% 3.09/0.99  fof(f89,plain,(
% 3.09/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.09/0.99    inference(cnf_transformation,[],[f53])).
% 3.09/0.99  
% 3.09/0.99  fof(f16,axiom,(
% 3.09/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f39,plain,(
% 3.09/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.99    inference(ennf_transformation,[],[f16])).
% 3.09/0.99  
% 3.09/0.99  fof(f73,plain,(
% 3.09/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/0.99    inference(cnf_transformation,[],[f39])).
% 3.09/0.99  
% 3.09/0.99  fof(f6,axiom,(
% 3.09/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f27,plain,(
% 3.09/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(ennf_transformation,[],[f6])).
% 3.09/0.99  
% 3.09/0.99  fof(f60,plain,(
% 3.09/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f27])).
% 3.09/0.99  
% 3.09/0.99  fof(f7,axiom,(
% 3.09/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f61,plain,(
% 3.09/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.09/0.99    inference(cnf_transformation,[],[f7])).
% 3.09/0.99  
% 3.09/0.99  fof(f14,axiom,(
% 3.09/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f36,plain,(
% 3.09/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.09/0.99    inference(ennf_transformation,[],[f14])).
% 3.09/0.99  
% 3.09/0.99  fof(f37,plain,(
% 3.09/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(flattening,[],[f36])).
% 3.09/0.99  
% 3.09/0.99  fof(f71,plain,(
% 3.09/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f37])).
% 3.09/0.99  
% 3.09/0.99  fof(f90,plain,(
% 3.09/0.99    v2_funct_1(sK3)),
% 3.09/0.99    inference(cnf_transformation,[],[f53])).
% 3.09/0.99  
% 3.09/0.99  fof(f87,plain,(
% 3.09/0.99    v1_funct_1(sK3)),
% 3.09/0.99    inference(cnf_transformation,[],[f53])).
% 3.09/0.99  
% 3.09/0.99  fof(f20,axiom,(
% 3.09/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f43,plain,(
% 3.09/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.09/0.99    inference(ennf_transformation,[],[f20])).
% 3.09/0.99  
% 3.09/0.99  fof(f44,plain,(
% 3.09/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(flattening,[],[f43])).
% 3.09/0.99  
% 3.09/0.99  fof(f86,plain,(
% 3.09/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f44])).
% 3.09/0.99  
% 3.09/0.99  fof(f17,axiom,(
% 3.09/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f40,plain,(
% 3.09/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.99    inference(ennf_transformation,[],[f17])).
% 3.09/0.99  
% 3.09/0.99  fof(f74,plain,(
% 3.09/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/0.99    inference(cnf_transformation,[],[f40])).
% 3.09/0.99  
% 3.09/0.99  fof(f91,plain,(
% 3.09/0.99    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.09/0.99    inference(cnf_transformation,[],[f53])).
% 3.09/0.99  
% 3.09/0.99  fof(f70,plain,(
% 3.09/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f37])).
% 3.09/0.99  
% 3.09/0.99  fof(f12,axiom,(
% 3.09/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f32,plain,(
% 3.09/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.09/0.99    inference(ennf_transformation,[],[f12])).
% 3.09/0.99  
% 3.09/0.99  fof(f33,plain,(
% 3.09/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(flattening,[],[f32])).
% 3.09/0.99  
% 3.09/0.99  fof(f68,plain,(
% 3.09/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f33])).
% 3.09/0.99  
% 3.09/0.99  fof(f67,plain,(
% 3.09/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f33])).
% 3.09/0.99  
% 3.09/0.99  fof(f85,plain,(
% 3.09/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f44])).
% 3.09/0.99  
% 3.09/0.99  fof(f92,plain,(
% 3.09/0.99    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.09/0.99    inference(cnf_transformation,[],[f53])).
% 3.09/0.99  
% 3.09/0.99  fof(f79,plain,(
% 3.09/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/0.99    inference(cnf_transformation,[],[f49])).
% 3.09/0.99  
% 3.09/0.99  fof(f97,plain,(
% 3.09/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.09/0.99    inference(equality_resolution,[],[f79])).
% 3.09/0.99  
% 3.09/0.99  fof(f3,axiom,(
% 3.09/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f47,plain,(
% 3.09/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.09/0.99    inference(nnf_transformation,[],[f3])).
% 3.09/0.99  
% 3.09/0.99  fof(f48,plain,(
% 3.09/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.09/0.99    inference(flattening,[],[f47])).
% 3.09/0.99  
% 3.09/0.99  fof(f58,plain,(
% 3.09/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.09/0.99    inference(cnf_transformation,[],[f48])).
% 3.09/0.99  
% 3.09/0.99  fof(f93,plain,(
% 3.09/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.09/0.99    inference(equality_resolution,[],[f58])).
% 3.09/0.99  
% 3.09/0.99  fof(f1,axiom,(
% 3.09/0.99    v1_xboole_0(k1_xboole_0)),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f54,plain,(
% 3.09/0.99    v1_xboole_0(k1_xboole_0)),
% 3.09/0.99    inference(cnf_transformation,[],[f1])).
% 3.09/0.99  
% 3.09/0.99  fof(f2,axiom,(
% 3.09/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f26,plain,(
% 3.09/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.09/0.99    inference(ennf_transformation,[],[f2])).
% 3.09/0.99  
% 3.09/0.99  fof(f55,plain,(
% 3.09/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f26])).
% 3.09/0.99  
% 3.09/0.99  fof(f15,axiom,(
% 3.09/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f38,plain,(
% 3.09/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.09/0.99    inference(ennf_transformation,[],[f15])).
% 3.09/0.99  
% 3.09/0.99  fof(f72,plain,(
% 3.09/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f38])).
% 3.09/0.99  
% 3.09/0.99  fof(f10,axiom,(
% 3.09/0.99    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f64,plain,(
% 3.09/0.99    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.09/0.99    inference(cnf_transformation,[],[f10])).
% 3.09/0.99  
% 3.09/0.99  fof(f57,plain,(
% 3.09/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.09/0.99    inference(cnf_transformation,[],[f48])).
% 3.09/0.99  
% 3.09/0.99  fof(f94,plain,(
% 3.09/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.09/0.99    inference(equality_resolution,[],[f57])).
% 3.09/0.99  
% 3.09/0.99  fof(f78,plain,(
% 3.09/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.09/0.99    inference(cnf_transformation,[],[f49])).
% 3.09/0.99  
% 3.09/0.99  fof(f98,plain,(
% 3.09/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.09/0.99    inference(equality_resolution,[],[f78])).
% 3.09/0.99  
% 3.09/0.99  fof(f19,axiom,(
% 3.09/0.99    ! [X0,X1] : ? [X2] : (v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f23,plain,(
% 3.09/0.99    ! [X0,X1] : ? [X2] : (v1_funct_1(X2) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.99    inference(pure_predicate_removal,[],[f19])).
% 3.09/0.99  
% 3.09/0.99  fof(f24,plain,(
% 3.09/0.99    ! [X0,X1] : ? [X2] : (v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.99    inference(pure_predicate_removal,[],[f23])).
% 3.09/0.99  
% 3.09/0.99  fof(f50,plain,(
% 3.09/0.99    ! [X1,X0] : (? [X2] : (v1_funct_1(X2) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_1(sK0(X0,X1)) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.09/0.99    introduced(choice_axiom,[])).
% 3.09/0.99  
% 3.09/0.99  fof(f51,plain,(
% 3.09/0.99    ! [X0,X1] : (v1_funct_1(sK0(X0,X1)) & v1_relat_1(sK0(X0,X1)) & m1_subset_1(sK0(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.09/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f50])).
% 3.09/0.99  
% 3.09/0.99  fof(f82,plain,(
% 3.09/0.99    ( ! [X0,X1] : (v1_relat_1(sK0(X0,X1))) )),
% 3.09/0.99    inference(cnf_transformation,[],[f51])).
% 3.09/0.99  
% 3.09/0.99  fof(f83,plain,(
% 3.09/0.99    ( ! [X0,X1] : (v1_funct_1(sK0(X0,X1))) )),
% 3.09/0.99    inference(cnf_transformation,[],[f51])).
% 3.09/0.99  
% 3.09/0.99  fof(f4,axiom,(
% 3.09/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f59,plain,(
% 3.09/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.09/0.99    inference(cnf_transformation,[],[f4])).
% 3.09/0.99  
% 3.09/0.99  fof(f11,axiom,(
% 3.09/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_funct_1(X1)))),
% 3.09/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.09/0.99  
% 3.09/0.99  fof(f30,plain,(
% 3.09/0.99    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.09/0.99    inference(ennf_transformation,[],[f11])).
% 3.09/0.99  
% 3.09/0.99  fof(f31,plain,(
% 3.09/0.99    ! [X0] : (! [X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.09/0.99    inference(flattening,[],[f30])).
% 3.09/0.99  
% 3.09/0.99  fof(f66,plain,(
% 3.09/0.99    ( ! [X0,X1] : (v1_funct_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.09/0.99    inference(cnf_transformation,[],[f31])).
% 3.09/0.99  
% 3.09/0.99  cnf(c_26,plain,
% 3.09/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.09/0.99      | k1_xboole_0 = X2 ),
% 3.09/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_37,negated_conjecture,
% 3.09/0.99      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.09/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_594,plain,
% 3.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.09/0.99      | sK1 != X1
% 3.09/0.99      | sK2 != X2
% 3.09/0.99      | sK3 != X0
% 3.09/0.99      | k1_xboole_0 = X2 ),
% 3.09/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_37]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_595,plain,
% 3.09/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.09/0.99      | k1_relset_1(sK1,sK2,sK3) = sK1
% 3.09/0.99      | k1_xboole_0 = sK2 ),
% 3.09/0.99      inference(unflattening,[status(thm)],[c_594]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_36,negated_conjecture,
% 3.09/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.09/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_597,plain,
% 3.09/0.99      ( k1_relset_1(sK1,sK2,sK3) = sK1 | k1_xboole_0 = sK2 ),
% 3.09/0.99      inference(global_propositional_subsumption,[status(thm)],[c_595,c_36]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1255,plain,
% 3.09/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_19,plain,
% 3.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1261,plain,
% 3.09/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.09/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_3247,plain,
% 3.09/0.99      ( k1_relset_1(sK1,sK2,sK3) = k1_relat_1(sK3) ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_1255,c_1261]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_3447,plain,
% 3.09/0.99      ( k1_relat_1(sK3) = sK1 | sK2 = k1_xboole_0 ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_597,c_3247]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_6,plain,
% 3.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1269,plain,
% 3.09/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.09/0.99      | v1_relat_1(X1) != iProver_top
% 3.09/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4162,plain,
% 3.09/0.99      ( v1_relat_1(k2_zfmisc_1(sK1,sK2)) != iProver_top
% 3.09/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_1255,c_1269]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_7,plain,
% 3.09/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.09/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1268,plain,
% 3.09/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4178,plain,
% 3.09/0.99      ( v1_relat_1(sK3) = iProver_top ),
% 3.09/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_4162,c_1268]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_16,plain,
% 3.09/0.99      ( ~ v2_funct_1(X0)
% 3.09/0.99      | ~ v1_funct_1(X0)
% 3.09/0.99      | ~ v1_relat_1(X0)
% 3.09/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_35,negated_conjecture,
% 3.09/0.99      ( v2_funct_1(sK3) ),
% 3.09/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_382,plain,
% 3.09/0.99      ( ~ v1_funct_1(X0)
% 3.09/0.99      | ~ v1_relat_1(X0)
% 3.09/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.09/0.99      | sK3 != X0 ),
% 3.09/0.99      inference(resolution_lifted,[status(thm)],[c_16,c_35]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_383,plain,
% 3.09/0.99      ( ~ v1_funct_1(sK3)
% 3.09/0.99      | ~ v1_relat_1(sK3)
% 3.09/0.99      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.09/0.99      inference(unflattening,[status(thm)],[c_382]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_38,negated_conjecture,
% 3.09/0.99      ( v1_funct_1(sK3) ),
% 3.09/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_385,plain,
% 3.09/0.99      ( ~ v1_relat_1(sK3) | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.09/0.99      inference(global_propositional_subsumption,[status(thm)],[c_383,c_38]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1252,plain,
% 3.09/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.09/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_385]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4186,plain,
% 3.09/0.99      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_4178,c_1252]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_30,plain,
% 3.09/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.09/0.99      | ~ v1_funct_1(X0)
% 3.09/0.99      | ~ v1_relat_1(X0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1256,plain,
% 3.09/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.09/0.99      | v1_funct_1(X0) != iProver_top
% 3.09/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4438,plain,
% 3.09/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.09/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_4186,c_1256]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_20,plain,
% 3.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1260,plain,
% 3.09/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.09/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2530,plain,
% 3.09/0.99      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_1255,c_1260]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_34,negated_conjecture,
% 3.09/0.99      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.09/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2542,plain,
% 3.09/0.99      ( k2_relat_1(sK3) = sK2 ),
% 3.09/0.99      inference(light_normalisation,[status(thm)],[c_2530,c_34]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_17,plain,
% 3.09/0.99      ( ~ v2_funct_1(X0)
% 3.09/0.99      | ~ v1_funct_1(X0)
% 3.09/0.99      | ~ v1_relat_1(X0)
% 3.09/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_368,plain,
% 3.09/0.99      ( ~ v1_funct_1(X0)
% 3.09/0.99      | ~ v1_relat_1(X0)
% 3.09/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.09/0.99      | sK3 != X0 ),
% 3.09/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_35]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_369,plain,
% 3.09/0.99      ( ~ v1_funct_1(sK3)
% 3.09/0.99      | ~ v1_relat_1(sK3)
% 3.09/0.99      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.09/0.99      inference(unflattening,[status(thm)],[c_368]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_371,plain,
% 3.09/0.99      ( ~ v1_relat_1(sK3) | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 3.09/0.99      inference(global_propositional_subsumption,[status(thm)],[c_369,c_38]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1253,plain,
% 3.09/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.09/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_371]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2566,plain,
% 3.09/0.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 | v1_relat_1(sK3) != iProver_top ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_2542,c_1253]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4184,plain,
% 3.09/0.99      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_4178,c_2566]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4439,plain,
% 3.09/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.09/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.09/0.99      inference(light_normalisation,[status(thm)],[c_4438,c_4184]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_39,plain,
% 3.09/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_13,plain,
% 3.09/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1558,plain,
% 3.09/0.99      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_13]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1559,plain,
% 3.09/0.99      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.09/0.99      | v1_funct_1(sK3) != iProver_top
% 3.09/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1558]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_14,plain,
% 3.09/0.99      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.09/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1566,plain,
% 3.09/0.99      ( ~ v1_funct_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1567,plain,
% 3.09/0.99      ( v1_funct_1(sK3) != iProver_top
% 3.09/0.99      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.09/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1566]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5093,plain,
% 3.09/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.09/0.99      inference(global_propositional_subsumption,
% 3.09/0.99                [status(thm)],
% 3.09/0.99                [c_4439,c_39,c_1559,c_1567,c_4178]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5098,plain,
% 3.09/0.99      ( sK2 = k1_xboole_0
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) = iProver_top ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_3447,c_5093]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_31,plain,
% 3.09/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.09/0.99      | ~ v1_funct_1(X0)
% 3.09/0.99      | ~ v1_relat_1(X0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_33,negated_conjecture,
% 3.09/0.99      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.09/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.09/0.99      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.09/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_605,plain,
% 3.09/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.09/0.99      | ~ v1_funct_1(X0)
% 3.09/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.09/0.99      | ~ v1_relat_1(X0)
% 3.09/0.99      | k2_funct_1(sK3) != X0
% 3.09/0.99      | k2_relat_1(X0) != sK1
% 3.09/0.99      | k1_relat_1(X0) != sK2 ),
% 3.09/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_33]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_606,plain,
% 3.09/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.09/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.09/0.99      | ~ v1_relat_1(k2_funct_1(sK3))
% 3.09/0.99      | k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.09/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2 ),
% 3.09/0.99      inference(unflattening,[status(thm)],[c_605]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1242,plain,
% 3.09/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.09/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.09/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4433,plain,
% 3.09/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.09/0.99      | sK2 != sK2
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.09/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_4184,c_1242]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4893,plain,
% 3.09/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.09/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.09/0.99      inference(equality_resolution_simp,[status(thm)],[c_4433]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_607,plain,
% 3.09/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.09/0.99      | k1_relat_1(k2_funct_1(sK3)) != sK2
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.09/0.99      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4895,plain,
% 3.09/0.99      ( k2_relat_1(k2_funct_1(sK3)) != sK1
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.09/0.99      inference(global_propositional_subsumption,
% 3.09/0.99                [status(thm)],
% 3.09/0.99                [c_4893,c_39,c_607,c_1559,c_1567,c_2566,c_4178]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4899,plain,
% 3.09/0.99      ( k1_relat_1(sK3) != sK1
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.09/0.99      inference(light_normalisation,[status(thm)],[c_4895,c_4186]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4903,plain,
% 3.09/0.99      ( sK2 = k1_xboole_0
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_3447,c_4899]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5133,plain,
% 3.09/0.99      ( sK2 = k1_xboole_0 ),
% 3.09/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5098,c_4903]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5136,plain,
% 3.09/0.99      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK3)))) = iProver_top ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_5133,c_5093]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_22,plain,
% 3.09/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.09/0.99      | k1_xboole_0 = X1
% 3.09/0.99      | k1_xboole_0 = X0 ),
% 3.09/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_457,plain,
% 3.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.09/0.99      | ~ v1_funct_1(X2)
% 3.09/0.99      | ~ v1_relat_1(X2)
% 3.09/0.99      | X2 != X0
% 3.09/0.99      | k2_relat_1(X2) != k1_xboole_0
% 3.09/0.99      | k1_relat_1(X2) != X1
% 3.09/0.99      | k1_xboole_0 = X0
% 3.09/0.99      | k1_xboole_0 = X1 ),
% 3.09/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_31]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_458,plain,
% 3.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0)))
% 3.09/0.99      | ~ v1_funct_1(X0)
% 3.09/0.99      | ~ v1_relat_1(X0)
% 3.09/0.99      | k2_relat_1(X0) != k1_xboole_0
% 3.09/0.99      | k1_xboole_0 = X0
% 3.09/0.99      | k1_xboole_0 = k1_relat_1(X0) ),
% 3.09/0.99      inference(unflattening,[status(thm)],[c_457]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1249,plain,
% 3.09/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.09/0.99      | k1_xboole_0 = X0
% 3.09/0.99      | k1_xboole_0 = k1_relat_1(X0)
% 3.09/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k1_xboole_0))) != iProver_top
% 3.09/0.99      | v1_funct_1(X0) != iProver_top
% 3.09/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_458]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2,plain,
% 3.09/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.09/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1442,plain,
% 3.09/0.99      ( k2_relat_1(X0) != k1_xboole_0
% 3.09/0.99      | k1_relat_1(X0) = k1_xboole_0
% 3.09/0.99      | k1_xboole_0 = X0
% 3.09/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.09/0.99      | v1_funct_1(X0) != iProver_top
% 3.09/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_1249,c_2]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4788,plain,
% 3.09/0.99      ( k1_relat_1(sK3) = k1_xboole_0
% 3.09/0.99      | sK2 != k1_xboole_0
% 3.09/0.99      | sK3 = k1_xboole_0
% 3.09/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.09/0.99      | v1_funct_1(sK3) != iProver_top
% 3.09/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_2542,c_1442]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_0,plain,
% 3.09/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_699,plain,
% 3.09/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.09/0.99      theory(equality) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1780,plain,
% 3.09/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK2) | sK2 != X0 ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_699]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1782,plain,
% 3.09/0.99      ( v1_xboole_0(sK2) | ~ v1_xboole_0(k1_xboole_0) | sK2 != k1_xboole_0 ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_1780]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1,plain,
% 3.09/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.09/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1875,plain,
% 3.09/0.99      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(sK3) | sK3 = X0 ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1877,plain,
% 3.09/0.99      ( ~ v1_xboole_0(sK3) | ~ v1_xboole_0(k1_xboole_0) | sK3 = k1_xboole_0 ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_1875]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_18,plain,
% 3.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/0.99      | ~ v1_xboole_0(X2)
% 3.09/0.99      | v1_xboole_0(X0) ),
% 3.09/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1262,plain,
% 3.09/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.09/0.99      | v1_xboole_0(X2) != iProver_top
% 3.09/0.99      | v1_xboole_0(X0) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2943,plain,
% 3.09/0.99      ( v1_xboole_0(sK2) != iProver_top | v1_xboole_0(sK3) = iProver_top ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_1255,c_1262]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2979,plain,
% 3.09/0.99      ( ~ v1_xboole_0(sK2) | v1_xboole_0(sK3) ),
% 3.09/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2943]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4889,plain,
% 3.09/0.99      ( sK3 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.09/0.99      inference(global_propositional_subsumption,
% 3.09/0.99                [status(thm)],
% 3.09/0.99                [c_4788,c_0,c_1782,c_1877,c_2979]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_4890,plain,
% 3.09/0.99      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.09/0.99      inference(renaming,[status(thm)],[c_4889]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5139,plain,
% 3.09/0.99      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_5133,c_4890]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5224,plain,
% 3.09/0.99      ( sK3 = k1_xboole_0 ),
% 3.09/0.99      inference(equality_resolution_simp,[status(thm)],[c_5139]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5278,plain,
% 3.09/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(k1_xboole_0)))) = iProver_top ),
% 3.09/0.99      inference(light_normalisation,[status(thm)],[c_5136,c_5224]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_11,plain,
% 3.09/0.99      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.09/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5280,plain,
% 3.09/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.09/0.99      inference(light_normalisation,[status(thm)],[c_5278,c_11]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_3,plain,
% 3.09/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.09/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5281,plain,
% 3.09/0.99      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_5280,c_3]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_23,plain,
% 3.09/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.09/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.09/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.09/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_522,plain,
% 3.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.09/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.09/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.09/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.09/0.99      | k2_funct_1(sK3) != X0
% 3.09/0.99      | sK1 != X1
% 3.09/0.99      | sK2 != k1_xboole_0 ),
% 3.09/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_33]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_523,plain,
% 3.09/0.99      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.09/0.99      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 3.09/0.99      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.09/0.99      | k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.09/0.99      | sK2 != k1_xboole_0 ),
% 3.09/0.99      inference(unflattening,[status(thm)],[c_522]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1246,plain,
% 3.09/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.09/0.99      | sK2 != k1_xboole_0
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1465,plain,
% 3.09/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.09/0.99      | sK2 != k1_xboole_0
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_1246,c_3]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5150,plain,
% 3.09/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.09/0.99      | k1_xboole_0 != k1_xboole_0
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_5133,c_1465]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5187,plain,
% 3.09/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.09/0.99      inference(equality_resolution_simp,[status(thm)],[c_5150]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5192,plain,
% 3.09/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(sK3)) != k1_xboole_0
% 3.09/0.99      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_5187,c_3]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5234,plain,
% 3.09/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 3.09/0.99      | m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_5224,c_5192]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5283,plain,
% 3.09/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0
% 3.09/0.99      | v1_funct_1(k2_funct_1(k1_xboole_0)) != iProver_top ),
% 3.09/0.99      inference(backward_subsumption_resolution,[status(thm)],[c_5281,c_5234]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_28,plain,
% 3.09/0.99      ( v1_relat_1(sK0(X0,X1)) ),
% 3.09/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_54,plain,
% 3.09/0.99      ( v1_relat_1(sK0(X0,X1)) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_27,plain,
% 3.09/0.99      ( v1_funct_1(sK0(X0,X1)) ),
% 3.09/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_57,plain,
% 3.09/0.99      ( v1_funct_1(sK0(X0,X1)) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_97,plain,
% 3.09/0.99      ( v1_funct_1(X0) != iProver_top
% 3.09/0.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.09/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_99,plain,
% 3.09/0.99      ( v1_funct_1(k2_funct_1(k1_xboole_0)) = iProver_top
% 3.09/0.99      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.09/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_97]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_107,plain,
% 3.09/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_109,plain,
% 3.09/0.99      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_107]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1575,plain,
% 3.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.09/0.99      | v1_relat_1(X0)
% 3.09/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1576,plain,
% 3.09/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.09/0.99      | v1_relat_1(X0) = iProver_top
% 3.09/0.99      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1575]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1578,plain,
% 3.09/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.09/0.99      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.09/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_1576]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5,plain,
% 3.09/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.09/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1660,plain,
% 3.09/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1663,plain,
% 3.09/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_1660]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1665,plain,
% 3.09/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_1663]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_12,plain,
% 3.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.09/0.99      | ~ v1_funct_1(X1)
% 3.09/0.99      | v1_funct_1(X0)
% 3.09/0.99      | ~ v1_relat_1(X1) ),
% 3.09/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_1631,plain,
% 3.09/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0(X1,X2)))
% 3.09/0.99      | v1_funct_1(X0)
% 3.09/0.99      | ~ v1_funct_1(sK0(X1,X2))
% 3.09/0.99      | ~ v1_relat_1(sK0(X1,X2)) ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2077,plain,
% 3.09/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0,X1)))
% 3.09/0.99      | ~ v1_funct_1(sK0(X0,X1))
% 3.09/0.99      | v1_funct_1(k1_xboole_0)
% 3.09/0.99      | ~ v1_relat_1(sK0(X0,X1)) ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_1631]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2079,plain,
% 3.09/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0,X1))) != iProver_top
% 3.09/0.99      | v1_funct_1(sK0(X0,X1)) != iProver_top
% 3.09/0.99      | v1_funct_1(k1_xboole_0) = iProver_top
% 3.09/0.99      | v1_relat_1(sK0(X0,X1)) != iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_2077]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2078,plain,
% 3.09/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0,X1))) ),
% 3.09/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_2081,plain,
% 3.09/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0(X0,X1))) = iProver_top ),
% 3.09/0.99      inference(predicate_to_equality,[status(thm)],[c_2078]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_6849,plain,
% 3.09/0.99      ( k1_relset_1(k1_xboole_0,sK1,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.09/0.99      inference(global_propositional_subsumption,
% 3.09/0.99                [status(thm)],
% 3.09/0.99                [c_5283,c_54,c_57,c_99,c_109,c_1578,c_1665,c_2079,c_2081]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_3250,plain,
% 3.09/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.09/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_3,c_1261]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5548,plain,
% 3.09/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_relat_1(k2_funct_1(k1_xboole_0)) ),
% 3.09/0.99      inference(superposition,[status(thm)],[c_5281,c_3250]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5142,plain,
% 3.09/0.99      ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0 ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_5133,c_4184]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_5228,plain,
% 3.09/0.99      ( k1_relat_1(k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_5224,c_5142]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_6201,plain,
% 3.09/0.99      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(k1_xboole_0)) = k1_xboole_0 ),
% 3.09/0.99      inference(light_normalisation,[status(thm)],[c_5548,c_5228]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_6851,plain,
% 3.09/0.99      ( k1_xboole_0 != k1_xboole_0 ),
% 3.09/0.99      inference(demodulation,[status(thm)],[c_6849,c_6201]) ).
% 3.09/0.99  
% 3.09/0.99  cnf(c_6852,plain,
% 3.09/0.99      ( $false ),
% 3.09/0.99      inference(equality_resolution_simp,[status(thm)],[c_6851]) ).
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.09/0.99  
% 3.09/0.99  ------                               Statistics
% 3.09/0.99  
% 3.09/0.99  ------ General
% 3.09/0.99  
% 3.09/0.99  abstr_ref_over_cycles:                  0
% 3.09/0.99  abstr_ref_under_cycles:                 0
% 3.09/0.99  gc_basic_clause_elim:                   0
% 3.09/0.99  forced_gc_time:                         0
% 3.09/0.99  parsing_time:                           0.01
% 3.09/0.99  unif_index_cands_time:                  0.
% 3.09/0.99  unif_index_add_time:                    0.
% 3.09/0.99  orderings_time:                         0.
% 3.09/0.99  out_proof_time:                         0.009
% 3.09/0.99  total_time:                             0.221
% 3.09/0.99  num_of_symbols:                         51
% 3.09/0.99  num_of_terms:                           4670
% 3.09/0.99  
% 3.09/0.99  ------ Preprocessing
% 3.09/0.99  
% 3.09/0.99  num_of_splits:                          0
% 3.09/0.99  num_of_split_atoms:                     0
% 3.09/0.99  num_of_reused_defs:                     0
% 3.09/0.99  num_eq_ax_congr_red:                    7
% 3.09/0.99  num_of_sem_filtered_clauses:            1
% 3.09/0.99  num_of_subtypes:                        0
% 3.09/0.99  monotx_restored_types:                  0
% 3.09/0.99  sat_num_of_epr_types:                   0
% 3.09/0.99  sat_num_of_non_cyclic_types:            0
% 3.09/0.99  sat_guarded_non_collapsed_types:        0
% 3.09/0.99  num_pure_diseq_elim:                    0
% 3.09/0.99  simp_replaced_by:                       0
% 3.09/0.99  res_preprocessed:                       147
% 3.09/0.99  prep_upred:                             0
% 3.09/0.99  prep_unflattend:                        44
% 3.09/0.99  smt_new_axioms:                         0
% 3.09/0.99  pred_elim_cands:                        6
% 3.09/0.99  pred_elim:                              2
% 3.09/0.99  pred_elim_cl:                           -1
% 3.09/0.99  pred_elim_cycles:                       3
% 3.09/0.99  merged_defs:                            0
% 3.09/0.99  merged_defs_ncl:                        0
% 3.09/0.99  bin_hyper_res:                          0
% 3.09/0.99  prep_cycles:                            3
% 3.09/0.99  pred_elim_time:                         0.007
% 3.09/0.99  splitting_time:                         0.
% 3.09/0.99  sem_filter_time:                        0.
% 3.09/0.99  monotx_time:                            0.
% 3.09/0.99  subtype_inf_time:                       0.
% 3.09/0.99  
% 3.09/0.99  ------ Problem properties
% 3.09/0.99  
% 3.09/0.99  clauses:                                39
% 3.09/0.99  conjectures:                            3
% 3.09/0.99  epr:                                    3
% 3.09/0.99  horn:                                   34
% 3.09/0.99  ground:                                 16
% 3.09/0.99  unary:                                  13
% 3.09/0.99  binary:                                 8
% 3.09/0.99  lits:                                   99
% 3.09/0.99  lits_eq:                                41
% 3.09/0.99  fd_pure:                                0
% 3.09/0.99  fd_pseudo:                              0
% 3.09/0.99  fd_cond:                                2
% 3.09/0.99  fd_pseudo_cond:                         1
% 3.09/0.99  ac_symbols:                             0
% 3.09/0.99  
% 3.09/0.99  ------ Propositional Solver
% 3.09/0.99  
% 3.09/0.99  prop_solver_calls:                      23
% 3.09/0.99  prop_fast_solver_calls:                 1051
% 3.09/0.99  smt_solver_calls:                       0
% 3.09/0.99  smt_fast_solver_calls:                  0
% 3.09/0.99  prop_num_of_clauses:                    2364
% 3.09/0.99  prop_preprocess_simplified:             6762
% 3.09/0.99  prop_fo_subsumed:                       30
% 3.09/0.99  prop_solver_time:                       0.
% 3.09/0.99  smt_solver_time:                        0.
% 3.09/0.99  smt_fast_solver_time:                   0.
% 3.09/0.99  prop_fast_solver_time:                  0.
% 3.09/0.99  prop_unsat_core_time:                   0.
% 3.09/0.99  
% 3.09/0.99  ------ QBF
% 3.09/0.99  
% 3.09/0.99  qbf_q_res:                              0
% 3.09/0.99  qbf_num_tautologies:                    0
% 3.09/0.99  qbf_prep_cycles:                        0
% 3.09/0.99  
% 3.09/0.99  ------ BMC1
% 3.09/0.99  
% 3.09/0.99  bmc1_current_bound:                     -1
% 3.09/0.99  bmc1_last_solved_bound:                 -1
% 3.09/0.99  bmc1_unsat_core_size:                   -1
% 3.09/0.99  bmc1_unsat_core_parents_size:           -1
% 3.09/0.99  bmc1_merge_next_fun:                    0
% 3.09/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.09/0.99  
% 3.09/0.99  ------ Instantiation
% 3.09/0.99  
% 3.09/0.99  inst_num_of_clauses:                    882
% 3.09/0.99  inst_num_in_passive:                    5
% 3.09/0.99  inst_num_in_active:                     457
% 3.09/0.99  inst_num_in_unprocessed:                420
% 3.09/0.99  inst_num_of_loops:                      520
% 3.09/0.99  inst_num_of_learning_restarts:          0
% 3.09/0.99  inst_num_moves_active_passive:          61
% 3.09/0.99  inst_lit_activity:                      0
% 3.09/0.99  inst_lit_activity_moves:                0
% 3.09/0.99  inst_num_tautologies:                   0
% 3.09/0.99  inst_num_prop_implied:                  0
% 3.09/0.99  inst_num_existing_simplified:           0
% 3.09/0.99  inst_num_eq_res_simplified:             0
% 3.09/0.99  inst_num_child_elim:                    0
% 3.09/0.99  inst_num_of_dismatching_blockings:      287
% 3.09/0.99  inst_num_of_non_proper_insts:           888
% 3.09/0.99  inst_num_of_duplicates:                 0
% 3.09/0.99  inst_inst_num_from_inst_to_res:         0
% 3.09/0.99  inst_dismatching_checking_time:         0.
% 3.09/0.99  
% 3.09/0.99  ------ Resolution
% 3.09/0.99  
% 3.09/0.99  res_num_of_clauses:                     0
% 3.09/0.99  res_num_in_passive:                     0
% 3.09/0.99  res_num_in_active:                      0
% 3.09/0.99  res_num_of_loops:                       150
% 3.09/0.99  res_forward_subset_subsumed:            36
% 3.09/0.99  res_backward_subset_subsumed:           0
% 3.09/0.99  res_forward_subsumed:                   0
% 3.09/0.99  res_backward_subsumed:                  0
% 3.09/0.99  res_forward_subsumption_resolution:     1
% 3.09/0.99  res_backward_subsumption_resolution:    0
% 3.09/0.99  res_clause_to_clause_subsumption:       262
% 3.09/0.99  res_orphan_elimination:                 0
% 3.09/0.99  res_tautology_del:                      101
% 3.09/0.99  res_num_eq_res_simplified:              0
% 3.09/0.99  res_num_sel_changes:                    0
% 3.09/0.99  res_moves_from_active_to_pass:          0
% 3.09/0.99  
% 3.09/0.99  ------ Superposition
% 3.09/0.99  
% 3.09/0.99  sup_time_total:                         0.
% 3.09/0.99  sup_time_generating:                    0.
% 3.09/0.99  sup_time_sim_full:                      0.
% 3.09/0.99  sup_time_sim_immed:                     0.
% 3.09/0.99  
% 3.09/0.99  sup_num_of_clauses:                     86
% 3.09/0.99  sup_num_in_active:                      65
% 3.09/0.99  sup_num_in_passive:                     21
% 3.09/0.99  sup_num_of_loops:                       102
% 3.09/0.99  sup_fw_superposition:                   89
% 3.09/0.99  sup_bw_superposition:                   40
% 3.09/0.99  sup_immediate_simplified:               93
% 3.09/0.99  sup_given_eliminated:                   1
% 3.09/0.99  comparisons_done:                       0
% 3.09/0.99  comparisons_avoided:                    5
% 3.09/0.99  
% 3.09/0.99  ------ Simplifications
% 3.09/0.99  
% 3.09/0.99  
% 3.09/0.99  sim_fw_subset_subsumed:                 15
% 3.09/0.99  sim_bw_subset_subsumed:                 7
% 3.09/0.99  sim_fw_subsumed:                        20
% 3.09/0.99  sim_bw_subsumed:                        4
% 3.09/0.99  sim_fw_subsumption_res:                 4
% 3.09/0.99  sim_bw_subsumption_res:                 2
% 3.09/0.99  sim_tautology_del:                      4
% 3.09/0.99  sim_eq_tautology_del:                   16
% 3.09/0.99  sim_eq_res_simp:                        4
% 3.09/0.99  sim_fw_demodulated:                     21
% 3.09/0.99  sim_bw_demodulated:                     45
% 3.09/0.99  sim_light_normalised:                   51
% 3.09/0.99  sim_joinable_taut:                      0
% 3.09/0.99  sim_joinable_simp:                      0
% 3.09/0.99  sim_ac_normalised:                      0
% 3.09/0.99  sim_smt_subsumption:                    0
% 3.09/0.99  
%------------------------------------------------------------------------------
