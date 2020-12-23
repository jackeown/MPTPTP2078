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
% DateTime   : Thu Dec  3 12:02:33 EST 2020

% Result     : Theorem 3.08s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :  174 (9378 expanded)
%              Number of clauses        :  116 (2919 expanded)
%              Number of leaves         :   15 (1839 expanded)
%              Depth                    :   27
%              Number of atoms          :  509 (50891 expanded)
%              Number of equality atoms :  262 (9907 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f43,plain,(
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

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f48,plain,
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

fof(f49,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f48])).

fof(f83,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f85,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f49])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f41])).

fof(f80,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f79,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f86,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f62,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f65,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
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

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f82,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f45])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f90,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f94,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f73])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1188,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1191,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3339,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1188,c_1191])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_3355,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3339,c_31])).

cnf(c_27,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1189,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3490,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3355,c_1189])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1486,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1487,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1486])).

cnf(c_4000,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3490,c_36,c_38,c_1487])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1193,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4126,plain,
    ( v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_4000,c_1193])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_111,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_672,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1691,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK1)
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_672])).

cnf(c_1692,plain,
    ( sK1 != X0
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1691])).

cnf(c_1694,plain,
    ( sK1 != k1_xboole_0
    | v1_xboole_0(sK1) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1692])).

cnf(c_1912,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2844,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_xboole_0(sK1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_1912])).

cnf(c_2845,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_xboole_0(sK1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2844])).

cnf(c_28,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_30,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_581,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != sK0
    | k1_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_30])).

cnf(c_582,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_594,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_582,c_16])).

cnf(c_1175,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_594])).

cnf(c_583,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_582])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1461,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1462,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1461])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1464,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1465,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1464])).

cnf(c_1562,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1175,c_36,c_38,c_583,c_1462,c_1465,c_1487])).

cnf(c_1563,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1562])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_32,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_354,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_32])).

cnf(c_355,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_354])).

cnf(c_357,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_355,c_35])).

cnf(c_1185,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_1490,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1185,c_35,c_33,c_355,c_1486])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_340,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_32])).

cnf(c_341,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_340])).

cnf(c_343,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_35])).

cnf(c_1186,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_1494,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1186,c_35,c_33,c_341,c_1486])).

cnf(c_1566,plain,
    ( k2_relat_1(sK2) != sK1
    | k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1563,c_1490,c_1494])).

cnf(c_3465,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3355,c_1566])).

cnf(c_3469,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3465])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_571,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_570])).

cnf(c_573,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_571,c_33])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1192,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4249,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1188,c_1192])).

cnf(c_4429,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_573,c_4249])).

cnf(c_2493,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1490,c_1189])).

cnf(c_2498,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2493,c_1494])).

cnf(c_2896,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2498,c_36,c_38,c_1462,c_1465,c_1487])).

cnf(c_3461,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3355,c_2896])).

cnf(c_4436,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_4429,c_3461])).

cnf(c_4598,plain,
    ( v1_xboole_0(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4126,c_38,c_111,c_1694,c_2845,c_3469,c_4429,c_4436])).

cnf(c_1202,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1201,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2807,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1202,c_1201])).

cnf(c_4603,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4598,c_2807])).

cnf(c_4125,plain,
    ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3461,c_1193])).

cnf(c_6815,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4603,c_4125])).

cnf(c_5247,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4429,c_3469])).

cnf(c_5380,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5247,c_3469,c_4429,c_4436])).

cnf(c_5389,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5380,c_3461])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_5454,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5389,c_3])).

cnf(c_6808,plain,
    ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4603,c_5454])).

cnf(c_4128,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3,c_1193])).

cnf(c_7659,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6808,c_4128])).

cnf(c_7680,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7659])).

cnf(c_7904,plain,
    ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6815,c_111,c_7680])).

cnf(c_7909,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7904,c_2807])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_498,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_499,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_1179,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_499])).

cnf(c_1379,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1179,c_3])).

cnf(c_1847,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1379,c_36,c_38,c_1462,c_1487])).

cnf(c_1848,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1847])).

cnf(c_5398,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5380,c_1848])).

cnf(c_5431,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5398])).

cnf(c_5435,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5431,c_3])).

cnf(c_5457,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5454,c_5435])).

cnf(c_7810,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5457,c_4603])).

cnf(c_7931,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7909,c_7810])).

cnf(c_5,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1200,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4246,plain,
    ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_1200,c_1192])).

cnf(c_7954,plain,
    ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_7931,c_4246])).

cnf(c_6820,plain,
    ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_4603,c_1490])).

cnf(c_7938,plain,
    ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_7909,c_6820])).

cnf(c_5396,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5380,c_3355])).

cnf(c_6813,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4603,c_5396])).

cnf(c_7940,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_7938,c_6813])).

cnf(c_7956,plain,
    ( $false ),
    inference(backward_subsumption_resolution,[status(thm)],[c_7954,c_7940])).

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
% 0.13/0.34  % DateTime   : Tue Dec  1 13:27:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.08/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.08/1.01  
% 3.08/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.08/1.01  
% 3.08/1.01  ------  iProver source info
% 3.08/1.01  
% 3.08/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.08/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.08/1.01  git: non_committed_changes: false
% 3.08/1.01  git: last_make_outside_of_git: false
% 3.08/1.01  
% 3.08/1.01  ------ 
% 3.08/1.01  
% 3.08/1.01  ------ Input Options
% 3.08/1.01  
% 3.08/1.01  --out_options                           all
% 3.08/1.01  --tptp_safe_out                         true
% 3.08/1.01  --problem_path                          ""
% 3.08/1.01  --include_path                          ""
% 3.08/1.01  --clausifier                            res/vclausify_rel
% 3.08/1.01  --clausifier_options                    --mode clausify
% 3.08/1.01  --stdin                                 false
% 3.08/1.01  --stats_out                             all
% 3.08/1.01  
% 3.08/1.01  ------ General Options
% 3.08/1.01  
% 3.08/1.01  --fof                                   false
% 3.08/1.01  --time_out_real                         305.
% 3.08/1.01  --time_out_virtual                      -1.
% 3.08/1.01  --symbol_type_check                     false
% 3.08/1.01  --clausify_out                          false
% 3.08/1.01  --sig_cnt_out                           false
% 3.08/1.01  --trig_cnt_out                          false
% 3.08/1.01  --trig_cnt_out_tolerance                1.
% 3.08/1.01  --trig_cnt_out_sk_spl                   false
% 3.08/1.01  --abstr_cl_out                          false
% 3.08/1.01  
% 3.08/1.01  ------ Global Options
% 3.08/1.01  
% 3.08/1.01  --schedule                              default
% 3.08/1.01  --add_important_lit                     false
% 3.08/1.01  --prop_solver_per_cl                    1000
% 3.08/1.01  --min_unsat_core                        false
% 3.08/1.01  --soft_assumptions                      false
% 3.08/1.01  --soft_lemma_size                       3
% 3.08/1.01  --prop_impl_unit_size                   0
% 3.08/1.01  --prop_impl_unit                        []
% 3.08/1.01  --share_sel_clauses                     true
% 3.08/1.01  --reset_solvers                         false
% 3.08/1.01  --bc_imp_inh                            [conj_cone]
% 3.08/1.01  --conj_cone_tolerance                   3.
% 3.08/1.01  --extra_neg_conj                        none
% 3.08/1.01  --large_theory_mode                     true
% 3.08/1.01  --prolific_symb_bound                   200
% 3.08/1.01  --lt_threshold                          2000
% 3.08/1.01  --clause_weak_htbl                      true
% 3.08/1.01  --gc_record_bc_elim                     false
% 3.08/1.01  
% 3.08/1.01  ------ Preprocessing Options
% 3.08/1.01  
% 3.08/1.01  --preprocessing_flag                    true
% 3.08/1.01  --time_out_prep_mult                    0.1
% 3.08/1.01  --splitting_mode                        input
% 3.08/1.01  --splitting_grd                         true
% 3.08/1.01  --splitting_cvd                         false
% 3.08/1.01  --splitting_cvd_svl                     false
% 3.08/1.01  --splitting_nvd                         32
% 3.08/1.01  --sub_typing                            true
% 3.08/1.01  --prep_gs_sim                           true
% 3.08/1.01  --prep_unflatten                        true
% 3.08/1.01  --prep_res_sim                          true
% 3.08/1.01  --prep_upred                            true
% 3.08/1.01  --prep_sem_filter                       exhaustive
% 3.08/1.01  --prep_sem_filter_out                   false
% 3.08/1.01  --pred_elim                             true
% 3.08/1.01  --res_sim_input                         true
% 3.08/1.01  --eq_ax_congr_red                       true
% 3.08/1.01  --pure_diseq_elim                       true
% 3.08/1.01  --brand_transform                       false
% 3.08/1.01  --non_eq_to_eq                          false
% 3.08/1.01  --prep_def_merge                        true
% 3.08/1.01  --prep_def_merge_prop_impl              false
% 3.08/1.01  --prep_def_merge_mbd                    true
% 3.08/1.01  --prep_def_merge_tr_red                 false
% 3.08/1.01  --prep_def_merge_tr_cl                  false
% 3.08/1.01  --smt_preprocessing                     true
% 3.08/1.01  --smt_ac_axioms                         fast
% 3.08/1.01  --preprocessed_out                      false
% 3.08/1.01  --preprocessed_stats                    false
% 3.08/1.01  
% 3.08/1.01  ------ Abstraction refinement Options
% 3.08/1.01  
% 3.08/1.01  --abstr_ref                             []
% 3.08/1.01  --abstr_ref_prep                        false
% 3.08/1.01  --abstr_ref_until_sat                   false
% 3.08/1.01  --abstr_ref_sig_restrict                funpre
% 3.08/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/1.01  --abstr_ref_under                       []
% 3.08/1.01  
% 3.08/1.01  ------ SAT Options
% 3.08/1.01  
% 3.08/1.01  --sat_mode                              false
% 3.08/1.01  --sat_fm_restart_options                ""
% 3.08/1.01  --sat_gr_def                            false
% 3.08/1.01  --sat_epr_types                         true
% 3.08/1.01  --sat_non_cyclic_types                  false
% 3.08/1.01  --sat_finite_models                     false
% 3.08/1.01  --sat_fm_lemmas                         false
% 3.08/1.01  --sat_fm_prep                           false
% 3.08/1.01  --sat_fm_uc_incr                        true
% 3.08/1.01  --sat_out_model                         small
% 3.08/1.01  --sat_out_clauses                       false
% 3.08/1.01  
% 3.08/1.01  ------ QBF Options
% 3.08/1.01  
% 3.08/1.01  --qbf_mode                              false
% 3.08/1.01  --qbf_elim_univ                         false
% 3.08/1.01  --qbf_dom_inst                          none
% 3.08/1.01  --qbf_dom_pre_inst                      false
% 3.08/1.01  --qbf_sk_in                             false
% 3.08/1.01  --qbf_pred_elim                         true
% 3.08/1.01  --qbf_split                             512
% 3.08/1.01  
% 3.08/1.01  ------ BMC1 Options
% 3.08/1.01  
% 3.08/1.01  --bmc1_incremental                      false
% 3.08/1.01  --bmc1_axioms                           reachable_all
% 3.08/1.01  --bmc1_min_bound                        0
% 3.08/1.01  --bmc1_max_bound                        -1
% 3.08/1.01  --bmc1_max_bound_default                -1
% 3.08/1.01  --bmc1_symbol_reachability              true
% 3.08/1.01  --bmc1_property_lemmas                  false
% 3.08/1.01  --bmc1_k_induction                      false
% 3.08/1.01  --bmc1_non_equiv_states                 false
% 3.08/1.01  --bmc1_deadlock                         false
% 3.08/1.01  --bmc1_ucm                              false
% 3.08/1.01  --bmc1_add_unsat_core                   none
% 3.08/1.01  --bmc1_unsat_core_children              false
% 3.08/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/1.01  --bmc1_out_stat                         full
% 3.08/1.01  --bmc1_ground_init                      false
% 3.08/1.01  --bmc1_pre_inst_next_state              false
% 3.08/1.01  --bmc1_pre_inst_state                   false
% 3.08/1.01  --bmc1_pre_inst_reach_state             false
% 3.08/1.01  --bmc1_out_unsat_core                   false
% 3.08/1.01  --bmc1_aig_witness_out                  false
% 3.08/1.01  --bmc1_verbose                          false
% 3.08/1.01  --bmc1_dump_clauses_tptp                false
% 3.08/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.08/1.01  --bmc1_dump_file                        -
% 3.08/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.08/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.08/1.01  --bmc1_ucm_extend_mode                  1
% 3.08/1.01  --bmc1_ucm_init_mode                    2
% 3.08/1.01  --bmc1_ucm_cone_mode                    none
% 3.08/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.08/1.01  --bmc1_ucm_relax_model                  4
% 3.08/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.08/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/1.01  --bmc1_ucm_layered_model                none
% 3.08/1.01  --bmc1_ucm_max_lemma_size               10
% 3.08/1.01  
% 3.08/1.01  ------ AIG Options
% 3.08/1.01  
% 3.08/1.01  --aig_mode                              false
% 3.08/1.01  
% 3.08/1.01  ------ Instantiation Options
% 3.08/1.01  
% 3.08/1.01  --instantiation_flag                    true
% 3.08/1.01  --inst_sos_flag                         false
% 3.08/1.01  --inst_sos_phase                        true
% 3.08/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/1.01  --inst_lit_sel_side                     num_symb
% 3.08/1.01  --inst_solver_per_active                1400
% 3.08/1.01  --inst_solver_calls_frac                1.
% 3.08/1.01  --inst_passive_queue_type               priority_queues
% 3.08/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.08/1.01  --inst_passive_queues_freq              [25;2]
% 3.08/1.01  --inst_dismatching                      true
% 3.08/1.01  --inst_eager_unprocessed_to_passive     true
% 3.08/1.01  --inst_prop_sim_given                   true
% 3.08/1.01  --inst_prop_sim_new                     false
% 3.08/1.01  --inst_subs_new                         false
% 3.08/1.01  --inst_eq_res_simp                      false
% 3.08/1.01  --inst_subs_given                       false
% 3.08/1.01  --inst_orphan_elimination               true
% 3.08/1.01  --inst_learning_loop_flag               true
% 3.08/1.01  --inst_learning_start                   3000
% 3.08/1.01  --inst_learning_factor                  2
% 3.08/1.01  --inst_start_prop_sim_after_learn       3
% 3.08/1.01  --inst_sel_renew                        solver
% 3.08/1.01  --inst_lit_activity_flag                true
% 3.08/1.01  --inst_restr_to_given                   false
% 3.08/1.01  --inst_activity_threshold               500
% 3.08/1.01  --inst_out_proof                        true
% 3.08/1.01  
% 3.08/1.01  ------ Resolution Options
% 3.08/1.01  
% 3.08/1.01  --resolution_flag                       true
% 3.08/1.01  --res_lit_sel                           adaptive
% 3.08/1.01  --res_lit_sel_side                      none
% 3.08/1.01  --res_ordering                          kbo
% 3.08/1.01  --res_to_prop_solver                    active
% 3.08/1.01  --res_prop_simpl_new                    false
% 3.08/1.01  --res_prop_simpl_given                  true
% 3.08/1.01  --res_passive_queue_type                priority_queues
% 3.08/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.08/1.01  --res_passive_queues_freq               [15;5]
% 3.08/1.01  --res_forward_subs                      full
% 3.08/1.01  --res_backward_subs                     full
% 3.08/1.01  --res_forward_subs_resolution           true
% 3.08/1.01  --res_backward_subs_resolution          true
% 3.08/1.01  --res_orphan_elimination                true
% 3.08/1.01  --res_time_limit                        2.
% 3.08/1.01  --res_out_proof                         true
% 3.08/1.01  
% 3.08/1.01  ------ Superposition Options
% 3.08/1.01  
% 3.08/1.01  --superposition_flag                    true
% 3.08/1.01  --sup_passive_queue_type                priority_queues
% 3.08/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.08/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.08/1.01  --demod_completeness_check              fast
% 3.08/1.01  --demod_use_ground                      true
% 3.08/1.01  --sup_to_prop_solver                    passive
% 3.08/1.01  --sup_prop_simpl_new                    true
% 3.08/1.01  --sup_prop_simpl_given                  true
% 3.08/1.01  --sup_fun_splitting                     false
% 3.08/1.01  --sup_smt_interval                      50000
% 3.08/1.01  
% 3.08/1.01  ------ Superposition Simplification Setup
% 3.08/1.01  
% 3.08/1.01  --sup_indices_passive                   []
% 3.08/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.08/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.01  --sup_full_bw                           [BwDemod]
% 3.08/1.01  --sup_immed_triv                        [TrivRules]
% 3.08/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.08/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.01  --sup_immed_bw_main                     []
% 3.08/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.08/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.01  
% 3.08/1.01  ------ Combination Options
% 3.08/1.01  
% 3.08/1.01  --comb_res_mult                         3
% 3.08/1.01  --comb_sup_mult                         2
% 3.08/1.01  --comb_inst_mult                        10
% 3.08/1.01  
% 3.08/1.01  ------ Debug Options
% 3.08/1.01  
% 3.08/1.01  --dbg_backtrace                         false
% 3.08/1.01  --dbg_dump_prop_clauses                 false
% 3.08/1.01  --dbg_dump_prop_clauses_file            -
% 3.08/1.01  --dbg_out_stat                          false
% 3.08/1.01  ------ Parsing...
% 3.08/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.08/1.01  
% 3.08/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e 
% 3.08/1.01  
% 3.08/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.08/1.01  
% 3.08/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.08/1.01  ------ Proving...
% 3.08/1.01  ------ Problem Properties 
% 3.08/1.01  
% 3.08/1.01  
% 3.08/1.01  clauses                                 36
% 3.08/1.01  conjectures                             3
% 3.08/1.01  EPR                                     3
% 3.08/1.01  Horn                                    31
% 3.08/1.01  unary                                   10
% 3.08/1.01  binary                                  9
% 3.08/1.01  lits                                    91
% 3.08/1.01  lits eq                                 41
% 3.08/1.01  fd_pure                                 0
% 3.08/1.01  fd_pseudo                               0
% 3.08/1.01  fd_cond                                 2
% 3.08/1.01  fd_pseudo_cond                          1
% 3.08/1.01  AC symbols                              0
% 3.08/1.01  
% 3.08/1.01  ------ Schedule dynamic 5 is on 
% 3.08/1.01  
% 3.08/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.08/1.01  
% 3.08/1.01  
% 3.08/1.01  ------ 
% 3.08/1.01  Current options:
% 3.08/1.01  ------ 
% 3.08/1.01  
% 3.08/1.01  ------ Input Options
% 3.08/1.01  
% 3.08/1.01  --out_options                           all
% 3.08/1.01  --tptp_safe_out                         true
% 3.08/1.01  --problem_path                          ""
% 3.08/1.01  --include_path                          ""
% 3.08/1.01  --clausifier                            res/vclausify_rel
% 3.08/1.01  --clausifier_options                    --mode clausify
% 3.08/1.01  --stdin                                 false
% 3.08/1.01  --stats_out                             all
% 3.08/1.01  
% 3.08/1.01  ------ General Options
% 3.08/1.01  
% 3.08/1.01  --fof                                   false
% 3.08/1.01  --time_out_real                         305.
% 3.08/1.01  --time_out_virtual                      -1.
% 3.08/1.01  --symbol_type_check                     false
% 3.08/1.01  --clausify_out                          false
% 3.08/1.01  --sig_cnt_out                           false
% 3.08/1.01  --trig_cnt_out                          false
% 3.08/1.01  --trig_cnt_out_tolerance                1.
% 3.08/1.01  --trig_cnt_out_sk_spl                   false
% 3.08/1.01  --abstr_cl_out                          false
% 3.08/1.01  
% 3.08/1.01  ------ Global Options
% 3.08/1.01  
% 3.08/1.01  --schedule                              default
% 3.08/1.01  --add_important_lit                     false
% 3.08/1.01  --prop_solver_per_cl                    1000
% 3.08/1.01  --min_unsat_core                        false
% 3.08/1.01  --soft_assumptions                      false
% 3.08/1.01  --soft_lemma_size                       3
% 3.08/1.01  --prop_impl_unit_size                   0
% 3.08/1.01  --prop_impl_unit                        []
% 3.08/1.01  --share_sel_clauses                     true
% 3.08/1.01  --reset_solvers                         false
% 3.08/1.01  --bc_imp_inh                            [conj_cone]
% 3.08/1.01  --conj_cone_tolerance                   3.
% 3.08/1.01  --extra_neg_conj                        none
% 3.08/1.01  --large_theory_mode                     true
% 3.08/1.01  --prolific_symb_bound                   200
% 3.08/1.01  --lt_threshold                          2000
% 3.08/1.01  --clause_weak_htbl                      true
% 3.08/1.01  --gc_record_bc_elim                     false
% 3.08/1.01  
% 3.08/1.01  ------ Preprocessing Options
% 3.08/1.01  
% 3.08/1.01  --preprocessing_flag                    true
% 3.08/1.01  --time_out_prep_mult                    0.1
% 3.08/1.01  --splitting_mode                        input
% 3.08/1.01  --splitting_grd                         true
% 3.08/1.01  --splitting_cvd                         false
% 3.08/1.01  --splitting_cvd_svl                     false
% 3.08/1.01  --splitting_nvd                         32
% 3.08/1.01  --sub_typing                            true
% 3.08/1.01  --prep_gs_sim                           true
% 3.08/1.01  --prep_unflatten                        true
% 3.08/1.01  --prep_res_sim                          true
% 3.08/1.01  --prep_upred                            true
% 3.08/1.01  --prep_sem_filter                       exhaustive
% 3.08/1.01  --prep_sem_filter_out                   false
% 3.08/1.01  --pred_elim                             true
% 3.08/1.01  --res_sim_input                         true
% 3.08/1.01  --eq_ax_congr_red                       true
% 3.08/1.01  --pure_diseq_elim                       true
% 3.08/1.01  --brand_transform                       false
% 3.08/1.01  --non_eq_to_eq                          false
% 3.08/1.01  --prep_def_merge                        true
% 3.08/1.01  --prep_def_merge_prop_impl              false
% 3.08/1.01  --prep_def_merge_mbd                    true
% 3.08/1.01  --prep_def_merge_tr_red                 false
% 3.08/1.01  --prep_def_merge_tr_cl                  false
% 3.08/1.01  --smt_preprocessing                     true
% 3.08/1.01  --smt_ac_axioms                         fast
% 3.08/1.01  --preprocessed_out                      false
% 3.08/1.01  --preprocessed_stats                    false
% 3.08/1.01  
% 3.08/1.01  ------ Abstraction refinement Options
% 3.08/1.01  
% 3.08/1.01  --abstr_ref                             []
% 3.08/1.01  --abstr_ref_prep                        false
% 3.08/1.01  --abstr_ref_until_sat                   false
% 3.08/1.01  --abstr_ref_sig_restrict                funpre
% 3.08/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.08/1.01  --abstr_ref_under                       []
% 3.08/1.01  
% 3.08/1.01  ------ SAT Options
% 3.08/1.01  
% 3.08/1.01  --sat_mode                              false
% 3.08/1.01  --sat_fm_restart_options                ""
% 3.08/1.01  --sat_gr_def                            false
% 3.08/1.01  --sat_epr_types                         true
% 3.08/1.01  --sat_non_cyclic_types                  false
% 3.08/1.01  --sat_finite_models                     false
% 3.08/1.01  --sat_fm_lemmas                         false
% 3.08/1.01  --sat_fm_prep                           false
% 3.08/1.01  --sat_fm_uc_incr                        true
% 3.08/1.01  --sat_out_model                         small
% 3.08/1.01  --sat_out_clauses                       false
% 3.08/1.01  
% 3.08/1.01  ------ QBF Options
% 3.08/1.01  
% 3.08/1.01  --qbf_mode                              false
% 3.08/1.01  --qbf_elim_univ                         false
% 3.08/1.01  --qbf_dom_inst                          none
% 3.08/1.01  --qbf_dom_pre_inst                      false
% 3.08/1.01  --qbf_sk_in                             false
% 3.08/1.01  --qbf_pred_elim                         true
% 3.08/1.01  --qbf_split                             512
% 3.08/1.01  
% 3.08/1.01  ------ BMC1 Options
% 3.08/1.01  
% 3.08/1.01  --bmc1_incremental                      false
% 3.08/1.01  --bmc1_axioms                           reachable_all
% 3.08/1.01  --bmc1_min_bound                        0
% 3.08/1.01  --bmc1_max_bound                        -1
% 3.08/1.01  --bmc1_max_bound_default                -1
% 3.08/1.01  --bmc1_symbol_reachability              true
% 3.08/1.01  --bmc1_property_lemmas                  false
% 3.08/1.01  --bmc1_k_induction                      false
% 3.08/1.01  --bmc1_non_equiv_states                 false
% 3.08/1.01  --bmc1_deadlock                         false
% 3.08/1.01  --bmc1_ucm                              false
% 3.08/1.01  --bmc1_add_unsat_core                   none
% 3.08/1.01  --bmc1_unsat_core_children              false
% 3.08/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.08/1.01  --bmc1_out_stat                         full
% 3.08/1.01  --bmc1_ground_init                      false
% 3.08/1.01  --bmc1_pre_inst_next_state              false
% 3.08/1.01  --bmc1_pre_inst_state                   false
% 3.08/1.01  --bmc1_pre_inst_reach_state             false
% 3.08/1.01  --bmc1_out_unsat_core                   false
% 3.08/1.01  --bmc1_aig_witness_out                  false
% 3.08/1.01  --bmc1_verbose                          false
% 3.08/1.01  --bmc1_dump_clauses_tptp                false
% 3.08/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.08/1.01  --bmc1_dump_file                        -
% 3.08/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.08/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.08/1.01  --bmc1_ucm_extend_mode                  1
% 3.08/1.01  --bmc1_ucm_init_mode                    2
% 3.08/1.01  --bmc1_ucm_cone_mode                    none
% 3.08/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.08/1.01  --bmc1_ucm_relax_model                  4
% 3.08/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.08/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.08/1.01  --bmc1_ucm_layered_model                none
% 3.08/1.01  --bmc1_ucm_max_lemma_size               10
% 3.08/1.01  
% 3.08/1.01  ------ AIG Options
% 3.08/1.01  
% 3.08/1.01  --aig_mode                              false
% 3.08/1.01  
% 3.08/1.01  ------ Instantiation Options
% 3.08/1.01  
% 3.08/1.01  --instantiation_flag                    true
% 3.08/1.01  --inst_sos_flag                         false
% 3.08/1.01  --inst_sos_phase                        true
% 3.08/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.08/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.08/1.01  --inst_lit_sel_side                     none
% 3.08/1.01  --inst_solver_per_active                1400
% 3.08/1.01  --inst_solver_calls_frac                1.
% 3.08/1.01  --inst_passive_queue_type               priority_queues
% 3.08/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.08/1.01  --inst_passive_queues_freq              [25;2]
% 3.08/1.01  --inst_dismatching                      true
% 3.08/1.01  --inst_eager_unprocessed_to_passive     true
% 3.08/1.01  --inst_prop_sim_given                   true
% 3.08/1.01  --inst_prop_sim_new                     false
% 3.08/1.01  --inst_subs_new                         false
% 3.08/1.01  --inst_eq_res_simp                      false
% 3.08/1.01  --inst_subs_given                       false
% 3.08/1.01  --inst_orphan_elimination               true
% 3.08/1.01  --inst_learning_loop_flag               true
% 3.08/1.01  --inst_learning_start                   3000
% 3.08/1.01  --inst_learning_factor                  2
% 3.08/1.01  --inst_start_prop_sim_after_learn       3
% 3.08/1.01  --inst_sel_renew                        solver
% 3.08/1.01  --inst_lit_activity_flag                true
% 3.08/1.01  --inst_restr_to_given                   false
% 3.08/1.01  --inst_activity_threshold               500
% 3.08/1.01  --inst_out_proof                        true
% 3.08/1.01  
% 3.08/1.01  ------ Resolution Options
% 3.08/1.01  
% 3.08/1.01  --resolution_flag                       false
% 3.08/1.01  --res_lit_sel                           adaptive
% 3.08/1.01  --res_lit_sel_side                      none
% 3.08/1.01  --res_ordering                          kbo
% 3.08/1.01  --res_to_prop_solver                    active
% 3.08/1.01  --res_prop_simpl_new                    false
% 3.08/1.01  --res_prop_simpl_given                  true
% 3.08/1.01  --res_passive_queue_type                priority_queues
% 3.08/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.08/1.01  --res_passive_queues_freq               [15;5]
% 3.08/1.01  --res_forward_subs                      full
% 3.08/1.01  --res_backward_subs                     full
% 3.08/1.01  --res_forward_subs_resolution           true
% 3.08/1.01  --res_backward_subs_resolution          true
% 3.08/1.01  --res_orphan_elimination                true
% 3.08/1.01  --res_time_limit                        2.
% 3.08/1.01  --res_out_proof                         true
% 3.08/1.01  
% 3.08/1.01  ------ Superposition Options
% 3.08/1.01  
% 3.08/1.01  --superposition_flag                    true
% 3.08/1.01  --sup_passive_queue_type                priority_queues
% 3.08/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.08/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.08/1.01  --demod_completeness_check              fast
% 3.08/1.01  --demod_use_ground                      true
% 3.08/1.01  --sup_to_prop_solver                    passive
% 3.08/1.01  --sup_prop_simpl_new                    true
% 3.08/1.01  --sup_prop_simpl_given                  true
% 3.08/1.01  --sup_fun_splitting                     false
% 3.08/1.01  --sup_smt_interval                      50000
% 3.08/1.01  
% 3.08/1.01  ------ Superposition Simplification Setup
% 3.08/1.01  
% 3.08/1.01  --sup_indices_passive                   []
% 3.08/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.08/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.08/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.01  --sup_full_bw                           [BwDemod]
% 3.08/1.01  --sup_immed_triv                        [TrivRules]
% 3.08/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.08/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.01  --sup_immed_bw_main                     []
% 3.08/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.08/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.08/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.08/1.01  
% 3.08/1.01  ------ Combination Options
% 3.08/1.01  
% 3.08/1.01  --comb_res_mult                         3
% 3.08/1.01  --comb_sup_mult                         2
% 3.08/1.01  --comb_inst_mult                        10
% 3.08/1.01  
% 3.08/1.01  ------ Debug Options
% 3.08/1.01  
% 3.08/1.01  --dbg_backtrace                         false
% 3.08/1.01  --dbg_dump_prop_clauses                 false
% 3.08/1.01  --dbg_dump_prop_clauses_file            -
% 3.08/1.01  --dbg_out_stat                          false
% 3.08/1.01  
% 3.08/1.01  
% 3.08/1.01  
% 3.08/1.01  
% 3.08/1.01  ------ Proving...
% 3.08/1.01  
% 3.08/1.01  
% 3.08/1.01  % SZS status Theorem for theBenchmark.p
% 3.08/1.01  
% 3.08/1.01   Resolution empty clause
% 3.08/1.01  
% 3.08/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.08/1.01  
% 3.08/1.01  fof(f21,conjecture,(
% 3.08/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f22,negated_conjecture,(
% 3.08/1.01    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.08/1.01    inference(negated_conjecture,[],[f21])).
% 3.08/1.01  
% 3.08/1.01  fof(f43,plain,(
% 3.08/1.01    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.08/1.01    inference(ennf_transformation,[],[f22])).
% 3.08/1.01  
% 3.08/1.01  fof(f44,plain,(
% 3.08/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.08/1.01    inference(flattening,[],[f43])).
% 3.08/1.01  
% 3.08/1.01  fof(f48,plain,(
% 3.08/1.01    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 3.08/1.01    introduced(choice_axiom,[])).
% 3.08/1.01  
% 3.08/1.01  fof(f49,plain,(
% 3.08/1.01    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 3.08/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f44,f48])).
% 3.08/1.01  
% 3.08/1.01  fof(f83,plain,(
% 3.08/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.08/1.01    inference(cnf_transformation,[],[f49])).
% 3.08/1.01  
% 3.08/1.01  fof(f16,axiom,(
% 3.08/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f38,plain,(
% 3.08/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.01    inference(ennf_transformation,[],[f16])).
% 3.08/1.01  
% 3.08/1.01  fof(f69,plain,(
% 3.08/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.01    inference(cnf_transformation,[],[f38])).
% 3.08/1.01  
% 3.08/1.01  fof(f85,plain,(
% 3.08/1.01    k2_relset_1(sK0,sK1,sK2) = sK1),
% 3.08/1.01    inference(cnf_transformation,[],[f49])).
% 3.08/1.01  
% 3.08/1.01  fof(f20,axiom,(
% 3.08/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f41,plain,(
% 3.08/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.08/1.01    inference(ennf_transformation,[],[f20])).
% 3.08/1.01  
% 3.08/1.01  fof(f42,plain,(
% 3.08/1.01    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.08/1.01    inference(flattening,[],[f41])).
% 3.08/1.01  
% 3.08/1.01  fof(f80,plain,(
% 3.08/1.01    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.08/1.01    inference(cnf_transformation,[],[f42])).
% 3.08/1.01  
% 3.08/1.01  fof(f81,plain,(
% 3.08/1.01    v1_funct_1(sK2)),
% 3.08/1.01    inference(cnf_transformation,[],[f49])).
% 3.08/1.01  
% 3.08/1.01  fof(f13,axiom,(
% 3.08/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f35,plain,(
% 3.08/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.01    inference(ennf_transformation,[],[f13])).
% 3.08/1.01  
% 3.08/1.01  fof(f66,plain,(
% 3.08/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.01    inference(cnf_transformation,[],[f35])).
% 3.08/1.01  
% 3.08/1.01  fof(f14,axiom,(
% 3.08/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f36,plain,(
% 3.08/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.08/1.01    inference(ennf_transformation,[],[f14])).
% 3.08/1.01  
% 3.08/1.01  fof(f67,plain,(
% 3.08/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.08/1.01    inference(cnf_transformation,[],[f36])).
% 3.08/1.01  
% 3.08/1.01  fof(f1,axiom,(
% 3.08/1.01    v1_xboole_0(k1_xboole_0)),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f50,plain,(
% 3.08/1.01    v1_xboole_0(k1_xboole_0)),
% 3.08/1.01    inference(cnf_transformation,[],[f1])).
% 3.08/1.01  
% 3.08/1.01  fof(f79,plain,(
% 3.08/1.01    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.08/1.01    inference(cnf_transformation,[],[f42])).
% 3.08/1.01  
% 3.08/1.01  fof(f86,plain,(
% 3.08/1.01    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 3.08/1.01    inference(cnf_transformation,[],[f49])).
% 3.08/1.01  
% 3.08/1.01  fof(f10,axiom,(
% 3.08/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f29,plain,(
% 3.08/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.08/1.01    inference(ennf_transformation,[],[f10])).
% 3.08/1.01  
% 3.08/1.01  fof(f30,plain,(
% 3.08/1.01    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.08/1.01    inference(flattening,[],[f29])).
% 3.08/1.01  
% 3.08/1.01  fof(f62,plain,(
% 3.08/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.08/1.01    inference(cnf_transformation,[],[f30])).
% 3.08/1.01  
% 3.08/1.01  fof(f61,plain,(
% 3.08/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.08/1.01    inference(cnf_transformation,[],[f30])).
% 3.08/1.01  
% 3.08/1.01  fof(f12,axiom,(
% 3.08/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f33,plain,(
% 3.08/1.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.08/1.01    inference(ennf_transformation,[],[f12])).
% 3.08/1.01  
% 3.08/1.01  fof(f34,plain,(
% 3.08/1.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.08/1.01    inference(flattening,[],[f33])).
% 3.08/1.01  
% 3.08/1.01  fof(f65,plain,(
% 3.08/1.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.08/1.01    inference(cnf_transformation,[],[f34])).
% 3.08/1.01  
% 3.08/1.01  fof(f84,plain,(
% 3.08/1.01    v2_funct_1(sK2)),
% 3.08/1.01    inference(cnf_transformation,[],[f49])).
% 3.08/1.01  
% 3.08/1.01  fof(f64,plain,(
% 3.08/1.01    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.08/1.01    inference(cnf_transformation,[],[f34])).
% 3.08/1.01  
% 3.08/1.01  fof(f17,axiom,(
% 3.08/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f39,plain,(
% 3.08/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.01    inference(ennf_transformation,[],[f17])).
% 3.08/1.01  
% 3.08/1.01  fof(f40,plain,(
% 3.08/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.01    inference(flattening,[],[f39])).
% 3.08/1.01  
% 3.08/1.01  fof(f47,plain,(
% 3.08/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.01    inference(nnf_transformation,[],[f40])).
% 3.08/1.01  
% 3.08/1.01  fof(f70,plain,(
% 3.08/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.01    inference(cnf_transformation,[],[f47])).
% 3.08/1.01  
% 3.08/1.01  fof(f82,plain,(
% 3.08/1.01    v1_funct_2(sK2,sK0,sK1)),
% 3.08/1.01    inference(cnf_transformation,[],[f49])).
% 3.08/1.01  
% 3.08/1.01  fof(f15,axiom,(
% 3.08/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f37,plain,(
% 3.08/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.08/1.01    inference(ennf_transformation,[],[f15])).
% 3.08/1.01  
% 3.08/1.01  fof(f68,plain,(
% 3.08/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.01    inference(cnf_transformation,[],[f37])).
% 3.08/1.01  
% 3.08/1.01  fof(f2,axiom,(
% 3.08/1.01    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f25,plain,(
% 3.08/1.01    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.08/1.01    inference(ennf_transformation,[],[f2])).
% 3.08/1.01  
% 3.08/1.01  fof(f51,plain,(
% 3.08/1.01    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.08/1.01    inference(cnf_transformation,[],[f25])).
% 3.08/1.01  
% 3.08/1.01  fof(f3,axiom,(
% 3.08/1.01    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f45,plain,(
% 3.08/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.08/1.01    inference(nnf_transformation,[],[f3])).
% 3.08/1.01  
% 3.08/1.01  fof(f46,plain,(
% 3.08/1.01    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.08/1.01    inference(flattening,[],[f45])).
% 3.08/1.01  
% 3.08/1.01  fof(f53,plain,(
% 3.08/1.01    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.08/1.01    inference(cnf_transformation,[],[f46])).
% 3.08/1.01  
% 3.08/1.01  fof(f90,plain,(
% 3.08/1.01    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.08/1.01    inference(equality_resolution,[],[f53])).
% 3.08/1.01  
% 3.08/1.01  fof(f73,plain,(
% 3.08/1.01    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.08/1.01    inference(cnf_transformation,[],[f47])).
% 3.08/1.01  
% 3.08/1.01  fof(f94,plain,(
% 3.08/1.01    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.08/1.01    inference(equality_resolution,[],[f73])).
% 3.08/1.01  
% 3.08/1.01  fof(f4,axiom,(
% 3.08/1.01    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.08/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.08/1.01  
% 3.08/1.01  fof(f55,plain,(
% 3.08/1.01    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.08/1.01    inference(cnf_transformation,[],[f4])).
% 3.08/1.01  
% 3.08/1.01  cnf(c_33,negated_conjecture,
% 3.08/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.08/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1188,plain,
% 3.08/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_19,plain,
% 3.08/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.08/1.01      inference(cnf_transformation,[],[f69]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1191,plain,
% 3.08/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.08/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_3339,plain,
% 3.08/1.01      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_1188,c_1191]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_31,negated_conjecture,
% 3.08/1.01      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 3.08/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_3355,plain,
% 3.08/1.01      ( k2_relat_1(sK2) = sK1 ),
% 3.08/1.01      inference(light_normalisation,[status(thm)],[c_3339,c_31]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_27,plain,
% 3.08/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.08/1.01      | ~ v1_funct_1(X0)
% 3.08/1.01      | ~ v1_relat_1(X0) ),
% 3.08/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1189,plain,
% 3.08/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.08/1.01      | v1_funct_1(X0) != iProver_top
% 3.08/1.01      | v1_relat_1(X0) != iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_3490,plain,
% 3.08/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top
% 3.08/1.01      | v1_funct_1(sK2) != iProver_top
% 3.08/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_3355,c_1189]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_35,negated_conjecture,
% 3.08/1.01      ( v1_funct_1(sK2) ),
% 3.08/1.01      inference(cnf_transformation,[],[f81]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_36,plain,
% 3.08/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_38,plain,
% 3.08/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_16,plain,
% 3.08/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.08/1.01      inference(cnf_transformation,[],[f66]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1486,plain,
% 3.08/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.08/1.01      | v1_relat_1(sK2) ),
% 3.08/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1487,plain,
% 3.08/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.08/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_1486]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_4000,plain,
% 3.08/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) = iProver_top ),
% 3.08/1.01      inference(global_propositional_subsumption,
% 3.08/1.01                [status(thm)],
% 3.08/1.01                [c_3490,c_36,c_38,c_1487]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_17,plain,
% 3.08/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.01      | ~ v1_xboole_0(X2)
% 3.08/1.01      | v1_xboole_0(X0) ),
% 3.08/1.01      inference(cnf_transformation,[],[f67]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1193,plain,
% 3.08/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.08/1.01      | v1_xboole_0(X2) != iProver_top
% 3.08/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_4126,plain,
% 3.08/1.01      ( v1_xboole_0(sK1) != iProver_top | v1_xboole_0(sK2) = iProver_top ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_4000,c_1193]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_0,plain,
% 3.08/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.08/1.01      inference(cnf_transformation,[],[f50]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_111,plain,
% 3.08/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_672,plain,
% 3.08/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.08/1.01      theory(equality) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1691,plain,
% 3.08/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK1) | sK1 != X0 ),
% 3.08/1.01      inference(instantiation,[status(thm)],[c_672]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1692,plain,
% 3.08/1.01      ( sK1 != X0
% 3.08/1.01      | v1_xboole_0(X0) != iProver_top
% 3.08/1.01      | v1_xboole_0(sK1) = iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_1691]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1694,plain,
% 3.08/1.01      ( sK1 != k1_xboole_0
% 3.08/1.01      | v1_xboole_0(sK1) = iProver_top
% 3.08/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.08/1.01      inference(instantiation,[status(thm)],[c_1692]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1912,plain,
% 3.08/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.08/1.01      | ~ v1_xboole_0(X1)
% 3.08/1.01      | v1_xboole_0(sK2) ),
% 3.08/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_2844,plain,
% 3.08/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.08/1.01      | ~ v1_xboole_0(sK1)
% 3.08/1.01      | v1_xboole_0(sK2) ),
% 3.08/1.01      inference(instantiation,[status(thm)],[c_1912]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_2845,plain,
% 3.08/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.08/1.01      | v1_xboole_0(sK1) != iProver_top
% 3.08/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_2844]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_28,plain,
% 3.08/1.01      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.08/1.01      | ~ v1_funct_1(X0)
% 3.08/1.01      | ~ v1_relat_1(X0) ),
% 3.08/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_30,negated_conjecture,
% 3.08/1.01      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 3.08/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.08/1.01      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 3.08/1.01      inference(cnf_transformation,[],[f86]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_581,plain,
% 3.08/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.08/1.01      | ~ v1_funct_1(X0)
% 3.08/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.08/1.01      | ~ v1_relat_1(X0)
% 3.08/1.01      | k2_funct_1(sK2) != X0
% 3.08/1.01      | k2_relat_1(X0) != sK0
% 3.08/1.01      | k1_relat_1(X0) != sK1 ),
% 3.08/1.01      inference(resolution_lifted,[status(thm)],[c_28,c_30]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_582,plain,
% 3.08/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.08/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.08/1.01      | ~ v1_relat_1(k2_funct_1(sK2))
% 3.08/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.08/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.08/1.01      inference(unflattening,[status(thm)],[c_581]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_594,plain,
% 3.08/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.08/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.08/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.08/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 3.08/1.01      inference(forward_subsumption_resolution,[status(thm)],[c_582,c_16]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1175,plain,
% 3.08/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.08/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.08/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_594]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_583,plain,
% 3.08/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.08/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.08/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.08/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_582]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_11,plain,
% 3.08/1.01      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.08/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1461,plain,
% 3.08/1.01      ( v1_funct_1(k2_funct_1(sK2)) | ~ v1_funct_1(sK2) | ~ v1_relat_1(sK2) ),
% 3.08/1.01      inference(instantiation,[status(thm)],[c_11]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1462,plain,
% 3.08/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.08/1.01      | v1_funct_1(sK2) != iProver_top
% 3.08/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_1461]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_12,plain,
% 3.08/1.01      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.08/1.01      inference(cnf_transformation,[],[f61]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1464,plain,
% 3.08/1.01      ( ~ v1_funct_1(sK2) | v1_relat_1(k2_funct_1(sK2)) | ~ v1_relat_1(sK2) ),
% 3.08/1.01      inference(instantiation,[status(thm)],[c_12]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1465,plain,
% 3.08/1.01      ( v1_funct_1(sK2) != iProver_top
% 3.08/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.08/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_1464]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1562,plain,
% 3.08/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.08/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.08/1.01      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 3.08/1.01      inference(global_propositional_subsumption,
% 3.08/1.01                [status(thm)],
% 3.08/1.01                [c_1175,c_36,c_38,c_583,c_1462,c_1465,c_1487]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1563,plain,
% 3.08/1.01      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 3.08/1.01      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.08/1.01      inference(renaming,[status(thm)],[c_1562]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_14,plain,
% 3.08/1.01      ( ~ v2_funct_1(X0)
% 3.08/1.01      | ~ v1_funct_1(X0)
% 3.08/1.01      | ~ v1_relat_1(X0)
% 3.08/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.08/1.01      inference(cnf_transformation,[],[f65]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_32,negated_conjecture,
% 3.08/1.01      ( v2_funct_1(sK2) ),
% 3.08/1.01      inference(cnf_transformation,[],[f84]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_354,plain,
% 3.08/1.01      ( ~ v1_funct_1(X0)
% 3.08/1.01      | ~ v1_relat_1(X0)
% 3.08/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.08/1.01      | sK2 != X0 ),
% 3.08/1.01      inference(resolution_lifted,[status(thm)],[c_14,c_32]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_355,plain,
% 3.08/1.01      ( ~ v1_funct_1(sK2)
% 3.08/1.01      | ~ v1_relat_1(sK2)
% 3.08/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.08/1.01      inference(unflattening,[status(thm)],[c_354]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_357,plain,
% 3.08/1.01      ( ~ v1_relat_1(sK2) | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.08/1.01      inference(global_propositional_subsumption,[status(thm)],[c_355,c_35]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1185,plain,
% 3.08/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.08/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1490,plain,
% 3.08/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.08/1.01      inference(global_propositional_subsumption,
% 3.08/1.01                [status(thm)],
% 3.08/1.01                [c_1185,c_35,c_33,c_355,c_1486]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_15,plain,
% 3.08/1.01      ( ~ v2_funct_1(X0)
% 3.08/1.01      | ~ v1_funct_1(X0)
% 3.08/1.01      | ~ v1_relat_1(X0)
% 3.08/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.08/1.01      inference(cnf_transformation,[],[f64]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_340,plain,
% 3.08/1.01      ( ~ v1_funct_1(X0)
% 3.08/1.01      | ~ v1_relat_1(X0)
% 3.08/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.08/1.01      | sK2 != X0 ),
% 3.08/1.01      inference(resolution_lifted,[status(thm)],[c_15,c_32]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_341,plain,
% 3.08/1.01      ( ~ v1_funct_1(sK2)
% 3.08/1.01      | ~ v1_relat_1(sK2)
% 3.08/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.08/1.01      inference(unflattening,[status(thm)],[c_340]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_343,plain,
% 3.08/1.01      ( ~ v1_relat_1(sK2) | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.08/1.01      inference(global_propositional_subsumption,[status(thm)],[c_341,c_35]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1186,plain,
% 3.08/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.08/1.01      | v1_relat_1(sK2) != iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1494,plain,
% 3.08/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.08/1.01      inference(global_propositional_subsumption,
% 3.08/1.01                [status(thm)],
% 3.08/1.01                [c_1186,c_35,c_33,c_341,c_1486]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1566,plain,
% 3.08/1.01      ( k2_relat_1(sK2) != sK1
% 3.08/1.01      | k1_relat_1(sK2) != sK0
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.08/1.01      inference(light_normalisation,[status(thm)],[c_1563,c_1490,c_1494]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_3465,plain,
% 3.08/1.01      ( k1_relat_1(sK2) != sK0
% 3.08/1.01      | sK1 != sK1
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_3355,c_1566]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_3469,plain,
% 3.08/1.01      ( k1_relat_1(sK2) != sK0
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.08/1.01      inference(equality_resolution_simp,[status(thm)],[c_3465]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_25,plain,
% 3.08/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.08/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.08/1.01      | k1_xboole_0 = X2 ),
% 3.08/1.01      inference(cnf_transformation,[],[f70]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_34,negated_conjecture,
% 3.08/1.01      ( v1_funct_2(sK2,sK0,sK1) ),
% 3.08/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_570,plain,
% 3.08/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.01      | k1_relset_1(X1,X2,X0) = X1
% 3.08/1.01      | sK0 != X1
% 3.08/1.01      | sK1 != X2
% 3.08/1.01      | sK2 != X0
% 3.08/1.01      | k1_xboole_0 = X2 ),
% 3.08/1.01      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_571,plain,
% 3.08/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.08/1.01      | k1_relset_1(sK0,sK1,sK2) = sK0
% 3.08/1.01      | k1_xboole_0 = sK1 ),
% 3.08/1.01      inference(unflattening,[status(thm)],[c_570]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_573,plain,
% 3.08/1.01      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 3.08/1.01      inference(global_propositional_subsumption,[status(thm)],[c_571,c_33]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_18,plain,
% 3.08/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.08/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.08/1.01      inference(cnf_transformation,[],[f68]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1192,plain,
% 3.08/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.08/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_4249,plain,
% 3.08/1.01      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_1188,c_1192]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_4429,plain,
% 3.08/1.01      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_573,c_4249]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_2493,plain,
% 3.08/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 3.08/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.08/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_1490,c_1189]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_2498,plain,
% 3.08/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 3.08/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.08/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.08/1.01      inference(light_normalisation,[status(thm)],[c_2493,c_1494]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_2896,plain,
% 3.08/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 3.08/1.01      inference(global_propositional_subsumption,
% 3.08/1.01                [status(thm)],
% 3.08/1.01                [c_2498,c_36,c_38,c_1462,c_1465,c_1487]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_3461,plain,
% 3.08/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_3355,c_2896]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_4436,plain,
% 3.08/1.01      ( sK1 = k1_xboole_0
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_4429,c_3461]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_4598,plain,
% 3.08/1.01      ( v1_xboole_0(sK2) = iProver_top ),
% 3.08/1.01      inference(global_propositional_subsumption,
% 3.08/1.01                [status(thm)],
% 3.08/1.01                [c_4126,c_38,c_111,c_1694,c_2845,c_3469,c_4429,c_4436]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1202,plain,
% 3.08/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1,plain,
% 3.08/1.01      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.08/1.01      inference(cnf_transformation,[],[f51]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1201,plain,
% 3.08/1.01      ( X0 = X1
% 3.08/1.01      | v1_xboole_0(X1) != iProver_top
% 3.08/1.01      | v1_xboole_0(X0) != iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_2807,plain,
% 3.08/1.01      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_1202,c_1201]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_4603,plain,
% 3.08/1.01      ( sK2 = k1_xboole_0 ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_4598,c_2807]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_4125,plain,
% 3.08/1.01      ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
% 3.08/1.01      | v1_xboole_0(k1_relat_1(sK2)) != iProver_top ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_3461,c_1193]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_6815,plain,
% 3.08/1.01      ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top
% 3.08/1.01      | v1_xboole_0(k1_relat_1(k1_xboole_0)) != iProver_top ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_4603,c_4125]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_5247,plain,
% 3.08/1.01      ( sK1 = k1_xboole_0
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_4429,c_3469]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_5380,plain,
% 3.08/1.01      ( sK1 = k1_xboole_0 ),
% 3.08/1.01      inference(global_propositional_subsumption,
% 3.08/1.01                [status(thm)],
% 3.08/1.01                [c_5247,c_3469,c_4429,c_4436]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_5389,plain,
% 3.08/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_5380,c_3461]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_3,plain,
% 3.08/1.01      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.08/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_5454,plain,
% 3.08/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_5389,c_3]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_6808,plain,
% 3.08/1.01      ( m1_subset_1(k2_funct_1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_4603,c_5454]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_4128,plain,
% 3.08/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.08/1.01      | v1_xboole_0(X1) != iProver_top
% 3.08/1.01      | v1_xboole_0(X0) = iProver_top ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_3,c_1193]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_7659,plain,
% 3.08/1.01      ( v1_xboole_0(X0) != iProver_top
% 3.08/1.01      | v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_6808,c_4128]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_7680,plain,
% 3.08/1.01      ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top
% 3.08/1.01      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.08/1.01      inference(instantiation,[status(thm)],[c_7659]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_7904,plain,
% 3.08/1.01      ( v1_xboole_0(k2_funct_1(k1_xboole_0)) = iProver_top ),
% 3.08/1.01      inference(global_propositional_subsumption,
% 3.08/1.01                [status(thm)],
% 3.08/1.01                [c_6815,c_111,c_7680]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_7909,plain,
% 3.08/1.01      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_7904,c_2807]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_22,plain,
% 3.08/1.01      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.08/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.08/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.08/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_498,plain,
% 3.08/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.08/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.08/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.08/1.01      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.08/1.01      | k2_funct_1(sK2) != X0
% 3.08/1.01      | sK0 != X1
% 3.08/1.01      | sK1 != k1_xboole_0 ),
% 3.08/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_499,plain,
% 3.08/1.01      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 3.08/1.01      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 3.08/1.01      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.08/1.01      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.08/1.01      | sK1 != k1_xboole_0 ),
% 3.08/1.01      inference(unflattening,[status(thm)],[c_498]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1179,plain,
% 3.08/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.08/1.01      | sK1 != k1_xboole_0
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.08/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_499]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1379,plain,
% 3.08/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.08/1.01      | sK1 != k1_xboole_0
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.08/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_1179,c_3]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1847,plain,
% 3.08/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.08/1.01      | sK1 != k1_xboole_0
% 3.08/1.01      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.08/1.01      inference(global_propositional_subsumption,
% 3.08/1.01                [status(thm)],
% 3.08/1.01                [c_1379,c_36,c_38,c_1462,c_1487]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1848,plain,
% 3.08/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.08/1.01      | sK1 != k1_xboole_0
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.08/1.01      inference(renaming,[status(thm)],[c_1847]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_5398,plain,
% 3.08/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.08/1.01      | k1_xboole_0 != k1_xboole_0
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_5380,c_1848]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_5431,plain,
% 3.08/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.08/1.01      inference(equality_resolution_simp,[status(thm)],[c_5398]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_5435,plain,
% 3.08/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 3.08/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_5431,c_3]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_5457,plain,
% 3.08/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 3.08/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_5454,c_5435]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_7810,plain,
% 3.08/1.01      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.08/1.01      inference(light_normalisation,[status(thm)],[c_5457,c_4603]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_7931,plain,
% 3.08/1.01      ( k1_relset_1(k1_xboole_0,sK0,k1_xboole_0) != k1_xboole_0 ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_7909,c_7810]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_5,plain,
% 3.08/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.08/1.01      inference(cnf_transformation,[],[f55]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_1200,plain,
% 3.08/1.01      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.08/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_4246,plain,
% 3.08/1.01      ( k1_relset_1(X0,X1,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.08/1.01      inference(superposition,[status(thm)],[c_1200,c_1192]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_7954,plain,
% 3.08/1.01      ( k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_7931,c_4246]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_6820,plain,
% 3.08/1.01      ( k2_relat_1(k2_funct_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_4603,c_1490]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_7938,plain,
% 3.08/1.01      ( k2_relat_1(k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_7909,c_6820]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_5396,plain,
% 3.08/1.01      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_5380,c_3355]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_6813,plain,
% 3.08/1.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.08/1.01      inference(demodulation,[status(thm)],[c_4603,c_5396]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_7940,plain,
% 3.08/1.01      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.08/1.01      inference(light_normalisation,[status(thm)],[c_7938,c_6813]) ).
% 3.08/1.01  
% 3.08/1.01  cnf(c_7956,plain,
% 3.08/1.01      ( $false ),
% 3.08/1.01      inference(backward_subsumption_resolution,[status(thm)],[c_7954,c_7940]) ).
% 3.08/1.01  
% 3.08/1.01  
% 3.08/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.08/1.01  
% 3.08/1.01  ------                               Statistics
% 3.08/1.01  
% 3.08/1.01  ------ General
% 3.08/1.01  
% 3.08/1.01  abstr_ref_over_cycles:                  0
% 3.08/1.01  abstr_ref_under_cycles:                 0
% 3.08/1.01  gc_basic_clause_elim:                   0
% 3.08/1.01  forced_gc_time:                         0
% 3.08/1.01  parsing_time:                           0.011
% 3.08/1.01  unif_index_cands_time:                  0.
% 3.08/1.01  unif_index_add_time:                    0.
% 3.08/1.01  orderings_time:                         0.
% 3.08/1.01  out_proof_time:                         0.029
% 3.08/1.01  total_time:                             0.323
% 3.08/1.01  num_of_symbols:                         51
% 3.08/1.01  num_of_terms:                           5763
% 3.08/1.01  
% 3.08/1.01  ------ Preprocessing
% 3.08/1.01  
% 3.08/1.01  num_of_splits:                          0
% 3.08/1.01  num_of_split_atoms:                     0
% 3.08/1.01  num_of_reused_defs:                     0
% 3.08/1.01  num_eq_ax_congr_red:                    5
% 3.08/1.01  num_of_sem_filtered_clauses:            1
% 3.08/1.01  num_of_subtypes:                        0
% 3.08/1.01  monotx_restored_types:                  0
% 3.08/1.01  sat_num_of_epr_types:                   0
% 3.08/1.01  sat_num_of_non_cyclic_types:            0
% 3.08/1.01  sat_guarded_non_collapsed_types:        0
% 3.08/1.01  num_pure_diseq_elim:                    0
% 3.08/1.01  simp_replaced_by:                       0
% 3.08/1.01  res_preprocessed:                       138
% 3.08/1.01  prep_upred:                             0
% 3.08/1.01  prep_unflattend:                        44
% 3.08/1.01  smt_new_axioms:                         0
% 3.08/1.01  pred_elim_cands:                        6
% 3.08/1.01  pred_elim:                              2
% 3.08/1.01  pred_elim_cl:                           -1
% 3.08/1.01  pred_elim_cycles:                       3
% 3.08/1.01  merged_defs:                            0
% 3.08/1.01  merged_defs_ncl:                        0
% 3.08/1.01  bin_hyper_res:                          0
% 3.08/1.01  prep_cycles:                            3
% 3.08/1.01  pred_elim_time:                         0.008
% 3.08/1.01  splitting_time:                         0.
% 3.08/1.01  sem_filter_time:                        0.
% 3.08/1.01  monotx_time:                            0.
% 3.08/1.01  subtype_inf_time:                       0.
% 3.08/1.01  
% 3.08/1.01  ------ Problem properties
% 3.08/1.01  
% 3.08/1.01  clauses:                                36
% 3.08/1.01  conjectures:                            3
% 3.08/1.01  epr:                                    3
% 3.08/1.01  horn:                                   31
% 3.08/1.01  ground:                                 14
% 3.08/1.01  unary:                                  10
% 3.08/1.01  binary:                                 9
% 3.08/1.01  lits:                                   91
% 3.08/1.01  lits_eq:                                41
% 3.08/1.01  fd_pure:                                0
% 3.08/1.01  fd_pseudo:                              0
% 3.08/1.01  fd_cond:                                2
% 3.08/1.01  fd_pseudo_cond:                         1
% 3.08/1.01  ac_symbols:                             0
% 3.08/1.01  
% 3.08/1.01  ------ Propositional Solver
% 3.08/1.01  
% 3.08/1.01  prop_solver_calls:                      24
% 3.08/1.01  prop_fast_solver_calls:                 1053
% 3.08/1.01  smt_solver_calls:                       0
% 3.08/1.01  smt_fast_solver_calls:                  0
% 3.08/1.01  prop_num_of_clauses:                    2899
% 3.08/1.01  prop_preprocess_simplified:             8223
% 3.08/1.01  prop_fo_subsumed:                       32
% 3.08/1.01  prop_solver_time:                       0.
% 3.08/1.01  smt_solver_time:                        0.
% 3.08/1.01  smt_fast_solver_time:                   0.
% 3.08/1.01  prop_fast_solver_time:                  0.
% 3.08/1.01  prop_unsat_core_time:                   0.
% 3.08/1.01  
% 3.08/1.01  ------ QBF
% 3.08/1.01  
% 3.08/1.01  qbf_q_res:                              0
% 3.08/1.01  qbf_num_tautologies:                    0
% 3.08/1.01  qbf_prep_cycles:                        0
% 3.08/1.01  
% 3.08/1.01  ------ BMC1
% 3.08/1.01  
% 3.08/1.01  bmc1_current_bound:                     -1
% 3.08/1.01  bmc1_last_solved_bound:                 -1
% 3.08/1.01  bmc1_unsat_core_size:                   -1
% 3.08/1.01  bmc1_unsat_core_parents_size:           -1
% 3.08/1.01  bmc1_merge_next_fun:                    0
% 3.08/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.08/1.01  
% 3.08/1.01  ------ Instantiation
% 3.08/1.01  
% 3.08/1.01  inst_num_of_clauses:                    1149
% 3.08/1.01  inst_num_in_passive:                    382
% 3.08/1.01  inst_num_in_active:                     533
% 3.08/1.01  inst_num_in_unprocessed:                234
% 3.08/1.01  inst_num_of_loops:                      620
% 3.08/1.01  inst_num_of_learning_restarts:          0
% 3.08/1.01  inst_num_moves_active_passive:          85
% 3.08/1.01  inst_lit_activity:                      0
% 3.08/1.01  inst_lit_activity_moves:                0
% 3.08/1.01  inst_num_tautologies:                   0
% 3.08/1.01  inst_num_prop_implied:                  0
% 3.08/1.01  inst_num_existing_simplified:           0
% 3.08/1.01  inst_num_eq_res_simplified:             0
% 3.08/1.01  inst_num_child_elim:                    0
% 3.08/1.01  inst_num_of_dismatching_blockings:      418
% 3.08/1.01  inst_num_of_non_proper_insts:           1027
% 3.08/1.01  inst_num_of_duplicates:                 0
% 3.08/1.01  inst_inst_num_from_inst_to_res:         0
% 3.08/1.01  inst_dismatching_checking_time:         0.
% 3.08/1.01  
% 3.08/1.01  ------ Resolution
% 3.08/1.01  
% 3.08/1.01  res_num_of_clauses:                     0
% 3.08/1.01  res_num_in_passive:                     0
% 3.08/1.01  res_num_in_active:                      0
% 3.08/1.01  res_num_of_loops:                       141
% 3.08/1.01  res_forward_subset_subsumed:            45
% 3.08/1.01  res_backward_subset_subsumed:           2
% 3.08/1.01  res_forward_subsumed:                   0
% 3.08/1.01  res_backward_subsumed:                  0
% 3.08/1.01  res_forward_subsumption_resolution:     4
% 3.08/1.01  res_backward_subsumption_resolution:    0
% 3.08/1.01  res_clause_to_clause_subsumption:       278
% 3.08/1.01  res_orphan_elimination:                 0
% 3.08/1.01  res_tautology_del:                      88
% 3.08/1.01  res_num_eq_res_simplified:              0
% 3.08/1.01  res_num_sel_changes:                    0
% 3.08/1.01  res_moves_from_active_to_pass:          0
% 3.08/1.01  
% 3.08/1.01  ------ Superposition
% 3.08/1.01  
% 3.08/1.01  sup_time_total:                         0.
% 3.08/1.01  sup_time_generating:                    0.
% 3.08/1.01  sup_time_sim_full:                      0.
% 3.08/1.01  sup_time_sim_immed:                     0.
% 3.08/1.01  
% 3.08/1.01  sup_num_of_clauses:                     88
% 3.08/1.01  sup_num_in_active:                      55
% 3.08/1.01  sup_num_in_passive:                     33
% 3.08/1.01  sup_num_of_loops:                       123
% 3.08/1.01  sup_fw_superposition:                   83
% 3.08/1.01  sup_bw_superposition:                   62
% 3.08/1.01  sup_immediate_simplified:               79
% 3.08/1.01  sup_given_eliminated:                   2
% 3.08/1.01  comparisons_done:                       0
% 3.08/1.01  comparisons_avoided:                    8
% 3.08/1.01  
% 3.08/1.01  ------ Simplifications
% 3.08/1.01  
% 3.08/1.01  
% 3.08/1.01  sim_fw_subset_subsumed:                 20
% 3.08/1.01  sim_bw_subset_subsumed:                 4
% 3.08/1.01  sim_fw_subsumed:                        16
% 3.08/1.01  sim_bw_subsumed:                        2
% 3.08/1.01  sim_fw_subsumption_res:                 1
% 3.08/1.01  sim_bw_subsumption_res:                 3
% 3.08/1.01  sim_tautology_del:                      3
% 3.08/1.01  sim_eq_tautology_del:                   9
% 3.08/1.01  sim_eq_res_simp:                        3
% 3.08/1.01  sim_fw_demodulated:                     27
% 3.08/1.01  sim_bw_demodulated:                     71
% 3.08/1.01  sim_light_normalised:                   46
% 3.08/1.01  sim_joinable_taut:                      0
% 3.08/1.01  sim_joinable_simp:                      0
% 3.08/1.01  sim_ac_normalised:                      0
% 3.08/1.01  sim_smt_subsumption:                    0
% 3.08/1.01  
%------------------------------------------------------------------------------
