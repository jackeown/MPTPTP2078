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
% DateTime   : Thu Dec  3 12:02:53 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 238 expanded)
%              Number of clauses        :   56 (  81 expanded)
%              Number of leaves         :   11 (  47 expanded)
%              Depth                    :   19
%              Number of atoms          :  360 (1183 expanded)
%              Number of equality atoms :  160 ( 391 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   14 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( ( r2_hidden(X2,X0)
            & v2_funct_1(X3) )
         => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
            | k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f39,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
      & k1_xboole_0 != X1
      & r2_hidden(X2,X0)
      & v2_funct_1(X3)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f39])).

fof(f44,plain,
    ( ? [X0,X1,X2,X3] :
        ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2
        & k1_xboole_0 != X1
        & r2_hidden(X2,X0)
        & v2_funct_1(X3)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2
      & k1_xboole_0 != sK1
      & r2_hidden(sK2,sK0)
      & v2_funct_1(sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2
    & k1_xboole_0 != sK1
    & r2_hidden(sK2,sK0)
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44])).

fof(f75,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

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

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f45])).

fof(f73,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f77,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f45])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f45])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k2_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
          & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0
        & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 )
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f76,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f52,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f45])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1087,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1090,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2392,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1087,c_1090])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_470,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_471,plain,
    ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_470])).

cnf(c_1331,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(equality_resolution,[status(thm)],[c_471])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_434,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_30])).

cnf(c_435,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_599,plain,
    ( k1_relset_1(X0,X1,sK3) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK0 != X0
    | sK1 != X1
    | sK3 != sK3
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_435])).

cnf(c_600,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_599])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_601,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_600,c_27])).

cnf(c_602,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(renaming,[status(thm)],[c_601])).

cnf(c_667,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0 ),
    inference(equality_resolution_simp,[status(thm)],[c_602])).

cnf(c_1655,plain,
    ( k1_relat_1(sK3) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_1331,c_667])).

cnf(c_2396,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK0
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2392,c_1655])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_769,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1269,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_769])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_479,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_30])).

cnf(c_480,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(unflattening,[status(thm)],[c_479])).

cnf(c_1272,plain,
    ( v1_relat_1(sK3)
    | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(instantiation,[status(thm)],[c_480])).

cnf(c_1273,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1272])).

cnf(c_2741,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2396,c_33,c_1269,c_1273])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_371,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),X1)) = X1
    | k2_relat_1(X0) != sK0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_28])).

cnf(c_372,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),sK2)) = sK2
    | k2_relat_1(X0) != sK0 ),
    inference(unflattening,[status(thm)],[c_371])).

cnf(c_1085,plain,
    ( k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),sK2)) = sK2
    | k2_relat_1(X0) != sK0
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_372])).

cnf(c_2745,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(k2_funct_1(k2_funct_1(sK3)),sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2741,c_1085])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1088,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1933,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1087,c_1088])).

cnf(c_1306,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2099,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1933,c_32,c_29,c_1269,c_1272,c_1306])).

cnf(c_2760,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2745,c_2099])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1281,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1282,plain,
    ( v2_funct_1(k2_funct_1(sK3)) = iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1281])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1278,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1279,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1278])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1275,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1276,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1275])).

cnf(c_26,negated_conjecture,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2760,c_1282,c_1279,c_1276,c_1273,c_1269,c_26,c_36,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:08:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.10/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.10/1.00  
% 2.10/1.00  ------  iProver source info
% 2.10/1.00  
% 2.10/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.10/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.10/1.00  git: non_committed_changes: false
% 2.10/1.00  git: last_make_outside_of_git: false
% 2.10/1.00  
% 2.10/1.00  ------ 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options
% 2.10/1.00  
% 2.10/1.00  --out_options                           all
% 2.10/1.00  --tptp_safe_out                         true
% 2.10/1.00  --problem_path                          ""
% 2.10/1.00  --include_path                          ""
% 2.10/1.00  --clausifier                            res/vclausify_rel
% 2.10/1.00  --clausifier_options                    --mode clausify
% 2.10/1.00  --stdin                                 false
% 2.10/1.00  --stats_out                             all
% 2.10/1.00  
% 2.10/1.00  ------ General Options
% 2.10/1.00  
% 2.10/1.00  --fof                                   false
% 2.10/1.00  --time_out_real                         305.
% 2.10/1.00  --time_out_virtual                      -1.
% 2.10/1.00  --symbol_type_check                     false
% 2.10/1.00  --clausify_out                          false
% 2.10/1.00  --sig_cnt_out                           false
% 2.10/1.00  --trig_cnt_out                          false
% 2.10/1.00  --trig_cnt_out_tolerance                1.
% 2.10/1.00  --trig_cnt_out_sk_spl                   false
% 2.10/1.00  --abstr_cl_out                          false
% 2.10/1.00  
% 2.10/1.00  ------ Global Options
% 2.10/1.00  
% 2.10/1.00  --schedule                              default
% 2.10/1.00  --add_important_lit                     false
% 2.10/1.00  --prop_solver_per_cl                    1000
% 2.10/1.00  --min_unsat_core                        false
% 2.10/1.00  --soft_assumptions                      false
% 2.10/1.00  --soft_lemma_size                       3
% 2.10/1.00  --prop_impl_unit_size                   0
% 2.10/1.00  --prop_impl_unit                        []
% 2.10/1.00  --share_sel_clauses                     true
% 2.10/1.00  --reset_solvers                         false
% 2.10/1.00  --bc_imp_inh                            [conj_cone]
% 2.10/1.00  --conj_cone_tolerance                   3.
% 2.10/1.00  --extra_neg_conj                        none
% 2.10/1.00  --large_theory_mode                     true
% 2.10/1.00  --prolific_symb_bound                   200
% 2.10/1.00  --lt_threshold                          2000
% 2.10/1.00  --clause_weak_htbl                      true
% 2.10/1.00  --gc_record_bc_elim                     false
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing Options
% 2.10/1.00  
% 2.10/1.00  --preprocessing_flag                    true
% 2.10/1.00  --time_out_prep_mult                    0.1
% 2.10/1.00  --splitting_mode                        input
% 2.10/1.00  --splitting_grd                         true
% 2.10/1.00  --splitting_cvd                         false
% 2.10/1.00  --splitting_cvd_svl                     false
% 2.10/1.00  --splitting_nvd                         32
% 2.10/1.00  --sub_typing                            true
% 2.10/1.00  --prep_gs_sim                           true
% 2.10/1.00  --prep_unflatten                        true
% 2.10/1.00  --prep_res_sim                          true
% 2.10/1.00  --prep_upred                            true
% 2.10/1.00  --prep_sem_filter                       exhaustive
% 2.10/1.00  --prep_sem_filter_out                   false
% 2.10/1.00  --pred_elim                             true
% 2.10/1.00  --res_sim_input                         true
% 2.10/1.00  --eq_ax_congr_red                       true
% 2.10/1.00  --pure_diseq_elim                       true
% 2.10/1.00  --brand_transform                       false
% 2.10/1.00  --non_eq_to_eq                          false
% 2.10/1.00  --prep_def_merge                        true
% 2.10/1.00  --prep_def_merge_prop_impl              false
% 2.10/1.00  --prep_def_merge_mbd                    true
% 2.10/1.00  --prep_def_merge_tr_red                 false
% 2.10/1.00  --prep_def_merge_tr_cl                  false
% 2.10/1.00  --smt_preprocessing                     true
% 2.10/1.00  --smt_ac_axioms                         fast
% 2.10/1.00  --preprocessed_out                      false
% 2.10/1.00  --preprocessed_stats                    false
% 2.10/1.00  
% 2.10/1.00  ------ Abstraction refinement Options
% 2.10/1.00  
% 2.10/1.00  --abstr_ref                             []
% 2.10/1.00  --abstr_ref_prep                        false
% 2.10/1.00  --abstr_ref_until_sat                   false
% 2.10/1.00  --abstr_ref_sig_restrict                funpre
% 2.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.00  --abstr_ref_under                       []
% 2.10/1.00  
% 2.10/1.00  ------ SAT Options
% 2.10/1.00  
% 2.10/1.00  --sat_mode                              false
% 2.10/1.00  --sat_fm_restart_options                ""
% 2.10/1.00  --sat_gr_def                            false
% 2.10/1.00  --sat_epr_types                         true
% 2.10/1.00  --sat_non_cyclic_types                  false
% 2.10/1.00  --sat_finite_models                     false
% 2.10/1.00  --sat_fm_lemmas                         false
% 2.10/1.00  --sat_fm_prep                           false
% 2.10/1.00  --sat_fm_uc_incr                        true
% 2.10/1.00  --sat_out_model                         small
% 2.10/1.00  --sat_out_clauses                       false
% 2.10/1.00  
% 2.10/1.00  ------ QBF Options
% 2.10/1.00  
% 2.10/1.00  --qbf_mode                              false
% 2.10/1.00  --qbf_elim_univ                         false
% 2.10/1.00  --qbf_dom_inst                          none
% 2.10/1.00  --qbf_dom_pre_inst                      false
% 2.10/1.00  --qbf_sk_in                             false
% 2.10/1.00  --qbf_pred_elim                         true
% 2.10/1.00  --qbf_split                             512
% 2.10/1.00  
% 2.10/1.00  ------ BMC1 Options
% 2.10/1.00  
% 2.10/1.00  --bmc1_incremental                      false
% 2.10/1.00  --bmc1_axioms                           reachable_all
% 2.10/1.00  --bmc1_min_bound                        0
% 2.10/1.00  --bmc1_max_bound                        -1
% 2.10/1.00  --bmc1_max_bound_default                -1
% 2.10/1.00  --bmc1_symbol_reachability              true
% 2.10/1.00  --bmc1_property_lemmas                  false
% 2.10/1.00  --bmc1_k_induction                      false
% 2.10/1.00  --bmc1_non_equiv_states                 false
% 2.10/1.00  --bmc1_deadlock                         false
% 2.10/1.00  --bmc1_ucm                              false
% 2.10/1.00  --bmc1_add_unsat_core                   none
% 2.10/1.00  --bmc1_unsat_core_children              false
% 2.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.00  --bmc1_out_stat                         full
% 2.10/1.00  --bmc1_ground_init                      false
% 2.10/1.00  --bmc1_pre_inst_next_state              false
% 2.10/1.00  --bmc1_pre_inst_state                   false
% 2.10/1.00  --bmc1_pre_inst_reach_state             false
% 2.10/1.00  --bmc1_out_unsat_core                   false
% 2.10/1.00  --bmc1_aig_witness_out                  false
% 2.10/1.00  --bmc1_verbose                          false
% 2.10/1.00  --bmc1_dump_clauses_tptp                false
% 2.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.00  --bmc1_dump_file                        -
% 2.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.00  --bmc1_ucm_extend_mode                  1
% 2.10/1.00  --bmc1_ucm_init_mode                    2
% 2.10/1.00  --bmc1_ucm_cone_mode                    none
% 2.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.00  --bmc1_ucm_relax_model                  4
% 2.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.00  --bmc1_ucm_layered_model                none
% 2.10/1.00  --bmc1_ucm_max_lemma_size               10
% 2.10/1.00  
% 2.10/1.00  ------ AIG Options
% 2.10/1.00  
% 2.10/1.00  --aig_mode                              false
% 2.10/1.00  
% 2.10/1.00  ------ Instantiation Options
% 2.10/1.00  
% 2.10/1.00  --instantiation_flag                    true
% 2.10/1.00  --inst_sos_flag                         false
% 2.10/1.00  --inst_sos_phase                        true
% 2.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel_side                     num_symb
% 2.10/1.00  --inst_solver_per_active                1400
% 2.10/1.00  --inst_solver_calls_frac                1.
% 2.10/1.00  --inst_passive_queue_type               priority_queues
% 2.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.00  --inst_passive_queues_freq              [25;2]
% 2.10/1.00  --inst_dismatching                      true
% 2.10/1.00  --inst_eager_unprocessed_to_passive     true
% 2.10/1.00  --inst_prop_sim_given                   true
% 2.10/1.00  --inst_prop_sim_new                     false
% 2.10/1.00  --inst_subs_new                         false
% 2.10/1.00  --inst_eq_res_simp                      false
% 2.10/1.00  --inst_subs_given                       false
% 2.10/1.00  --inst_orphan_elimination               true
% 2.10/1.00  --inst_learning_loop_flag               true
% 2.10/1.00  --inst_learning_start                   3000
% 2.10/1.00  --inst_learning_factor                  2
% 2.10/1.00  --inst_start_prop_sim_after_learn       3
% 2.10/1.00  --inst_sel_renew                        solver
% 2.10/1.00  --inst_lit_activity_flag                true
% 2.10/1.00  --inst_restr_to_given                   false
% 2.10/1.00  --inst_activity_threshold               500
% 2.10/1.00  --inst_out_proof                        true
% 2.10/1.00  
% 2.10/1.00  ------ Resolution Options
% 2.10/1.00  
% 2.10/1.00  --resolution_flag                       true
% 2.10/1.00  --res_lit_sel                           adaptive
% 2.10/1.00  --res_lit_sel_side                      none
% 2.10/1.00  --res_ordering                          kbo
% 2.10/1.00  --res_to_prop_solver                    active
% 2.10/1.00  --res_prop_simpl_new                    false
% 2.10/1.00  --res_prop_simpl_given                  true
% 2.10/1.00  --res_passive_queue_type                priority_queues
% 2.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.00  --res_passive_queues_freq               [15;5]
% 2.10/1.00  --res_forward_subs                      full
% 2.10/1.00  --res_backward_subs                     full
% 2.10/1.00  --res_forward_subs_resolution           true
% 2.10/1.00  --res_backward_subs_resolution          true
% 2.10/1.00  --res_orphan_elimination                true
% 2.10/1.00  --res_time_limit                        2.
% 2.10/1.00  --res_out_proof                         true
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Options
% 2.10/1.00  
% 2.10/1.00  --superposition_flag                    true
% 2.10/1.00  --sup_passive_queue_type                priority_queues
% 2.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.00  --demod_completeness_check              fast
% 2.10/1.00  --demod_use_ground                      true
% 2.10/1.00  --sup_to_prop_solver                    passive
% 2.10/1.00  --sup_prop_simpl_new                    true
% 2.10/1.00  --sup_prop_simpl_given                  true
% 2.10/1.00  --sup_fun_splitting                     false
% 2.10/1.00  --sup_smt_interval                      50000
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Simplification Setup
% 2.10/1.00  
% 2.10/1.00  --sup_indices_passive                   []
% 2.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_full_bw                           [BwDemod]
% 2.10/1.00  --sup_immed_triv                        [TrivRules]
% 2.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_immed_bw_main                     []
% 2.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  
% 2.10/1.00  ------ Combination Options
% 2.10/1.00  
% 2.10/1.00  --comb_res_mult                         3
% 2.10/1.00  --comb_sup_mult                         2
% 2.10/1.00  --comb_inst_mult                        10
% 2.10/1.00  
% 2.10/1.00  ------ Debug Options
% 2.10/1.00  
% 2.10/1.00  --dbg_backtrace                         false
% 2.10/1.00  --dbg_dump_prop_clauses                 false
% 2.10/1.00  --dbg_dump_prop_clauses_file            -
% 2.10/1.00  --dbg_out_stat                          false
% 2.10/1.00  ------ Parsing...
% 2.10/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.10/1.00  ------ Proving...
% 2.10/1.00  ------ Problem Properties 
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  clauses                                 23
% 2.10/1.00  conjectures                             4
% 2.10/1.00  EPR                                     5
% 2.10/1.00  Horn                                    22
% 2.10/1.00  unary                                   6
% 2.10/1.00  binary                                  5
% 2.10/1.00  lits                                    63
% 2.10/1.00  lits eq                                 26
% 2.10/1.00  fd_pure                                 0
% 2.10/1.00  fd_pseudo                               0
% 2.10/1.00  fd_cond                                 0
% 2.10/1.00  fd_pseudo_cond                          1
% 2.10/1.00  AC symbols                              0
% 2.10/1.00  
% 2.10/1.00  ------ Schedule dynamic 5 is on 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  ------ 
% 2.10/1.00  Current options:
% 2.10/1.00  ------ 
% 2.10/1.00  
% 2.10/1.00  ------ Input Options
% 2.10/1.00  
% 2.10/1.00  --out_options                           all
% 2.10/1.00  --tptp_safe_out                         true
% 2.10/1.00  --problem_path                          ""
% 2.10/1.00  --include_path                          ""
% 2.10/1.00  --clausifier                            res/vclausify_rel
% 2.10/1.00  --clausifier_options                    --mode clausify
% 2.10/1.00  --stdin                                 false
% 2.10/1.00  --stats_out                             all
% 2.10/1.00  
% 2.10/1.00  ------ General Options
% 2.10/1.00  
% 2.10/1.00  --fof                                   false
% 2.10/1.00  --time_out_real                         305.
% 2.10/1.00  --time_out_virtual                      -1.
% 2.10/1.00  --symbol_type_check                     false
% 2.10/1.00  --clausify_out                          false
% 2.10/1.00  --sig_cnt_out                           false
% 2.10/1.00  --trig_cnt_out                          false
% 2.10/1.00  --trig_cnt_out_tolerance                1.
% 2.10/1.00  --trig_cnt_out_sk_spl                   false
% 2.10/1.00  --abstr_cl_out                          false
% 2.10/1.00  
% 2.10/1.00  ------ Global Options
% 2.10/1.00  
% 2.10/1.00  --schedule                              default
% 2.10/1.00  --add_important_lit                     false
% 2.10/1.00  --prop_solver_per_cl                    1000
% 2.10/1.00  --min_unsat_core                        false
% 2.10/1.00  --soft_assumptions                      false
% 2.10/1.00  --soft_lemma_size                       3
% 2.10/1.00  --prop_impl_unit_size                   0
% 2.10/1.00  --prop_impl_unit                        []
% 2.10/1.00  --share_sel_clauses                     true
% 2.10/1.00  --reset_solvers                         false
% 2.10/1.00  --bc_imp_inh                            [conj_cone]
% 2.10/1.00  --conj_cone_tolerance                   3.
% 2.10/1.00  --extra_neg_conj                        none
% 2.10/1.00  --large_theory_mode                     true
% 2.10/1.00  --prolific_symb_bound                   200
% 2.10/1.00  --lt_threshold                          2000
% 2.10/1.00  --clause_weak_htbl                      true
% 2.10/1.00  --gc_record_bc_elim                     false
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing Options
% 2.10/1.00  
% 2.10/1.00  --preprocessing_flag                    true
% 2.10/1.00  --time_out_prep_mult                    0.1
% 2.10/1.00  --splitting_mode                        input
% 2.10/1.00  --splitting_grd                         true
% 2.10/1.00  --splitting_cvd                         false
% 2.10/1.00  --splitting_cvd_svl                     false
% 2.10/1.00  --splitting_nvd                         32
% 2.10/1.00  --sub_typing                            true
% 2.10/1.00  --prep_gs_sim                           true
% 2.10/1.00  --prep_unflatten                        true
% 2.10/1.00  --prep_res_sim                          true
% 2.10/1.00  --prep_upred                            true
% 2.10/1.00  --prep_sem_filter                       exhaustive
% 2.10/1.00  --prep_sem_filter_out                   false
% 2.10/1.00  --pred_elim                             true
% 2.10/1.00  --res_sim_input                         true
% 2.10/1.00  --eq_ax_congr_red                       true
% 2.10/1.00  --pure_diseq_elim                       true
% 2.10/1.00  --brand_transform                       false
% 2.10/1.00  --non_eq_to_eq                          false
% 2.10/1.00  --prep_def_merge                        true
% 2.10/1.00  --prep_def_merge_prop_impl              false
% 2.10/1.00  --prep_def_merge_mbd                    true
% 2.10/1.00  --prep_def_merge_tr_red                 false
% 2.10/1.00  --prep_def_merge_tr_cl                  false
% 2.10/1.00  --smt_preprocessing                     true
% 2.10/1.00  --smt_ac_axioms                         fast
% 2.10/1.00  --preprocessed_out                      false
% 2.10/1.00  --preprocessed_stats                    false
% 2.10/1.00  
% 2.10/1.00  ------ Abstraction refinement Options
% 2.10/1.00  
% 2.10/1.00  --abstr_ref                             []
% 2.10/1.00  --abstr_ref_prep                        false
% 2.10/1.00  --abstr_ref_until_sat                   false
% 2.10/1.00  --abstr_ref_sig_restrict                funpre
% 2.10/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.10/1.00  --abstr_ref_under                       []
% 2.10/1.00  
% 2.10/1.00  ------ SAT Options
% 2.10/1.00  
% 2.10/1.00  --sat_mode                              false
% 2.10/1.00  --sat_fm_restart_options                ""
% 2.10/1.00  --sat_gr_def                            false
% 2.10/1.00  --sat_epr_types                         true
% 2.10/1.00  --sat_non_cyclic_types                  false
% 2.10/1.00  --sat_finite_models                     false
% 2.10/1.00  --sat_fm_lemmas                         false
% 2.10/1.00  --sat_fm_prep                           false
% 2.10/1.00  --sat_fm_uc_incr                        true
% 2.10/1.00  --sat_out_model                         small
% 2.10/1.00  --sat_out_clauses                       false
% 2.10/1.00  
% 2.10/1.00  ------ QBF Options
% 2.10/1.00  
% 2.10/1.00  --qbf_mode                              false
% 2.10/1.00  --qbf_elim_univ                         false
% 2.10/1.00  --qbf_dom_inst                          none
% 2.10/1.00  --qbf_dom_pre_inst                      false
% 2.10/1.00  --qbf_sk_in                             false
% 2.10/1.00  --qbf_pred_elim                         true
% 2.10/1.00  --qbf_split                             512
% 2.10/1.00  
% 2.10/1.00  ------ BMC1 Options
% 2.10/1.00  
% 2.10/1.00  --bmc1_incremental                      false
% 2.10/1.00  --bmc1_axioms                           reachable_all
% 2.10/1.00  --bmc1_min_bound                        0
% 2.10/1.00  --bmc1_max_bound                        -1
% 2.10/1.00  --bmc1_max_bound_default                -1
% 2.10/1.00  --bmc1_symbol_reachability              true
% 2.10/1.00  --bmc1_property_lemmas                  false
% 2.10/1.00  --bmc1_k_induction                      false
% 2.10/1.00  --bmc1_non_equiv_states                 false
% 2.10/1.00  --bmc1_deadlock                         false
% 2.10/1.00  --bmc1_ucm                              false
% 2.10/1.00  --bmc1_add_unsat_core                   none
% 2.10/1.00  --bmc1_unsat_core_children              false
% 2.10/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.10/1.00  --bmc1_out_stat                         full
% 2.10/1.00  --bmc1_ground_init                      false
% 2.10/1.00  --bmc1_pre_inst_next_state              false
% 2.10/1.00  --bmc1_pre_inst_state                   false
% 2.10/1.00  --bmc1_pre_inst_reach_state             false
% 2.10/1.00  --bmc1_out_unsat_core                   false
% 2.10/1.00  --bmc1_aig_witness_out                  false
% 2.10/1.00  --bmc1_verbose                          false
% 2.10/1.00  --bmc1_dump_clauses_tptp                false
% 2.10/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.10/1.00  --bmc1_dump_file                        -
% 2.10/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.10/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.10/1.00  --bmc1_ucm_extend_mode                  1
% 2.10/1.00  --bmc1_ucm_init_mode                    2
% 2.10/1.00  --bmc1_ucm_cone_mode                    none
% 2.10/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.10/1.00  --bmc1_ucm_relax_model                  4
% 2.10/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.10/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.10/1.00  --bmc1_ucm_layered_model                none
% 2.10/1.00  --bmc1_ucm_max_lemma_size               10
% 2.10/1.00  
% 2.10/1.00  ------ AIG Options
% 2.10/1.00  
% 2.10/1.00  --aig_mode                              false
% 2.10/1.00  
% 2.10/1.00  ------ Instantiation Options
% 2.10/1.00  
% 2.10/1.00  --instantiation_flag                    true
% 2.10/1.00  --inst_sos_flag                         false
% 2.10/1.00  --inst_sos_phase                        true
% 2.10/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.10/1.00  --inst_lit_sel_side                     none
% 2.10/1.00  --inst_solver_per_active                1400
% 2.10/1.00  --inst_solver_calls_frac                1.
% 2.10/1.00  --inst_passive_queue_type               priority_queues
% 2.10/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.10/1.00  --inst_passive_queues_freq              [25;2]
% 2.10/1.00  --inst_dismatching                      true
% 2.10/1.00  --inst_eager_unprocessed_to_passive     true
% 2.10/1.00  --inst_prop_sim_given                   true
% 2.10/1.00  --inst_prop_sim_new                     false
% 2.10/1.00  --inst_subs_new                         false
% 2.10/1.00  --inst_eq_res_simp                      false
% 2.10/1.00  --inst_subs_given                       false
% 2.10/1.00  --inst_orphan_elimination               true
% 2.10/1.00  --inst_learning_loop_flag               true
% 2.10/1.00  --inst_learning_start                   3000
% 2.10/1.00  --inst_learning_factor                  2
% 2.10/1.00  --inst_start_prop_sim_after_learn       3
% 2.10/1.00  --inst_sel_renew                        solver
% 2.10/1.00  --inst_lit_activity_flag                true
% 2.10/1.00  --inst_restr_to_given                   false
% 2.10/1.00  --inst_activity_threshold               500
% 2.10/1.00  --inst_out_proof                        true
% 2.10/1.00  
% 2.10/1.00  ------ Resolution Options
% 2.10/1.00  
% 2.10/1.00  --resolution_flag                       false
% 2.10/1.00  --res_lit_sel                           adaptive
% 2.10/1.00  --res_lit_sel_side                      none
% 2.10/1.00  --res_ordering                          kbo
% 2.10/1.00  --res_to_prop_solver                    active
% 2.10/1.00  --res_prop_simpl_new                    false
% 2.10/1.00  --res_prop_simpl_given                  true
% 2.10/1.00  --res_passive_queue_type                priority_queues
% 2.10/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.10/1.00  --res_passive_queues_freq               [15;5]
% 2.10/1.00  --res_forward_subs                      full
% 2.10/1.00  --res_backward_subs                     full
% 2.10/1.00  --res_forward_subs_resolution           true
% 2.10/1.00  --res_backward_subs_resolution          true
% 2.10/1.00  --res_orphan_elimination                true
% 2.10/1.00  --res_time_limit                        2.
% 2.10/1.00  --res_out_proof                         true
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Options
% 2.10/1.00  
% 2.10/1.00  --superposition_flag                    true
% 2.10/1.00  --sup_passive_queue_type                priority_queues
% 2.10/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.10/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.10/1.00  --demod_completeness_check              fast
% 2.10/1.00  --demod_use_ground                      true
% 2.10/1.00  --sup_to_prop_solver                    passive
% 2.10/1.00  --sup_prop_simpl_new                    true
% 2.10/1.00  --sup_prop_simpl_given                  true
% 2.10/1.00  --sup_fun_splitting                     false
% 2.10/1.00  --sup_smt_interval                      50000
% 2.10/1.00  
% 2.10/1.00  ------ Superposition Simplification Setup
% 2.10/1.00  
% 2.10/1.00  --sup_indices_passive                   []
% 2.10/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.10/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.10/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_full_bw                           [BwDemod]
% 2.10/1.00  --sup_immed_triv                        [TrivRules]
% 2.10/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.10/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_immed_bw_main                     []
% 2.10/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.10/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.10/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.10/1.00  
% 2.10/1.00  ------ Combination Options
% 2.10/1.00  
% 2.10/1.00  --comb_res_mult                         3
% 2.10/1.00  --comb_sup_mult                         2
% 2.10/1.00  --comb_inst_mult                        10
% 2.10/1.00  
% 2.10/1.00  ------ Debug Options
% 2.10/1.00  
% 2.10/1.00  --dbg_backtrace                         false
% 2.10/1.00  --dbg_dump_prop_clauses                 false
% 2.10/1.00  --dbg_dump_prop_clauses_file            -
% 2.10/1.00  --dbg_out_stat                          false
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  ------ Proving...
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  % SZS status Theorem for theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  fof(f15,conjecture,(
% 2.10/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f16,negated_conjecture,(
% 2.10/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 2.10/1.00    inference(negated_conjecture,[],[f15])).
% 2.10/1.00  
% 2.10/1.00  fof(f39,plain,(
% 2.10/1.00    ? [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1) & (r2_hidden(X2,X0) & v2_funct_1(X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.10/1.00    inference(ennf_transformation,[],[f16])).
% 2.10/1.00  
% 2.10/1.00  fof(f40,plain,(
% 2.10/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v2_funct_1(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.10/1.00    inference(flattening,[],[f39])).
% 2.10/1.00  
% 2.10/1.00  fof(f44,plain,(
% 2.10/1.00    ? [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) != X2 & k1_xboole_0 != X1 & r2_hidden(X2,X0) & v2_funct_1(X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.10/1.00    introduced(choice_axiom,[])).
% 2.10/1.00  
% 2.10/1.00  fof(f45,plain,(
% 2.10/1.00    k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 & k1_xboole_0 != sK1 & r2_hidden(sK2,sK0) & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.10/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f40,f44])).
% 2.10/1.00  
% 2.10/1.00  fof(f75,plain,(
% 2.10/1.00    v2_funct_1(sK3)),
% 2.10/1.00    inference(cnf_transformation,[],[f45])).
% 2.10/1.00  
% 2.10/1.00  fof(f8,axiom,(
% 2.10/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f28,plain,(
% 2.10/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.10/1.00    inference(ennf_transformation,[],[f8])).
% 2.10/1.00  
% 2.10/1.00  fof(f29,plain,(
% 2.10/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.10/1.00    inference(flattening,[],[f28])).
% 2.10/1.00  
% 2.10/1.00  fof(f59,plain,(
% 2.10/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f29])).
% 2.10/1.00  
% 2.10/1.00  fof(f13,axiom,(
% 2.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f36,plain,(
% 2.10/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.00    inference(ennf_transformation,[],[f13])).
% 2.10/1.00  
% 2.10/1.00  fof(f65,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f36])).
% 2.10/1.00  
% 2.10/1.00  fof(f74,plain,(
% 2.10/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.10/1.00    inference(cnf_transformation,[],[f45])).
% 2.10/1.00  
% 2.10/1.00  fof(f73,plain,(
% 2.10/1.00    v1_funct_2(sK3,sK0,sK1)),
% 2.10/1.00    inference(cnf_transformation,[],[f45])).
% 2.10/1.00  
% 2.10/1.00  fof(f14,axiom,(
% 2.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f37,plain,(
% 2.10/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.00    inference(ennf_transformation,[],[f14])).
% 2.10/1.00  
% 2.10/1.00  fof(f38,plain,(
% 2.10/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.00    inference(flattening,[],[f37])).
% 2.10/1.00  
% 2.10/1.00  fof(f43,plain,(
% 2.10/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.00    inference(nnf_transformation,[],[f38])).
% 2.10/1.00  
% 2.10/1.00  fof(f66,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f43])).
% 2.10/1.00  
% 2.10/1.00  fof(f77,plain,(
% 2.10/1.00    k1_xboole_0 != sK1),
% 2.10/1.00    inference(cnf_transformation,[],[f45])).
% 2.10/1.00  
% 2.10/1.00  fof(f72,plain,(
% 2.10/1.00    v1_funct_1(sK3)),
% 2.10/1.00    inference(cnf_transformation,[],[f45])).
% 2.10/1.00  
% 2.10/1.00  fof(f11,axiom,(
% 2.10/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f34,plain,(
% 2.10/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.10/1.00    inference(ennf_transformation,[],[f11])).
% 2.10/1.00  
% 2.10/1.00  fof(f63,plain,(
% 2.10/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.10/1.00    inference(cnf_transformation,[],[f34])).
% 2.10/1.00  
% 2.10/1.00  fof(f9,axiom,(
% 2.10/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k2_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0)))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f30,plain,(
% 2.10/1.00    ! [X0,X1] : (((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | (~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.10/1.00    inference(ennf_transformation,[],[f9])).
% 2.10/1.00  
% 2.10/1.00  fof(f31,plain,(
% 2.10/1.00    ! [X0,X1] : ((k1_funct_1(k5_relat_1(k2_funct_1(X1),X1),X0) = X0 & k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.10/1.00    inference(flattening,[],[f30])).
% 2.10/1.00  
% 2.10/1.00  fof(f60,plain,(
% 2.10/1.00    ( ! [X0,X1] : (k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 | ~r2_hidden(X0,k2_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f31])).
% 2.10/1.00  
% 2.10/1.00  fof(f76,plain,(
% 2.10/1.00    r2_hidden(sK2,sK0)),
% 2.10/1.00    inference(cnf_transformation,[],[f45])).
% 2.10/1.00  
% 2.10/1.00  fof(f10,axiom,(
% 2.10/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f32,plain,(
% 2.10/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.10/1.00    inference(ennf_transformation,[],[f10])).
% 2.10/1.00  
% 2.10/1.00  fof(f33,plain,(
% 2.10/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.10/1.00    inference(flattening,[],[f32])).
% 2.10/1.00  
% 2.10/1.00  fof(f62,plain,(
% 2.10/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f33])).
% 2.10/1.00  
% 2.10/1.00  fof(f6,axiom,(
% 2.10/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f24,plain,(
% 2.10/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.10/1.00    inference(ennf_transformation,[],[f6])).
% 2.10/1.00  
% 2.10/1.00  fof(f25,plain,(
% 2.10/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.10/1.00    inference(flattening,[],[f24])).
% 2.10/1.00  
% 2.10/1.00  fof(f56,plain,(
% 2.10/1.00    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f25])).
% 2.10/1.00  
% 2.10/1.00  fof(f5,axiom,(
% 2.10/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.10/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.10/1.00  
% 2.10/1.00  fof(f22,plain,(
% 2.10/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.10/1.00    inference(ennf_transformation,[],[f5])).
% 2.10/1.00  
% 2.10/1.00  fof(f23,plain,(
% 2.10/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.10/1.00    inference(flattening,[],[f22])).
% 2.10/1.00  
% 2.10/1.00  fof(f52,plain,(
% 2.10/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f23])).
% 2.10/1.00  
% 2.10/1.00  fof(f53,plain,(
% 2.10/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.10/1.00    inference(cnf_transformation,[],[f23])).
% 2.10/1.00  
% 2.10/1.00  fof(f78,plain,(
% 2.10/1.00    k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2),
% 2.10/1.00    inference(cnf_transformation,[],[f45])).
% 2.10/1.00  
% 2.10/1.00  cnf(c_29,negated_conjecture,
% 2.10/1.00      ( v2_funct_1(sK3) ),
% 2.10/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1087,plain,
% 2.10/1.00      ( v2_funct_1(sK3) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_12,plain,
% 2.10/1.00      ( ~ v2_funct_1(X0)
% 2.10/1.00      | ~ v1_funct_1(X0)
% 2.10/1.00      | ~ v1_relat_1(X0)
% 2.10/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1090,plain,
% 2.10/1.00      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.10/1.00      | v2_funct_1(X0) != iProver_top
% 2.10/1.00      | v1_funct_1(X0) != iProver_top
% 2.10/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2392,plain,
% 2.10/1.00      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 2.10/1.00      | v1_funct_1(sK3) != iProver_top
% 2.10/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_1087,c_1090]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_19,plain,
% 2.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_30,negated_conjecture,
% 2.10/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.10/1.00      inference(cnf_transformation,[],[f74]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_470,plain,
% 2.10/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.10/1.00      | sK3 != X2 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_471,plain,
% 2.10/1.00      ( k1_relset_1(X0,X1,sK3) = k1_relat_1(sK3)
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_470]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1331,plain,
% 2.10/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.10/1.00      inference(equality_resolution,[status(thm)],[c_471]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_31,negated_conjecture,
% 2.10/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.10/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_25,plain,
% 2.10/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.10/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.10/1.00      | k1_xboole_0 = X2 ),
% 2.10/1.00      inference(cnf_transformation,[],[f66]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_434,plain,
% 2.10/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.10/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.10/1.00      | sK3 != X0
% 2.10/1.00      | k1_xboole_0 = X2 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_30]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_435,plain,
% 2.10/1.00      ( ~ v1_funct_2(sK3,X0,X1)
% 2.10/1.00      | k1_relset_1(X0,X1,sK3) = X0
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.10/1.00      | k1_xboole_0 = X1 ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_434]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_599,plain,
% 2.10/1.00      ( k1_relset_1(X0,X1,sK3) = X0
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.10/1.00      | sK0 != X0
% 2.10/1.00      | sK1 != X1
% 2.10/1.00      | sK3 != sK3
% 2.10/1.00      | k1_xboole_0 = X1 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_31,c_435]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_600,plain,
% 2.10/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.10/1.00      | k1_xboole_0 = sK1 ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_599]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_27,negated_conjecture,
% 2.10/1.00      ( k1_xboole_0 != sK1 ),
% 2.10/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_601,plain,
% 2.10/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.10/1.00      | k1_relset_1(sK0,sK1,sK3) = sK0 ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_600,c_27]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_602,plain,
% 2.10/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.10/1.00      inference(renaming,[status(thm)],[c_601]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_667,plain,
% 2.10/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 ),
% 2.10/1.00      inference(equality_resolution_simp,[status(thm)],[c_602]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1655,plain,
% 2.10/1.00      ( k1_relat_1(sK3) = sK0 ),
% 2.10/1.00      inference(light_normalisation,[status(thm)],[c_1331,c_667]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2396,plain,
% 2.10/1.00      ( k2_relat_1(k2_funct_1(sK3)) = sK0
% 2.10/1.00      | v1_funct_1(sK3) != iProver_top
% 2.10/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.10/1.00      inference(light_normalisation,[status(thm)],[c_2392,c_1655]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_32,negated_conjecture,
% 2.10/1.00      ( v1_funct_1(sK3) ),
% 2.10/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_33,plain,
% 2.10/1.00      ( v1_funct_1(sK3) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_769,plain,( X0 = X0 ),theory(equality) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1269,plain,
% 2.10/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) = k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_769]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_17,plain,
% 2.10/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.10/1.00      | v1_relat_1(X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_479,plain,
% 2.10/1.00      ( v1_relat_1(X0)
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.10/1.00      | sK3 != X0 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_30]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_480,plain,
% 2.10/1.00      ( v1_relat_1(sK3)
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_479]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1272,plain,
% 2.10/1.00      ( v1_relat_1(sK3)
% 2.10/1.00      | k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_480]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1273,plain,
% 2.10/1.00      ( k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)) != k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))
% 2.10/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1272]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2741,plain,
% 2.10/1.00      ( k2_relat_1(k2_funct_1(sK3)) = sK0 ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_2396,c_33,c_1269,c_1273]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_15,plain,
% 2.10/1.00      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.10/1.00      | ~ v2_funct_1(X1)
% 2.10/1.00      | ~ v1_funct_1(X1)
% 2.10/1.00      | ~ v1_relat_1(X1)
% 2.10/1.00      | k1_funct_1(X1,k1_funct_1(k2_funct_1(X1),X0)) = X0 ),
% 2.10/1.00      inference(cnf_transformation,[],[f60]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_28,negated_conjecture,
% 2.10/1.00      ( r2_hidden(sK2,sK0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_371,plain,
% 2.10/1.00      ( ~ v2_funct_1(X0)
% 2.10/1.00      | ~ v1_funct_1(X0)
% 2.10/1.00      | ~ v1_relat_1(X0)
% 2.10/1.00      | k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),X1)) = X1
% 2.10/1.00      | k2_relat_1(X0) != sK0
% 2.10/1.00      | sK2 != X1 ),
% 2.10/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_28]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_372,plain,
% 2.10/1.00      ( ~ v2_funct_1(X0)
% 2.10/1.00      | ~ v1_funct_1(X0)
% 2.10/1.00      | ~ v1_relat_1(X0)
% 2.10/1.00      | k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),sK2)) = sK2
% 2.10/1.00      | k2_relat_1(X0) != sK0 ),
% 2.10/1.00      inference(unflattening,[status(thm)],[c_371]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1085,plain,
% 2.10/1.00      ( k1_funct_1(X0,k1_funct_1(k2_funct_1(X0),sK2)) = sK2
% 2.10/1.00      | k2_relat_1(X0) != sK0
% 2.10/1.00      | v2_funct_1(X0) != iProver_top
% 2.10/1.00      | v1_funct_1(X0) != iProver_top
% 2.10/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_372]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2745,plain,
% 2.10/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(k2_funct_1(k2_funct_1(sK3)),sK2)) = sK2
% 2.10/1.00      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.10/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.10/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_2741,c_1085]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_16,plain,
% 2.10/1.00      ( ~ v2_funct_1(X0)
% 2.10/1.00      | ~ v1_funct_1(X0)
% 2.10/1.00      | ~ v1_relat_1(X0)
% 2.10/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.10/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1088,plain,
% 2.10/1.00      ( k2_funct_1(k2_funct_1(X0)) = X0
% 2.10/1.00      | v2_funct_1(X0) != iProver_top
% 2.10/1.00      | v1_funct_1(X0) != iProver_top
% 2.10/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1933,plain,
% 2.10/1.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 2.10/1.00      | v1_funct_1(sK3) != iProver_top
% 2.10/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.10/1.00      inference(superposition,[status(thm)],[c_1087,c_1088]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1306,plain,
% 2.10/1.00      ( ~ v2_funct_1(sK3)
% 2.10/1.00      | ~ v1_funct_1(sK3)
% 2.10/1.00      | ~ v1_relat_1(sK3)
% 2.10/1.00      | k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2099,plain,
% 2.10/1.00      ( k2_funct_1(k2_funct_1(sK3)) = sK3 ),
% 2.10/1.00      inference(global_propositional_subsumption,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_1933,c_32,c_29,c_1269,c_1272,c_1306]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_2760,plain,
% 2.10/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) = sK2
% 2.10/1.00      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.10/1.00      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 2.10/1.00      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 2.10/1.00      inference(light_normalisation,[status(thm)],[c_2745,c_2099]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_8,plain,
% 2.10/1.00      ( ~ v2_funct_1(X0)
% 2.10/1.00      | v2_funct_1(k2_funct_1(X0))
% 2.10/1.00      | ~ v1_funct_1(X0)
% 2.10/1.00      | ~ v1_relat_1(X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1281,plain,
% 2.10/1.00      ( v2_funct_1(k2_funct_1(sK3))
% 2.10/1.00      | ~ v2_funct_1(sK3)
% 2.10/1.00      | ~ v1_funct_1(sK3)
% 2.10/1.00      | ~ v1_relat_1(sK3) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1282,plain,
% 2.10/1.00      ( v2_funct_1(k2_funct_1(sK3)) = iProver_top
% 2.10/1.00      | v2_funct_1(sK3) != iProver_top
% 2.10/1.00      | v1_funct_1(sK3) != iProver_top
% 2.10/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1281]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_7,plain,
% 2.10/1.00      ( ~ v1_funct_1(X0)
% 2.10/1.00      | ~ v1_relat_1(X0)
% 2.10/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 2.10/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1278,plain,
% 2.10/1.00      ( ~ v1_funct_1(sK3)
% 2.10/1.00      | v1_relat_1(k2_funct_1(sK3))
% 2.10/1.00      | ~ v1_relat_1(sK3) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1279,plain,
% 2.10/1.00      ( v1_funct_1(sK3) != iProver_top
% 2.10/1.00      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 2.10/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1278]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_6,plain,
% 2.10/1.00      ( ~ v1_funct_1(X0)
% 2.10/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.10/1.00      | ~ v1_relat_1(X0) ),
% 2.10/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1275,plain,
% 2.10/1.00      ( v1_funct_1(k2_funct_1(sK3))
% 2.10/1.00      | ~ v1_funct_1(sK3)
% 2.10/1.00      | ~ v1_relat_1(sK3) ),
% 2.10/1.00      inference(instantiation,[status(thm)],[c_6]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_1276,plain,
% 2.10/1.00      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 2.10/1.00      | v1_funct_1(sK3) != iProver_top
% 2.10/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_1275]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_26,negated_conjecture,
% 2.10/1.00      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK2)) != sK2 ),
% 2.10/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(c_36,plain,
% 2.10/1.00      ( v2_funct_1(sK3) = iProver_top ),
% 2.10/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.10/1.00  
% 2.10/1.00  cnf(contradiction,plain,
% 2.10/1.00      ( $false ),
% 2.10/1.00      inference(minisat,
% 2.10/1.00                [status(thm)],
% 2.10/1.00                [c_2760,c_1282,c_1279,c_1276,c_1273,c_1269,c_26,c_36,
% 2.10/1.00                 c_33]) ).
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.10/1.00  
% 2.10/1.00  ------                               Statistics
% 2.10/1.00  
% 2.10/1.00  ------ General
% 2.10/1.00  
% 2.10/1.00  abstr_ref_over_cycles:                  0
% 2.10/1.00  abstr_ref_under_cycles:                 0
% 2.10/1.00  gc_basic_clause_elim:                   0
% 2.10/1.00  forced_gc_time:                         0
% 2.10/1.00  parsing_time:                           0.009
% 2.10/1.00  unif_index_cands_time:                  0.
% 2.10/1.00  unif_index_add_time:                    0.
% 2.10/1.00  orderings_time:                         0.
% 2.10/1.00  out_proof_time:                         0.011
% 2.10/1.00  total_time:                             0.128
% 2.10/1.00  num_of_symbols:                         54
% 2.10/1.00  num_of_terms:                           1984
% 2.10/1.00  
% 2.10/1.00  ------ Preprocessing
% 2.10/1.00  
% 2.10/1.00  num_of_splits:                          0
% 2.10/1.00  num_of_split_atoms:                     0
% 2.10/1.00  num_of_reused_defs:                     0
% 2.10/1.00  num_eq_ax_congr_red:                    14
% 2.10/1.00  num_of_sem_filtered_clauses:            1
% 2.10/1.00  num_of_subtypes:                        0
% 2.10/1.00  monotx_restored_types:                  0
% 2.10/1.00  sat_num_of_epr_types:                   0
% 2.10/1.00  sat_num_of_non_cyclic_types:            0
% 2.10/1.00  sat_guarded_non_collapsed_types:        0
% 2.10/1.00  num_pure_diseq_elim:                    0
% 2.10/1.00  simp_replaced_by:                       0
% 2.10/1.00  res_preprocessed:                       132
% 2.10/1.00  prep_upred:                             0
% 2.10/1.00  prep_unflattend:                        27
% 2.10/1.00  smt_new_axioms:                         0
% 2.10/1.00  pred_elim_cands:                        4
% 2.10/1.00  pred_elim:                              4
% 2.10/1.00  pred_elim_cl:                           7
% 2.10/1.00  pred_elim_cycles:                       6
% 2.10/1.00  merged_defs:                            0
% 2.10/1.00  merged_defs_ncl:                        0
% 2.10/1.00  bin_hyper_res:                          0
% 2.10/1.00  prep_cycles:                            4
% 2.10/1.00  pred_elim_time:                         0.007
% 2.10/1.00  splitting_time:                         0.
% 2.10/1.00  sem_filter_time:                        0.
% 2.10/1.00  monotx_time:                            0.001
% 2.10/1.00  subtype_inf_time:                       0.
% 2.10/1.00  
% 2.10/1.00  ------ Problem properties
% 2.10/1.00  
% 2.10/1.00  clauses:                                23
% 2.10/1.00  conjectures:                            4
% 2.10/1.00  epr:                                    5
% 2.10/1.00  horn:                                   22
% 2.10/1.00  ground:                                 7
% 2.10/1.00  unary:                                  6
% 2.10/1.00  binary:                                 5
% 2.10/1.00  lits:                                   63
% 2.10/1.00  lits_eq:                                26
% 2.10/1.00  fd_pure:                                0
% 2.10/1.00  fd_pseudo:                              0
% 2.10/1.00  fd_cond:                                0
% 2.10/1.00  fd_pseudo_cond:                         1
% 2.10/1.00  ac_symbols:                             0
% 2.10/1.00  
% 2.10/1.00  ------ Propositional Solver
% 2.10/1.00  
% 2.10/1.00  prop_solver_calls:                      27
% 2.10/1.00  prop_fast_solver_calls:                 900
% 2.10/1.00  smt_solver_calls:                       0
% 2.10/1.00  smt_fast_solver_calls:                  0
% 2.10/1.00  prop_num_of_clauses:                    902
% 2.10/1.00  prop_preprocess_simplified:             3990
% 2.10/1.00  prop_fo_subsumed:                       17
% 2.10/1.00  prop_solver_time:                       0.
% 2.10/1.00  smt_solver_time:                        0.
% 2.10/1.00  smt_fast_solver_time:                   0.
% 2.10/1.00  prop_fast_solver_time:                  0.
% 2.10/1.00  prop_unsat_core_time:                   0.
% 2.10/1.00  
% 2.10/1.00  ------ QBF
% 2.10/1.00  
% 2.10/1.00  qbf_q_res:                              0
% 2.10/1.00  qbf_num_tautologies:                    0
% 2.10/1.00  qbf_prep_cycles:                        0
% 2.10/1.00  
% 2.10/1.00  ------ BMC1
% 2.10/1.00  
% 2.10/1.00  bmc1_current_bound:                     -1
% 2.10/1.00  bmc1_last_solved_bound:                 -1
% 2.10/1.00  bmc1_unsat_core_size:                   -1
% 2.10/1.00  bmc1_unsat_core_parents_size:           -1
% 2.10/1.00  bmc1_merge_next_fun:                    0
% 2.10/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.10/1.00  
% 2.10/1.00  ------ Instantiation
% 2.10/1.00  
% 2.10/1.00  inst_num_of_clauses:                    287
% 2.10/1.00  inst_num_in_passive:                    59
% 2.10/1.00  inst_num_in_active:                     184
% 2.10/1.00  inst_num_in_unprocessed:                45
% 2.10/1.00  inst_num_of_loops:                      200
% 2.10/1.00  inst_num_of_learning_restarts:          0
% 2.10/1.00  inst_num_moves_active_passive:          13
% 2.10/1.00  inst_lit_activity:                      0
% 2.10/1.00  inst_lit_activity_moves:                0
% 2.10/1.00  inst_num_tautologies:                   0
% 2.10/1.00  inst_num_prop_implied:                  0
% 2.10/1.00  inst_num_existing_simplified:           0
% 2.10/1.00  inst_num_eq_res_simplified:             0
% 2.10/1.00  inst_num_child_elim:                    0
% 2.10/1.00  inst_num_of_dismatching_blockings:      15
% 2.10/1.00  inst_num_of_non_proper_insts:           241
% 2.10/1.00  inst_num_of_duplicates:                 0
% 2.10/1.00  inst_inst_num_from_inst_to_res:         0
% 2.10/1.00  inst_dismatching_checking_time:         0.
% 2.10/1.00  
% 2.10/1.00  ------ Resolution
% 2.10/1.00  
% 2.10/1.00  res_num_of_clauses:                     0
% 2.10/1.00  res_num_in_passive:                     0
% 2.10/1.00  res_num_in_active:                      0
% 2.10/1.00  res_num_of_loops:                       136
% 2.10/1.00  res_forward_subset_subsumed:            26
% 2.10/1.00  res_backward_subset_subsumed:           2
% 2.10/1.00  res_forward_subsumed:                   0
% 2.10/1.00  res_backward_subsumed:                  0
% 2.10/1.00  res_forward_subsumption_resolution:     0
% 2.10/1.00  res_backward_subsumption_resolution:    0
% 2.10/1.00  res_clause_to_clause_subsumption:       114
% 2.10/1.00  res_orphan_elimination:                 0
% 2.10/1.00  res_tautology_del:                      48
% 2.10/1.00  res_num_eq_res_simplified:              1
% 2.10/1.00  res_num_sel_changes:                    0
% 2.10/1.00  res_moves_from_active_to_pass:          0
% 2.10/1.00  
% 2.10/1.00  ------ Superposition
% 2.10/1.00  
% 2.10/1.00  sup_time_total:                         0.
% 2.10/1.00  sup_time_generating:                    0.
% 2.10/1.00  sup_time_sim_full:                      0.
% 2.10/1.00  sup_time_sim_immed:                     0.
% 2.10/1.00  
% 2.10/1.00  sup_num_of_clauses:                     52
% 2.10/1.00  sup_num_in_active:                      38
% 2.10/1.00  sup_num_in_passive:                     14
% 2.10/1.00  sup_num_of_loops:                       39
% 2.10/1.00  sup_fw_superposition:                   18
% 2.10/1.00  sup_bw_superposition:                   17
% 2.10/1.00  sup_immediate_simplified:               13
% 2.10/1.00  sup_given_eliminated:                   0
% 2.10/1.00  comparisons_done:                       0
% 2.10/1.00  comparisons_avoided:                    0
% 2.10/1.00  
% 2.10/1.00  ------ Simplifications
% 2.10/1.00  
% 2.10/1.00  
% 2.10/1.00  sim_fw_subset_subsumed:                 3
% 2.10/1.00  sim_bw_subset_subsumed:                 1
% 2.10/1.00  sim_fw_subsumed:                        2
% 2.10/1.00  sim_bw_subsumed:                        0
% 2.10/1.00  sim_fw_subsumption_res:                 0
% 2.10/1.00  sim_bw_subsumption_res:                 0
% 2.10/1.00  sim_tautology_del:                      0
% 2.10/1.00  sim_eq_tautology_del:                   2
% 2.10/1.00  sim_eq_res_simp:                        0
% 2.10/1.00  sim_fw_demodulated:                     0
% 2.10/1.00  sim_bw_demodulated:                     2
% 2.10/1.00  sim_light_normalised:                   11
% 2.10/1.00  sim_joinable_taut:                      0
% 2.10/1.00  sim_joinable_simp:                      0
% 2.10/1.00  sim_ac_normalised:                      0
% 2.10/1.00  sim_smt_subsumption:                    0
% 2.10/1.00  
%------------------------------------------------------------------------------
