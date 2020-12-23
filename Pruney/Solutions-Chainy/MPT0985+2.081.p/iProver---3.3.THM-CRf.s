%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:36 EST 2020

% Result     : Theorem 1.14s
% Output     : CNFRefutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :  152 (2624 expanded)
%              Number of clauses        :   97 ( 802 expanded)
%              Number of leaves         :   12 ( 513 expanded)
%              Depth                    :   24
%              Number of atoms          :  471 (14323 expanded)
%              Number of equality atoms :  238 (2870 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f43,plain,
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

fof(f44,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
      | ~ v1_funct_1(k2_funct_1(sK2)) )
    & k2_relset_1(sK0,sK1,sK2) = sK1
    & v2_funct_1(sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f43])).

fof(f77,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f74,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f76,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f33,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f44])).

fof(f59,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f58,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f75,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f38])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f83,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f49])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f87,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f68])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_31,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_420,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_31])).

cnf(c_421,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_423,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_421,c_34])).

cnf(c_1638,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_423])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1911,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1915,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1638,c_34,c_32,c_421,c_1911])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1642,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3766,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_1642])).

cnf(c_1641,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1643,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3053,plain,
    ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1641,c_1643])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_3065,plain,
    ( k2_relat_1(sK2) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_3053,c_30])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_406,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_407,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_409,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_34])).

cnf(c_1639,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_409])).

cnf(c_1919,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1639,c_34,c_32,c_407,c_1911])).

cnf(c_3080,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
    inference(demodulation,[status(thm)],[c_3065,c_1919])).

cnf(c_3786,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3766,c_3080])).

cnf(c_35,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_37,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1890,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1891,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1890])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1893,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1894,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1893])).

cnf(c_1912,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1911])).

cnf(c_5017,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3786,c_35,c_37,c_1891,c_1894,c_1912])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_636,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK0 != X1
    | sK1 != X2
    | sK2 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_33])).

cnf(c_637,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_636])).

cnf(c_639,plain,
    ( k1_relset_1(sK0,sK1,sK2) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_637,c_32])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1644,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3879,plain,
    ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1641,c_1644])).

cnf(c_4014,plain,
    ( k1_relat_1(sK2) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_639,c_3879])).

cnf(c_27,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_29,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_647,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK2) != X0
    | k2_relat_1(X0) != sK0
    | k1_relat_1(X0) != sK1 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_29])).

cnf(c_648,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(unflattening,[status(thm)],[c_647])).

cnf(c_660,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_648,c_16])).

cnf(c_1628,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_660])).

cnf(c_649,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_648])).

cnf(c_1988,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1628,c_35,c_37,c_649,c_1891,c_1894,c_1912])).

cnf(c_1989,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != sK0
    | k1_relat_1(k2_funct_1(sK2)) != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_1988])).

cnf(c_1992,plain,
    ( k2_relat_1(sK2) != sK1
    | k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1989,c_1915,c_1919])).

cnf(c_3079,plain,
    ( k1_relat_1(sK2) != sK0
    | sK1 != sK1
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3065,c_1992])).

cnf(c_3083,plain,
    ( k1_relat_1(sK2) != sK0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3079])).

cnf(c_4094,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4014,c_3083])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1908,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2381,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) ),
    inference(instantiation,[status(thm)],[c_1908])).

cnf(c_2382,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2381])).

cnf(c_11,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1648,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3226,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3080,c_1648])).

cnf(c_3227,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3226,c_1915])).

cnf(c_3675,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3227,c_35,c_37,c_1894,c_1912])).

cnf(c_4093,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4014,c_3675])).

cnf(c_4202,plain,
    ( sK1 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4094,c_2382,c_4093])).

cnf(c_5021,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5017,c_4202])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_5022,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5021,c_4])).

cnf(c_3881,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1644])).

cnf(c_5028,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5022,c_3881])).

cnf(c_4212,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4202,c_3080])).

cnf(c_5042,plain,
    ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_5028,c_4212])).

cnf(c_22,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_564,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | k2_funct_1(sK2) != X0
    | sK0 != X1
    | sK1 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_29])).

cnf(c_565,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_1632,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_565])).

cnf(c_1816,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1632,c_4])).

cnf(c_2187,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | sK1 != k1_xboole_0
    | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1816,c_35,c_37,c_1891,c_1912])).

cnf(c_2188,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | sK1 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2187])).

cnf(c_4216,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4202,c_2188])).

cnf(c_4249,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4216])).

cnf(c_4253,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4249,c_4])).

cnf(c_4752,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4212,c_1642])).

cnf(c_4761,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4752,c_1915])).

cnf(c_4762,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4761,c_4])).

cnf(c_5227,plain,
    ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4253,c_35,c_37,c_1891,c_1894,c_1912,c_4762])).

cnf(c_5546,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_5042,c_5227])).

cnf(c_108,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_107,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5546,c_108,c_107])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:15:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 1.14/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.14/1.03  
% 1.14/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.14/1.03  
% 1.14/1.03  ------  iProver source info
% 1.14/1.03  
% 1.14/1.03  git: date: 2020-06-30 10:37:57 +0100
% 1.14/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.14/1.03  git: non_committed_changes: false
% 1.14/1.03  git: last_make_outside_of_git: false
% 1.14/1.03  
% 1.14/1.03  ------ 
% 1.14/1.03  
% 1.14/1.03  ------ Input Options
% 1.14/1.03  
% 1.14/1.03  --out_options                           all
% 1.14/1.03  --tptp_safe_out                         true
% 1.14/1.03  --problem_path                          ""
% 1.14/1.03  --include_path                          ""
% 1.14/1.03  --clausifier                            res/vclausify_rel
% 1.14/1.03  --clausifier_options                    --mode clausify
% 1.14/1.03  --stdin                                 false
% 1.14/1.03  --stats_out                             all
% 1.14/1.03  
% 1.14/1.03  ------ General Options
% 1.14/1.03  
% 1.14/1.03  --fof                                   false
% 1.14/1.03  --time_out_real                         305.
% 1.14/1.03  --time_out_virtual                      -1.
% 1.14/1.03  --symbol_type_check                     false
% 1.14/1.03  --clausify_out                          false
% 1.14/1.03  --sig_cnt_out                           false
% 1.14/1.03  --trig_cnt_out                          false
% 1.14/1.03  --trig_cnt_out_tolerance                1.
% 1.14/1.03  --trig_cnt_out_sk_spl                   false
% 1.14/1.03  --abstr_cl_out                          false
% 1.14/1.03  
% 1.14/1.03  ------ Global Options
% 1.14/1.03  
% 1.14/1.03  --schedule                              default
% 1.14/1.03  --add_important_lit                     false
% 1.14/1.03  --prop_solver_per_cl                    1000
% 1.14/1.03  --min_unsat_core                        false
% 1.14/1.03  --soft_assumptions                      false
% 1.14/1.03  --soft_lemma_size                       3
% 1.14/1.03  --prop_impl_unit_size                   0
% 1.14/1.03  --prop_impl_unit                        []
% 1.14/1.03  --share_sel_clauses                     true
% 1.14/1.03  --reset_solvers                         false
% 1.14/1.03  --bc_imp_inh                            [conj_cone]
% 1.14/1.03  --conj_cone_tolerance                   3.
% 1.14/1.03  --extra_neg_conj                        none
% 1.14/1.03  --large_theory_mode                     true
% 1.14/1.03  --prolific_symb_bound                   200
% 1.14/1.03  --lt_threshold                          2000
% 1.14/1.03  --clause_weak_htbl                      true
% 1.14/1.03  --gc_record_bc_elim                     false
% 1.14/1.03  
% 1.14/1.03  ------ Preprocessing Options
% 1.14/1.03  
% 1.14/1.03  --preprocessing_flag                    true
% 1.14/1.03  --time_out_prep_mult                    0.1
% 1.14/1.03  --splitting_mode                        input
% 1.14/1.03  --splitting_grd                         true
% 1.14/1.03  --splitting_cvd                         false
% 1.14/1.03  --splitting_cvd_svl                     false
% 1.14/1.03  --splitting_nvd                         32
% 1.14/1.03  --sub_typing                            true
% 1.14/1.03  --prep_gs_sim                           true
% 1.14/1.03  --prep_unflatten                        true
% 1.14/1.03  --prep_res_sim                          true
% 1.14/1.03  --prep_upred                            true
% 1.14/1.03  --prep_sem_filter                       exhaustive
% 1.14/1.03  --prep_sem_filter_out                   false
% 1.14/1.03  --pred_elim                             true
% 1.14/1.03  --res_sim_input                         true
% 1.14/1.03  --eq_ax_congr_red                       true
% 1.14/1.03  --pure_diseq_elim                       true
% 1.14/1.03  --brand_transform                       false
% 1.14/1.03  --non_eq_to_eq                          false
% 1.14/1.03  --prep_def_merge                        true
% 1.14/1.03  --prep_def_merge_prop_impl              false
% 1.14/1.03  --prep_def_merge_mbd                    true
% 1.14/1.03  --prep_def_merge_tr_red                 false
% 1.14/1.03  --prep_def_merge_tr_cl                  false
% 1.14/1.03  --smt_preprocessing                     true
% 1.14/1.03  --smt_ac_axioms                         fast
% 1.14/1.03  --preprocessed_out                      false
% 1.14/1.03  --preprocessed_stats                    false
% 1.14/1.03  
% 1.14/1.03  ------ Abstraction refinement Options
% 1.14/1.03  
% 1.14/1.03  --abstr_ref                             []
% 1.14/1.03  --abstr_ref_prep                        false
% 1.14/1.03  --abstr_ref_until_sat                   false
% 1.14/1.03  --abstr_ref_sig_restrict                funpre
% 1.14/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.14/1.03  --abstr_ref_under                       []
% 1.14/1.03  
% 1.14/1.03  ------ SAT Options
% 1.14/1.03  
% 1.14/1.03  --sat_mode                              false
% 1.14/1.03  --sat_fm_restart_options                ""
% 1.14/1.03  --sat_gr_def                            false
% 1.14/1.03  --sat_epr_types                         true
% 1.14/1.03  --sat_non_cyclic_types                  false
% 1.14/1.03  --sat_finite_models                     false
% 1.14/1.03  --sat_fm_lemmas                         false
% 1.14/1.03  --sat_fm_prep                           false
% 1.14/1.03  --sat_fm_uc_incr                        true
% 1.14/1.03  --sat_out_model                         small
% 1.14/1.03  --sat_out_clauses                       false
% 1.14/1.03  
% 1.14/1.03  ------ QBF Options
% 1.14/1.03  
% 1.14/1.03  --qbf_mode                              false
% 1.14/1.03  --qbf_elim_univ                         false
% 1.14/1.03  --qbf_dom_inst                          none
% 1.14/1.03  --qbf_dom_pre_inst                      false
% 1.14/1.03  --qbf_sk_in                             false
% 1.14/1.03  --qbf_pred_elim                         true
% 1.14/1.03  --qbf_split                             512
% 1.14/1.03  
% 1.14/1.03  ------ BMC1 Options
% 1.14/1.03  
% 1.14/1.03  --bmc1_incremental                      false
% 1.14/1.03  --bmc1_axioms                           reachable_all
% 1.14/1.03  --bmc1_min_bound                        0
% 1.14/1.03  --bmc1_max_bound                        -1
% 1.14/1.03  --bmc1_max_bound_default                -1
% 1.14/1.03  --bmc1_symbol_reachability              true
% 1.14/1.03  --bmc1_property_lemmas                  false
% 1.14/1.03  --bmc1_k_induction                      false
% 1.14/1.03  --bmc1_non_equiv_states                 false
% 1.14/1.03  --bmc1_deadlock                         false
% 1.14/1.03  --bmc1_ucm                              false
% 1.14/1.03  --bmc1_add_unsat_core                   none
% 1.14/1.03  --bmc1_unsat_core_children              false
% 1.14/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.14/1.03  --bmc1_out_stat                         full
% 1.14/1.03  --bmc1_ground_init                      false
% 1.14/1.03  --bmc1_pre_inst_next_state              false
% 1.14/1.03  --bmc1_pre_inst_state                   false
% 1.14/1.03  --bmc1_pre_inst_reach_state             false
% 1.14/1.03  --bmc1_out_unsat_core                   false
% 1.14/1.03  --bmc1_aig_witness_out                  false
% 1.14/1.03  --bmc1_verbose                          false
% 1.14/1.03  --bmc1_dump_clauses_tptp                false
% 1.14/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.14/1.03  --bmc1_dump_file                        -
% 1.14/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.14/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.14/1.03  --bmc1_ucm_extend_mode                  1
% 1.14/1.03  --bmc1_ucm_init_mode                    2
% 1.14/1.03  --bmc1_ucm_cone_mode                    none
% 1.14/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.14/1.03  --bmc1_ucm_relax_model                  4
% 1.14/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.14/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.14/1.03  --bmc1_ucm_layered_model                none
% 1.14/1.03  --bmc1_ucm_max_lemma_size               10
% 1.14/1.03  
% 1.14/1.03  ------ AIG Options
% 1.14/1.03  
% 1.14/1.03  --aig_mode                              false
% 1.14/1.03  
% 1.14/1.03  ------ Instantiation Options
% 1.14/1.03  
% 1.14/1.03  --instantiation_flag                    true
% 1.14/1.03  --inst_sos_flag                         false
% 1.14/1.03  --inst_sos_phase                        true
% 1.14/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.14/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.14/1.03  --inst_lit_sel_side                     num_symb
% 1.14/1.03  --inst_solver_per_active                1400
% 1.14/1.03  --inst_solver_calls_frac                1.
% 1.14/1.03  --inst_passive_queue_type               priority_queues
% 1.14/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.14/1.03  --inst_passive_queues_freq              [25;2]
% 1.14/1.03  --inst_dismatching                      true
% 1.14/1.03  --inst_eager_unprocessed_to_passive     true
% 1.14/1.03  --inst_prop_sim_given                   true
% 1.14/1.03  --inst_prop_sim_new                     false
% 1.14/1.03  --inst_subs_new                         false
% 1.14/1.03  --inst_eq_res_simp                      false
% 1.14/1.03  --inst_subs_given                       false
% 1.14/1.03  --inst_orphan_elimination               true
% 1.14/1.03  --inst_learning_loop_flag               true
% 1.14/1.03  --inst_learning_start                   3000
% 1.14/1.03  --inst_learning_factor                  2
% 1.14/1.03  --inst_start_prop_sim_after_learn       3
% 1.14/1.03  --inst_sel_renew                        solver
% 1.14/1.03  --inst_lit_activity_flag                true
% 1.14/1.03  --inst_restr_to_given                   false
% 1.14/1.03  --inst_activity_threshold               500
% 1.14/1.03  --inst_out_proof                        true
% 1.14/1.03  
% 1.14/1.03  ------ Resolution Options
% 1.14/1.03  
% 1.14/1.03  --resolution_flag                       true
% 1.14/1.03  --res_lit_sel                           adaptive
% 1.14/1.03  --res_lit_sel_side                      none
% 1.14/1.03  --res_ordering                          kbo
% 1.14/1.03  --res_to_prop_solver                    active
% 1.14/1.03  --res_prop_simpl_new                    false
% 1.14/1.03  --res_prop_simpl_given                  true
% 1.14/1.03  --res_passive_queue_type                priority_queues
% 1.14/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.14/1.03  --res_passive_queues_freq               [15;5]
% 1.14/1.03  --res_forward_subs                      full
% 1.14/1.03  --res_backward_subs                     full
% 1.14/1.03  --res_forward_subs_resolution           true
% 1.14/1.03  --res_backward_subs_resolution          true
% 1.14/1.03  --res_orphan_elimination                true
% 1.14/1.03  --res_time_limit                        2.
% 1.14/1.03  --res_out_proof                         true
% 1.14/1.03  
% 1.14/1.03  ------ Superposition Options
% 1.14/1.03  
% 1.14/1.03  --superposition_flag                    true
% 1.14/1.03  --sup_passive_queue_type                priority_queues
% 1.14/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.14/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.14/1.03  --demod_completeness_check              fast
% 1.14/1.03  --demod_use_ground                      true
% 1.14/1.03  --sup_to_prop_solver                    passive
% 1.14/1.03  --sup_prop_simpl_new                    true
% 1.14/1.03  --sup_prop_simpl_given                  true
% 1.14/1.03  --sup_fun_splitting                     false
% 1.14/1.03  --sup_smt_interval                      50000
% 1.14/1.03  
% 1.14/1.03  ------ Superposition Simplification Setup
% 1.14/1.03  
% 1.14/1.03  --sup_indices_passive                   []
% 1.14/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.14/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_full_bw                           [BwDemod]
% 1.14/1.03  --sup_immed_triv                        [TrivRules]
% 1.14/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.14/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_immed_bw_main                     []
% 1.14/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.14/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.03  
% 1.14/1.03  ------ Combination Options
% 1.14/1.03  
% 1.14/1.03  --comb_res_mult                         3
% 1.14/1.03  --comb_sup_mult                         2
% 1.14/1.03  --comb_inst_mult                        10
% 1.14/1.03  
% 1.14/1.03  ------ Debug Options
% 1.14/1.03  
% 1.14/1.03  --dbg_backtrace                         false
% 1.14/1.03  --dbg_dump_prop_clauses                 false
% 1.14/1.03  --dbg_dump_prop_clauses_file            -
% 1.14/1.03  --dbg_out_stat                          false
% 1.14/1.03  ------ Parsing...
% 1.14/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.14/1.03  
% 1.14/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 1.14/1.03  
% 1.14/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.14/1.03  
% 1.14/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.14/1.03  ------ Proving...
% 1.14/1.03  ------ Problem Properties 
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  clauses                                 32
% 1.14/1.03  conjectures                             3
% 1.14/1.03  EPR                                     3
% 1.14/1.03  Horn                                    27
% 1.14/1.03  unary                                   7
% 1.14/1.03  binary                                  10
% 1.14/1.03  lits                                    84
% 1.14/1.03  lits eq                                 36
% 1.14/1.03  fd_pure                                 0
% 1.14/1.03  fd_pseudo                               0
% 1.14/1.03  fd_cond                                 2
% 1.14/1.03  fd_pseudo_cond                          1
% 1.14/1.03  AC symbols                              0
% 1.14/1.03  
% 1.14/1.03  ------ Schedule dynamic 5 is on 
% 1.14/1.03  
% 1.14/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  ------ 
% 1.14/1.03  Current options:
% 1.14/1.03  ------ 
% 1.14/1.03  
% 1.14/1.03  ------ Input Options
% 1.14/1.03  
% 1.14/1.03  --out_options                           all
% 1.14/1.03  --tptp_safe_out                         true
% 1.14/1.03  --problem_path                          ""
% 1.14/1.03  --include_path                          ""
% 1.14/1.03  --clausifier                            res/vclausify_rel
% 1.14/1.03  --clausifier_options                    --mode clausify
% 1.14/1.03  --stdin                                 false
% 1.14/1.03  --stats_out                             all
% 1.14/1.03  
% 1.14/1.03  ------ General Options
% 1.14/1.03  
% 1.14/1.03  --fof                                   false
% 1.14/1.03  --time_out_real                         305.
% 1.14/1.03  --time_out_virtual                      -1.
% 1.14/1.03  --symbol_type_check                     false
% 1.14/1.03  --clausify_out                          false
% 1.14/1.03  --sig_cnt_out                           false
% 1.14/1.03  --trig_cnt_out                          false
% 1.14/1.03  --trig_cnt_out_tolerance                1.
% 1.14/1.03  --trig_cnt_out_sk_spl                   false
% 1.14/1.03  --abstr_cl_out                          false
% 1.14/1.03  
% 1.14/1.03  ------ Global Options
% 1.14/1.03  
% 1.14/1.03  --schedule                              default
% 1.14/1.03  --add_important_lit                     false
% 1.14/1.03  --prop_solver_per_cl                    1000
% 1.14/1.03  --min_unsat_core                        false
% 1.14/1.03  --soft_assumptions                      false
% 1.14/1.03  --soft_lemma_size                       3
% 1.14/1.03  --prop_impl_unit_size                   0
% 1.14/1.03  --prop_impl_unit                        []
% 1.14/1.03  --share_sel_clauses                     true
% 1.14/1.03  --reset_solvers                         false
% 1.14/1.03  --bc_imp_inh                            [conj_cone]
% 1.14/1.03  --conj_cone_tolerance                   3.
% 1.14/1.03  --extra_neg_conj                        none
% 1.14/1.03  --large_theory_mode                     true
% 1.14/1.03  --prolific_symb_bound                   200
% 1.14/1.03  --lt_threshold                          2000
% 1.14/1.03  --clause_weak_htbl                      true
% 1.14/1.03  --gc_record_bc_elim                     false
% 1.14/1.03  
% 1.14/1.03  ------ Preprocessing Options
% 1.14/1.03  
% 1.14/1.03  --preprocessing_flag                    true
% 1.14/1.03  --time_out_prep_mult                    0.1
% 1.14/1.03  --splitting_mode                        input
% 1.14/1.03  --splitting_grd                         true
% 1.14/1.03  --splitting_cvd                         false
% 1.14/1.03  --splitting_cvd_svl                     false
% 1.14/1.03  --splitting_nvd                         32
% 1.14/1.03  --sub_typing                            true
% 1.14/1.03  --prep_gs_sim                           true
% 1.14/1.03  --prep_unflatten                        true
% 1.14/1.03  --prep_res_sim                          true
% 1.14/1.03  --prep_upred                            true
% 1.14/1.03  --prep_sem_filter                       exhaustive
% 1.14/1.03  --prep_sem_filter_out                   false
% 1.14/1.03  --pred_elim                             true
% 1.14/1.03  --res_sim_input                         true
% 1.14/1.03  --eq_ax_congr_red                       true
% 1.14/1.03  --pure_diseq_elim                       true
% 1.14/1.03  --brand_transform                       false
% 1.14/1.03  --non_eq_to_eq                          false
% 1.14/1.03  --prep_def_merge                        true
% 1.14/1.03  --prep_def_merge_prop_impl              false
% 1.14/1.03  --prep_def_merge_mbd                    true
% 1.14/1.03  --prep_def_merge_tr_red                 false
% 1.14/1.03  --prep_def_merge_tr_cl                  false
% 1.14/1.03  --smt_preprocessing                     true
% 1.14/1.03  --smt_ac_axioms                         fast
% 1.14/1.03  --preprocessed_out                      false
% 1.14/1.03  --preprocessed_stats                    false
% 1.14/1.03  
% 1.14/1.03  ------ Abstraction refinement Options
% 1.14/1.03  
% 1.14/1.03  --abstr_ref                             []
% 1.14/1.03  --abstr_ref_prep                        false
% 1.14/1.03  --abstr_ref_until_sat                   false
% 1.14/1.03  --abstr_ref_sig_restrict                funpre
% 1.14/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 1.14/1.03  --abstr_ref_under                       []
% 1.14/1.03  
% 1.14/1.03  ------ SAT Options
% 1.14/1.03  
% 1.14/1.03  --sat_mode                              false
% 1.14/1.03  --sat_fm_restart_options                ""
% 1.14/1.03  --sat_gr_def                            false
% 1.14/1.03  --sat_epr_types                         true
% 1.14/1.03  --sat_non_cyclic_types                  false
% 1.14/1.03  --sat_finite_models                     false
% 1.14/1.03  --sat_fm_lemmas                         false
% 1.14/1.03  --sat_fm_prep                           false
% 1.14/1.03  --sat_fm_uc_incr                        true
% 1.14/1.03  --sat_out_model                         small
% 1.14/1.03  --sat_out_clauses                       false
% 1.14/1.03  
% 1.14/1.03  ------ QBF Options
% 1.14/1.03  
% 1.14/1.03  --qbf_mode                              false
% 1.14/1.03  --qbf_elim_univ                         false
% 1.14/1.03  --qbf_dom_inst                          none
% 1.14/1.03  --qbf_dom_pre_inst                      false
% 1.14/1.03  --qbf_sk_in                             false
% 1.14/1.03  --qbf_pred_elim                         true
% 1.14/1.03  --qbf_split                             512
% 1.14/1.03  
% 1.14/1.03  ------ BMC1 Options
% 1.14/1.03  
% 1.14/1.03  --bmc1_incremental                      false
% 1.14/1.03  --bmc1_axioms                           reachable_all
% 1.14/1.03  --bmc1_min_bound                        0
% 1.14/1.03  --bmc1_max_bound                        -1
% 1.14/1.03  --bmc1_max_bound_default                -1
% 1.14/1.03  --bmc1_symbol_reachability              true
% 1.14/1.03  --bmc1_property_lemmas                  false
% 1.14/1.03  --bmc1_k_induction                      false
% 1.14/1.03  --bmc1_non_equiv_states                 false
% 1.14/1.03  --bmc1_deadlock                         false
% 1.14/1.03  --bmc1_ucm                              false
% 1.14/1.03  --bmc1_add_unsat_core                   none
% 1.14/1.03  --bmc1_unsat_core_children              false
% 1.14/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 1.14/1.03  --bmc1_out_stat                         full
% 1.14/1.03  --bmc1_ground_init                      false
% 1.14/1.03  --bmc1_pre_inst_next_state              false
% 1.14/1.03  --bmc1_pre_inst_state                   false
% 1.14/1.03  --bmc1_pre_inst_reach_state             false
% 1.14/1.03  --bmc1_out_unsat_core                   false
% 1.14/1.03  --bmc1_aig_witness_out                  false
% 1.14/1.03  --bmc1_verbose                          false
% 1.14/1.03  --bmc1_dump_clauses_tptp                false
% 1.14/1.03  --bmc1_dump_unsat_core_tptp             false
% 1.14/1.03  --bmc1_dump_file                        -
% 1.14/1.03  --bmc1_ucm_expand_uc_limit              128
% 1.14/1.03  --bmc1_ucm_n_expand_iterations          6
% 1.14/1.03  --bmc1_ucm_extend_mode                  1
% 1.14/1.03  --bmc1_ucm_init_mode                    2
% 1.14/1.03  --bmc1_ucm_cone_mode                    none
% 1.14/1.03  --bmc1_ucm_reduced_relation_type        0
% 1.14/1.03  --bmc1_ucm_relax_model                  4
% 1.14/1.03  --bmc1_ucm_full_tr_after_sat            true
% 1.14/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 1.14/1.03  --bmc1_ucm_layered_model                none
% 1.14/1.03  --bmc1_ucm_max_lemma_size               10
% 1.14/1.03  
% 1.14/1.03  ------ AIG Options
% 1.14/1.03  
% 1.14/1.03  --aig_mode                              false
% 1.14/1.03  
% 1.14/1.03  ------ Instantiation Options
% 1.14/1.03  
% 1.14/1.03  --instantiation_flag                    true
% 1.14/1.03  --inst_sos_flag                         false
% 1.14/1.03  --inst_sos_phase                        true
% 1.14/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.14/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.14/1.03  --inst_lit_sel_side                     none
% 1.14/1.03  --inst_solver_per_active                1400
% 1.14/1.03  --inst_solver_calls_frac                1.
% 1.14/1.03  --inst_passive_queue_type               priority_queues
% 1.14/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.14/1.03  --inst_passive_queues_freq              [25;2]
% 1.14/1.03  --inst_dismatching                      true
% 1.14/1.03  --inst_eager_unprocessed_to_passive     true
% 1.14/1.03  --inst_prop_sim_given                   true
% 1.14/1.03  --inst_prop_sim_new                     false
% 1.14/1.03  --inst_subs_new                         false
% 1.14/1.03  --inst_eq_res_simp                      false
% 1.14/1.03  --inst_subs_given                       false
% 1.14/1.03  --inst_orphan_elimination               true
% 1.14/1.03  --inst_learning_loop_flag               true
% 1.14/1.03  --inst_learning_start                   3000
% 1.14/1.03  --inst_learning_factor                  2
% 1.14/1.03  --inst_start_prop_sim_after_learn       3
% 1.14/1.03  --inst_sel_renew                        solver
% 1.14/1.03  --inst_lit_activity_flag                true
% 1.14/1.03  --inst_restr_to_given                   false
% 1.14/1.03  --inst_activity_threshold               500
% 1.14/1.03  --inst_out_proof                        true
% 1.14/1.03  
% 1.14/1.03  ------ Resolution Options
% 1.14/1.03  
% 1.14/1.03  --resolution_flag                       false
% 1.14/1.03  --res_lit_sel                           adaptive
% 1.14/1.03  --res_lit_sel_side                      none
% 1.14/1.03  --res_ordering                          kbo
% 1.14/1.03  --res_to_prop_solver                    active
% 1.14/1.03  --res_prop_simpl_new                    false
% 1.14/1.03  --res_prop_simpl_given                  true
% 1.14/1.03  --res_passive_queue_type                priority_queues
% 1.14/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.14/1.03  --res_passive_queues_freq               [15;5]
% 1.14/1.03  --res_forward_subs                      full
% 1.14/1.03  --res_backward_subs                     full
% 1.14/1.03  --res_forward_subs_resolution           true
% 1.14/1.03  --res_backward_subs_resolution          true
% 1.14/1.03  --res_orphan_elimination                true
% 1.14/1.03  --res_time_limit                        2.
% 1.14/1.03  --res_out_proof                         true
% 1.14/1.03  
% 1.14/1.03  ------ Superposition Options
% 1.14/1.03  
% 1.14/1.03  --superposition_flag                    true
% 1.14/1.03  --sup_passive_queue_type                priority_queues
% 1.14/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.14/1.03  --sup_passive_queues_freq               [8;1;4]
% 1.14/1.03  --demod_completeness_check              fast
% 1.14/1.03  --demod_use_ground                      true
% 1.14/1.03  --sup_to_prop_solver                    passive
% 1.14/1.03  --sup_prop_simpl_new                    true
% 1.14/1.03  --sup_prop_simpl_given                  true
% 1.14/1.03  --sup_fun_splitting                     false
% 1.14/1.03  --sup_smt_interval                      50000
% 1.14/1.03  
% 1.14/1.03  ------ Superposition Simplification Setup
% 1.14/1.03  
% 1.14/1.03  --sup_indices_passive                   []
% 1.14/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.14/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 1.14/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_full_bw                           [BwDemod]
% 1.14/1.03  --sup_immed_triv                        [TrivRules]
% 1.14/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.14/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_immed_bw_main                     []
% 1.14/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 1.14/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.14/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.14/1.03  
% 1.14/1.03  ------ Combination Options
% 1.14/1.03  
% 1.14/1.03  --comb_res_mult                         3
% 1.14/1.03  --comb_sup_mult                         2
% 1.14/1.03  --comb_inst_mult                        10
% 1.14/1.03  
% 1.14/1.03  ------ Debug Options
% 1.14/1.03  
% 1.14/1.03  --dbg_backtrace                         false
% 1.14/1.03  --dbg_dump_prop_clauses                 false
% 1.14/1.03  --dbg_dump_prop_clauses_file            -
% 1.14/1.03  --dbg_out_stat                          false
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  ------ Proving...
% 1.14/1.03  
% 1.14/1.03  
% 1.14/1.03  % SZS status Theorem for theBenchmark.p
% 1.14/1.03  
% 1.14/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 1.14/1.03  
% 1.14/1.03  fof(f9,axiom,(
% 1.14/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 1.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f24,plain,(
% 1.14/1.03    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.14/1.03    inference(ennf_transformation,[],[f9])).
% 1.14/1.03  
% 1.14/1.03  fof(f25,plain,(
% 1.14/1.03    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.14/1.03    inference(flattening,[],[f24])).
% 1.14/1.03  
% 1.14/1.03  fof(f60,plain,(
% 1.14/1.03    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f25])).
% 1.14/1.03  
% 1.14/1.03  fof(f16,conjecture,(
% 1.14/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f17,negated_conjecture,(
% 1.14/1.03    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.14/1.03    inference(negated_conjecture,[],[f16])).
% 1.14/1.03  
% 1.14/1.03  fof(f34,plain,(
% 1.14/1.03    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.14/1.03    inference(ennf_transformation,[],[f17])).
% 1.14/1.03  
% 1.14/1.03  fof(f35,plain,(
% 1.14/1.03    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.14/1.03    inference(flattening,[],[f34])).
% 1.14/1.03  
% 1.14/1.03  fof(f43,plain,(
% 1.14/1.03    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.14/1.03    introduced(choice_axiom,[])).
% 1.14/1.03  
% 1.14/1.03  fof(f44,plain,(
% 1.14/1.03    (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))) & k2_relset_1(sK0,sK1,sK2) = sK1 & v2_funct_1(sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.14/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f35,f43])).
% 1.14/1.03  
% 1.14/1.03  fof(f77,plain,(
% 1.14/1.03    v2_funct_1(sK2)),
% 1.14/1.03    inference(cnf_transformation,[],[f44])).
% 1.14/1.03  
% 1.14/1.03  fof(f74,plain,(
% 1.14/1.03    v1_funct_1(sK2)),
% 1.14/1.03    inference(cnf_transformation,[],[f44])).
% 1.14/1.03  
% 1.14/1.03  fof(f76,plain,(
% 1.14/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.14/1.03    inference(cnf_transformation,[],[f44])).
% 1.14/1.03  
% 1.14/1.03  fof(f10,axiom,(
% 1.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f26,plain,(
% 1.14/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(ennf_transformation,[],[f10])).
% 1.14/1.03  
% 1.14/1.03  fof(f61,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f26])).
% 1.14/1.03  
% 1.14/1.03  fof(f15,axiom,(
% 1.14/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f32,plain,(
% 1.14/1.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.14/1.03    inference(ennf_transformation,[],[f15])).
% 1.14/1.03  
% 1.14/1.03  fof(f33,plain,(
% 1.14/1.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.14/1.03    inference(flattening,[],[f32])).
% 1.14/1.03  
% 1.14/1.03  fof(f73,plain,(
% 1.14/1.03    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f33])).
% 1.14/1.03  
% 1.14/1.03  fof(f13,axiom,(
% 1.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f29,plain,(
% 1.14/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(ennf_transformation,[],[f13])).
% 1.14/1.03  
% 1.14/1.03  fof(f64,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f29])).
% 1.14/1.03  
% 1.14/1.03  fof(f78,plain,(
% 1.14/1.03    k2_relset_1(sK0,sK1,sK2) = sK1),
% 1.14/1.03    inference(cnf_transformation,[],[f44])).
% 1.14/1.03  
% 1.14/1.03  fof(f59,plain,(
% 1.14/1.03    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f25])).
% 1.14/1.03  
% 1.14/1.03  fof(f8,axiom,(
% 1.14/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f22,plain,(
% 1.14/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.14/1.03    inference(ennf_transformation,[],[f8])).
% 1.14/1.03  
% 1.14/1.03  fof(f23,plain,(
% 1.14/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.14/1.03    inference(flattening,[],[f22])).
% 1.14/1.03  
% 1.14/1.03  fof(f58,plain,(
% 1.14/1.03    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f23])).
% 1.14/1.03  
% 1.14/1.03  fof(f57,plain,(
% 1.14/1.03    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f23])).
% 1.14/1.03  
% 1.14/1.03  fof(f14,axiom,(
% 1.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f30,plain,(
% 1.14/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(ennf_transformation,[],[f14])).
% 1.14/1.03  
% 1.14/1.03  fof(f31,plain,(
% 1.14/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(flattening,[],[f30])).
% 1.14/1.03  
% 1.14/1.03  fof(f42,plain,(
% 1.14/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(nnf_transformation,[],[f31])).
% 1.14/1.03  
% 1.14/1.03  fof(f65,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f42])).
% 1.14/1.03  
% 1.14/1.03  fof(f75,plain,(
% 1.14/1.03    v1_funct_2(sK2,sK0,sK1)),
% 1.14/1.03    inference(cnf_transformation,[],[f44])).
% 1.14/1.03  
% 1.14/1.03  fof(f12,axiom,(
% 1.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f28,plain,(
% 1.14/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.14/1.03    inference(ennf_transformation,[],[f12])).
% 1.14/1.03  
% 1.14/1.03  fof(f63,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f28])).
% 1.14/1.03  
% 1.14/1.03  fof(f72,plain,(
% 1.14/1.03    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f33])).
% 1.14/1.03  
% 1.14/1.03  fof(f79,plain,(
% 1.14/1.03    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~v1_funct_1(k2_funct_1(sK2))),
% 1.14/1.03    inference(cnf_transformation,[],[f44])).
% 1.14/1.03  
% 1.14/1.03  fof(f4,axiom,(
% 1.14/1.03    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f40,plain,(
% 1.14/1.03    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.14/1.03    inference(nnf_transformation,[],[f4])).
% 1.14/1.03  
% 1.14/1.03  fof(f53,plain,(
% 1.14/1.03    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f40])).
% 1.14/1.03  
% 1.14/1.03  fof(f7,axiom,(
% 1.14/1.03    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 1.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f21,plain,(
% 1.14/1.03    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.14/1.03    inference(ennf_transformation,[],[f7])).
% 1.14/1.03  
% 1.14/1.03  fof(f56,plain,(
% 1.14/1.03    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.14/1.03    inference(cnf_transformation,[],[f21])).
% 1.14/1.03  
% 1.14/1.03  fof(f2,axiom,(
% 1.14/1.03    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.14/1.03  
% 1.14/1.03  fof(f38,plain,(
% 1.14/1.03    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.14/1.03    inference(nnf_transformation,[],[f2])).
% 1.14/1.03  
% 1.14/1.03  fof(f39,plain,(
% 1.14/1.03    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 1.14/1.03    inference(flattening,[],[f38])).
% 1.14/1.03  
% 1.14/1.03  fof(f49,plain,(
% 1.14/1.03    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 1.14/1.03    inference(cnf_transformation,[],[f39])).
% 1.14/1.03  
% 1.14/1.03  fof(f83,plain,(
% 1.14/1.03    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 1.14/1.03    inference(equality_resolution,[],[f49])).
% 1.14/1.03  
% 1.14/1.03  fof(f68,plain,(
% 1.14/1.03    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.14/1.03    inference(cnf_transformation,[],[f42])).
% 1.14/1.03  
% 1.14/1.03  fof(f87,plain,(
% 1.14/1.03    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.14/1.03    inference(equality_resolution,[],[f68])).
% 1.14/1.03  
% 1.14/1.03  fof(f48,plain,(
% 1.14/1.03    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0) )),
% 1.14/1.03    inference(cnf_transformation,[],[f39])).
% 1.14/1.03  
% 1.14/1.03  cnf(c_14,plain,
% 1.14/1.03      ( ~ v2_funct_1(X0)
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f60]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_31,negated_conjecture,
% 1.14/1.03      ( v2_funct_1(sK2) ),
% 1.14/1.03      inference(cnf_transformation,[],[f77]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_420,plain,
% 1.14/1.03      ( ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 1.14/1.03      | sK2 != X0 ),
% 1.14/1.03      inference(resolution_lifted,[status(thm)],[c_14,c_31]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_421,plain,
% 1.14/1.03      ( ~ v1_funct_1(sK2)
% 1.14/1.03      | ~ v1_relat_1(sK2)
% 1.14/1.03      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.14/1.03      inference(unflattening,[status(thm)],[c_420]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_34,negated_conjecture,
% 1.14/1.03      ( v1_funct_1(sK2) ),
% 1.14/1.03      inference(cnf_transformation,[],[f74]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_423,plain,
% 1.14/1.03      ( ~ v1_relat_1(sK2)
% 1.14/1.03      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_421,c_34]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1638,plain,
% 1.14/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 1.14/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_423]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_32,negated_conjecture,
% 1.14/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 1.14/1.03      inference(cnf_transformation,[],[f76]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_16,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | v1_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f61]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1911,plain,
% 1.14/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.14/1.03      | v1_relat_1(sK2) ),
% 1.14/1.03      inference(instantiation,[status(thm)],[c_16]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1915,plain,
% 1.14/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_1638,c_34,c_32,c_421,c_1911]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_26,plain,
% 1.14/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f73]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1642,plain,
% 1.14/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 1.14/1.03      | v1_funct_1(X0) != iProver_top
% 1.14/1.03      | v1_relat_1(X0) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3766,plain,
% 1.14/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 1.14/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.14/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_1915,c_1642]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1641,plain,
% 1.14/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_19,plain,
% 1.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f64]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1643,plain,
% 1.14/1.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.14/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3053,plain,
% 1.14/1.03      ( k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
% 1.14/1.03      inference(superposition,[status(thm)],[c_1641,c_1643]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_30,negated_conjecture,
% 1.14/1.03      ( k2_relset_1(sK0,sK1,sK2) = sK1 ),
% 1.14/1.03      inference(cnf_transformation,[],[f78]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3065,plain,
% 1.14/1.03      ( k2_relat_1(sK2) = sK1 ),
% 1.14/1.03      inference(light_normalisation,[status(thm)],[c_3053,c_30]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_15,plain,
% 1.14/1.03      ( ~ v2_funct_1(X0)
% 1.14/1.03      | ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 1.14/1.03      inference(cnf_transformation,[],[f59]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_406,plain,
% 1.14/1.03      ( ~ v1_funct_1(X0)
% 1.14/1.03      | ~ v1_relat_1(X0)
% 1.14/1.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 1.14/1.03      | sK2 != X0 ),
% 1.14/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_407,plain,
% 1.14/1.03      ( ~ v1_funct_1(sK2)
% 1.14/1.03      | ~ v1_relat_1(sK2)
% 1.14/1.03      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.14/1.03      inference(unflattening,[status(thm)],[c_406]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_409,plain,
% 1.14/1.03      ( ~ v1_relat_1(sK2)
% 1.14/1.03      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_407,c_34]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1639,plain,
% 1.14/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 1.14/1.03      | v1_relat_1(sK2) != iProver_top ),
% 1.14/1.03      inference(predicate_to_equality,[status(thm)],[c_409]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_1919,plain,
% 1.14/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.14/1.03      inference(global_propositional_subsumption,
% 1.14/1.03                [status(thm)],
% 1.14/1.03                [c_1639,c_34,c_32,c_407,c_1911]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3080,plain,
% 1.14/1.03      ( k1_relat_1(k2_funct_1(sK2)) = sK1 ),
% 1.14/1.03      inference(demodulation,[status(thm)],[c_3065,c_1919]) ).
% 1.14/1.03  
% 1.14/1.03  cnf(c_3786,plain,
% 1.14/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top
% 1.14/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.14/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.04      inference(light_normalisation,[status(thm)],[c_3766,c_3080]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_35,plain,
% 1.14/1.04      ( v1_funct_1(sK2) = iProver_top ),
% 1.14/1.04      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_37,plain,
% 1.14/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 1.14/1.04      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_12,plain,
% 1.14/1.04      ( ~ v1_funct_1(X0)
% 1.14/1.04      | v1_funct_1(k2_funct_1(X0))
% 1.14/1.04      | ~ v1_relat_1(X0) ),
% 1.14/1.04      inference(cnf_transformation,[],[f58]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1890,plain,
% 1.14/1.04      ( v1_funct_1(k2_funct_1(sK2))
% 1.14/1.04      | ~ v1_funct_1(sK2)
% 1.14/1.04      | ~ v1_relat_1(sK2) ),
% 1.14/1.04      inference(instantiation,[status(thm)],[c_12]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1891,plain,
% 1.14/1.04      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.14/1.04      | v1_funct_1(sK2) != iProver_top
% 1.14/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.14/1.04      inference(predicate_to_equality,[status(thm)],[c_1890]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_13,plain,
% 1.14/1.04      ( ~ v1_funct_1(X0)
% 1.14/1.04      | ~ v1_relat_1(X0)
% 1.14/1.04      | v1_relat_1(k2_funct_1(X0)) ),
% 1.14/1.04      inference(cnf_transformation,[],[f57]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1893,plain,
% 1.14/1.04      ( ~ v1_funct_1(sK2)
% 1.14/1.04      | v1_relat_1(k2_funct_1(sK2))
% 1.14/1.04      | ~ v1_relat_1(sK2) ),
% 1.14/1.04      inference(instantiation,[status(thm)],[c_13]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1894,plain,
% 1.14/1.04      ( v1_funct_1(sK2) != iProver_top
% 1.14/1.04      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 1.14/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.14/1.04      inference(predicate_to_equality,[status(thm)],[c_1893]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1912,plain,
% 1.14/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 1.14/1.04      | v1_relat_1(sK2) = iProver_top ),
% 1.14/1.04      inference(predicate_to_equality,[status(thm)],[c_1911]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_5017,plain,
% 1.14/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) = iProver_top ),
% 1.14/1.04      inference(global_propositional_subsumption,
% 1.14/1.04                [status(thm)],
% 1.14/1.04                [c_3786,c_35,c_37,c_1891,c_1894,c_1912]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_25,plain,
% 1.14/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.14/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.04      | k1_relset_1(X1,X2,X0) = X1
% 1.14/1.04      | k1_xboole_0 = X2 ),
% 1.14/1.04      inference(cnf_transformation,[],[f65]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_33,negated_conjecture,
% 1.14/1.04      ( v1_funct_2(sK2,sK0,sK1) ),
% 1.14/1.04      inference(cnf_transformation,[],[f75]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_636,plain,
% 1.14/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.04      | k1_relset_1(X1,X2,X0) = X1
% 1.14/1.04      | sK0 != X1
% 1.14/1.04      | sK1 != X2
% 1.14/1.04      | sK2 != X0
% 1.14/1.04      | k1_xboole_0 = X2 ),
% 1.14/1.04      inference(resolution_lifted,[status(thm)],[c_25,c_33]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_637,plain,
% 1.14/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 1.14/1.04      | k1_relset_1(sK0,sK1,sK2) = sK0
% 1.14/1.04      | k1_xboole_0 = sK1 ),
% 1.14/1.04      inference(unflattening,[status(thm)],[c_636]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_639,plain,
% 1.14/1.04      ( k1_relset_1(sK0,sK1,sK2) = sK0 | k1_xboole_0 = sK1 ),
% 1.14/1.04      inference(global_propositional_subsumption,
% 1.14/1.04                [status(thm)],
% 1.14/1.04                [c_637,c_32]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_18,plain,
% 1.14/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.14/1.04      inference(cnf_transformation,[],[f63]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1644,plain,
% 1.14/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.14/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.14/1.04      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_3879,plain,
% 1.14/1.04      ( k1_relset_1(sK0,sK1,sK2) = k1_relat_1(sK2) ),
% 1.14/1.04      inference(superposition,[status(thm)],[c_1641,c_1644]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4014,plain,
% 1.14/1.04      ( k1_relat_1(sK2) = sK0 | sK1 = k1_xboole_0 ),
% 1.14/1.04      inference(superposition,[status(thm)],[c_639,c_3879]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_27,plain,
% 1.14/1.04      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 1.14/1.04      | ~ v1_funct_1(X0)
% 1.14/1.04      | ~ v1_relat_1(X0) ),
% 1.14/1.04      inference(cnf_transformation,[],[f72]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_29,negated_conjecture,
% 1.14/1.04      ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
% 1.14/1.04      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.04      | ~ v1_funct_1(k2_funct_1(sK2)) ),
% 1.14/1.04      inference(cnf_transformation,[],[f79]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_647,plain,
% 1.14/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.04      | ~ v1_funct_1(X0)
% 1.14/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.04      | ~ v1_relat_1(X0)
% 1.14/1.04      | k2_funct_1(sK2) != X0
% 1.14/1.04      | k2_relat_1(X0) != sK0
% 1.14/1.04      | k1_relat_1(X0) != sK1 ),
% 1.14/1.04      inference(resolution_lifted,[status(thm)],[c_27,c_29]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_648,plain,
% 1.14/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.04      | ~ v1_relat_1(k2_funct_1(sK2))
% 1.14/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 1.14/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 1.14/1.04      inference(unflattening,[status(thm)],[c_647]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_660,plain,
% 1.14/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0
% 1.14/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1 ),
% 1.14/1.04      inference(forward_subsumption_resolution,
% 1.14/1.04                [status(thm)],
% 1.14/1.04                [c_648,c_16]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1628,plain,
% 1.14/1.04      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 1.14/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.04      inference(predicate_to_equality,[status(thm)],[c_660]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_649,plain,
% 1.14/1.04      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 1.14/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.14/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.04      inference(predicate_to_equality,[status(thm)],[c_648]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1988,plain,
% 1.14/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.14/1.04      | k2_relat_1(k2_funct_1(sK2)) != sK0 ),
% 1.14/1.04      inference(global_propositional_subsumption,
% 1.14/1.04                [status(thm)],
% 1.14/1.04                [c_1628,c_35,c_37,c_649,c_1891,c_1894,c_1912]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1989,plain,
% 1.14/1.04      ( k2_relat_1(k2_funct_1(sK2)) != sK0
% 1.14/1.04      | k1_relat_1(k2_funct_1(sK2)) != sK1
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.04      inference(renaming,[status(thm)],[c_1988]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1992,plain,
% 1.14/1.04      ( k2_relat_1(sK2) != sK1
% 1.14/1.04      | k1_relat_1(sK2) != sK0
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.04      inference(light_normalisation,[status(thm)],[c_1989,c_1915,c_1919]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_3079,plain,
% 1.14/1.04      ( k1_relat_1(sK2) != sK0
% 1.14/1.04      | sK1 != sK1
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.04      inference(demodulation,[status(thm)],[c_3065,c_1992]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_3083,plain,
% 1.14/1.04      ( k1_relat_1(sK2) != sK0
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.04      inference(equality_resolution_simp,[status(thm)],[c_3079]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4094,plain,
% 1.14/1.04      ( sK1 = k1_xboole_0
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top ),
% 1.14/1.04      inference(superposition,[status(thm)],[c_4014,c_3083]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_7,plain,
% 1.14/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.14/1.04      inference(cnf_transformation,[],[f53]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1908,plain,
% 1.14/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.14/1.04      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 1.14/1.04      inference(instantiation,[status(thm)],[c_7]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_2381,plain,
% 1.14/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.04      | ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) ),
% 1.14/1.04      inference(instantiation,[status(thm)],[c_1908]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_2382,plain,
% 1.14/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) = iProver_top
% 1.14/1.04      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) != iProver_top ),
% 1.14/1.04      inference(predicate_to_equality,[status(thm)],[c_2381]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_11,plain,
% 1.14/1.04      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 1.14/1.04      | ~ v1_relat_1(X0) ),
% 1.14/1.04      inference(cnf_transformation,[],[f56]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1648,plain,
% 1.14/1.04      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 1.14/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.14/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_3226,plain,
% 1.14/1.04      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))) = iProver_top
% 1.14/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.04      inference(superposition,[status(thm)],[c_3080,c_1648]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_3227,plain,
% 1.14/1.04      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top
% 1.14/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.04      inference(light_normalisation,[status(thm)],[c_3226,c_1915]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_3675,plain,
% 1.14/1.04      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,k1_relat_1(sK2))) = iProver_top ),
% 1.14/1.04      inference(global_propositional_subsumption,
% 1.14/1.04                [status(thm)],
% 1.14/1.04                [c_3227,c_35,c_37,c_1894,c_1912]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4093,plain,
% 1.14/1.04      ( sK1 = k1_xboole_0
% 1.14/1.04      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(sK1,sK0)) = iProver_top ),
% 1.14/1.04      inference(superposition,[status(thm)],[c_4014,c_3675]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4202,plain,
% 1.14/1.04      ( sK1 = k1_xboole_0 ),
% 1.14/1.04      inference(global_propositional_subsumption,
% 1.14/1.04                [status(thm)],
% 1.14/1.04                [c_4094,c_2382,c_4093]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_5021,plain,
% 1.14/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top ),
% 1.14/1.04      inference(light_normalisation,[status(thm)],[c_5017,c_4202]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4,plain,
% 1.14/1.04      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 1.14/1.04      inference(cnf_transformation,[],[f83]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_5022,plain,
% 1.14/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 1.14/1.04      inference(demodulation,[status(thm)],[c_5021,c_4]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_3881,plain,
% 1.14/1.04      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 1.14/1.04      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.14/1.04      inference(superposition,[status(thm)],[c_4,c_1644]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_5028,plain,
% 1.14/1.04      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 1.14/1.04      inference(superposition,[status(thm)],[c_5022,c_3881]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4212,plain,
% 1.14/1.04      ( k1_relat_1(k2_funct_1(sK2)) = k1_xboole_0 ),
% 1.14/1.04      inference(demodulation,[status(thm)],[c_4202,c_3080]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_5042,plain,
% 1.14/1.04      ( k1_relset_1(k1_xboole_0,X0,k2_funct_1(sK2)) = k1_xboole_0 ),
% 1.14/1.04      inference(light_normalisation,[status(thm)],[c_5028,c_4212]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_22,plain,
% 1.14/1.04      ( v1_funct_2(X0,k1_xboole_0,X1)
% 1.14/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.14/1.04      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 1.14/1.04      inference(cnf_transformation,[],[f87]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_564,plain,
% 1.14/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 1.14/1.04      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.04      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 1.14/1.04      | k2_funct_1(sK2) != X0
% 1.14/1.04      | sK0 != X1
% 1.14/1.04      | sK1 != k1_xboole_0 ),
% 1.14/1.04      inference(resolution_lifted,[status(thm)],[c_22,c_29]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_565,plain,
% 1.14/1.04      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
% 1.14/1.04      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
% 1.14/1.04      | ~ v1_funct_1(k2_funct_1(sK2))
% 1.14/1.04      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 1.14/1.04      | sK1 != k1_xboole_0 ),
% 1.14/1.04      inference(unflattening,[status(thm)],[c_564]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1632,plain,
% 1.14/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 1.14/1.04      | sK1 != k1_xboole_0
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 1.14/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.04      inference(predicate_to_equality,[status(thm)],[c_565]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_1816,plain,
% 1.14/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 1.14/1.04      | sK1 != k1_xboole_0
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.14/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.04      inference(demodulation,[status(thm)],[c_1632,c_4]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_2187,plain,
% 1.14/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.04      | sK1 != k1_xboole_0
% 1.14/1.04      | k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 1.14/1.04      inference(global_propositional_subsumption,
% 1.14/1.04                [status(thm)],
% 1.14/1.04                [c_1816,c_35,c_37,c_1891,c_1912]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_2188,plain,
% 1.14/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 1.14/1.04      | sK1 != k1_xboole_0
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) != iProver_top
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.14/1.04      inference(renaming,[status(thm)],[c_2187]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4216,plain,
% 1.14/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 1.14/1.04      | k1_xboole_0 != k1_xboole_0
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.14/1.04      inference(demodulation,[status(thm)],[c_4202,c_2188]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4249,plain,
% 1.14/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) != iProver_top
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.14/1.04      inference(equality_resolution_simp,[status(thm)],[c_4216]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4253,plain,
% 1.14/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0
% 1.14/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 1.14/1.04      inference(demodulation,[status(thm)],[c_4249,c_4]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4752,plain,
% 1.14/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 1.14/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.14/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.04      inference(superposition,[status(thm)],[c_4212,c_1642]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4761,plain,
% 1.14/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) = iProver_top
% 1.14/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.14/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.04      inference(light_normalisation,[status(thm)],[c_4752,c_1915]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_4762,plain,
% 1.14/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 1.14/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.14/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 1.14/1.04      inference(demodulation,[status(thm)],[c_4761,c_4]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_5227,plain,
% 1.14/1.04      ( k1_relset_1(k1_xboole_0,sK0,k2_funct_1(sK2)) != k1_xboole_0 ),
% 1.14/1.04      inference(global_propositional_subsumption,
% 1.14/1.04                [status(thm)],
% 1.14/1.04                [c_4253,c_35,c_37,c_1891,c_1894,c_1912,c_4762]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_5546,plain,
% 1.14/1.04      ( k1_xboole_0 != k1_xboole_0 ),
% 1.14/1.04      inference(demodulation,[status(thm)],[c_5042,c_5227]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_108,plain,
% 1.14/1.04      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 1.14/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_5,plain,
% 1.14/1.04      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 1.14/1.04      | k1_xboole_0 = X1
% 1.14/1.04      | k1_xboole_0 = X0 ),
% 1.14/1.04      inference(cnf_transformation,[],[f48]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(c_107,plain,
% 1.14/1.04      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 1.14/1.04      | k1_xboole_0 = k1_xboole_0 ),
% 1.14/1.04      inference(instantiation,[status(thm)],[c_5]) ).
% 1.14/1.04  
% 1.14/1.04  cnf(contradiction,plain,
% 1.14/1.04      ( $false ),
% 1.14/1.04      inference(minisat,[status(thm)],[c_5546,c_108,c_107]) ).
% 1.14/1.04  
% 1.14/1.04  
% 1.14/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.14/1.04  
% 1.14/1.04  ------                               Statistics
% 1.14/1.04  
% 1.14/1.04  ------ General
% 1.14/1.04  
% 1.14/1.04  abstr_ref_over_cycles:                  0
% 1.14/1.04  abstr_ref_under_cycles:                 0
% 1.14/1.04  gc_basic_clause_elim:                   0
% 1.14/1.04  forced_gc_time:                         0
% 1.14/1.04  parsing_time:                           0.02
% 1.14/1.04  unif_index_cands_time:                  0.
% 1.14/1.04  unif_index_add_time:                    0.
% 1.14/1.04  orderings_time:                         0.
% 1.14/1.04  out_proof_time:                         0.01
% 1.14/1.04  total_time:                             0.158
% 1.14/1.04  num_of_symbols:                         49
% 1.14/1.04  num_of_terms:                           4419
% 1.14/1.04  
% 1.14/1.04  ------ Preprocessing
% 1.14/1.04  
% 1.14/1.04  num_of_splits:                          0
% 1.14/1.04  num_of_split_atoms:                     0
% 1.14/1.04  num_of_reused_defs:                     0
% 1.14/1.04  num_eq_ax_congr_red:                    4
% 1.14/1.04  num_of_sem_filtered_clauses:            1
% 1.14/1.04  num_of_subtypes:                        0
% 1.14/1.04  monotx_restored_types:                  0
% 1.14/1.04  sat_num_of_epr_types:                   0
% 1.14/1.04  sat_num_of_non_cyclic_types:            0
% 1.14/1.04  sat_guarded_non_collapsed_types:        0
% 1.14/1.04  num_pure_diseq_elim:                    0
% 1.14/1.04  simp_replaced_by:                       0
% 1.14/1.04  res_preprocessed:                       156
% 1.14/1.04  prep_upred:                             0
% 1.14/1.04  prep_unflattend:                        43
% 1.14/1.04  smt_new_axioms:                         0
% 1.14/1.04  pred_elim_cands:                        4
% 1.14/1.04  pred_elim:                              3
% 1.14/1.04  pred_elim_cl:                           1
% 1.14/1.04  pred_elim_cycles:                       5
% 1.14/1.04  merged_defs:                            8
% 1.14/1.04  merged_defs_ncl:                        0
% 1.14/1.04  bin_hyper_res:                          8
% 1.14/1.04  prep_cycles:                            4
% 1.14/1.04  pred_elim_time:                         0.005
% 1.14/1.04  splitting_time:                         0.
% 1.14/1.04  sem_filter_time:                        0.
% 1.14/1.04  monotx_time:                            0.
% 1.14/1.04  subtype_inf_time:                       0.
% 1.14/1.04  
% 1.14/1.04  ------ Problem properties
% 1.14/1.04  
% 1.14/1.04  clauses:                                32
% 1.14/1.04  conjectures:                            3
% 1.14/1.04  epr:                                    3
% 1.14/1.04  horn:                                   27
% 1.14/1.04  ground:                                 13
% 1.14/1.04  unary:                                  7
% 1.14/1.04  binary:                                 10
% 1.14/1.04  lits:                                   84
% 1.14/1.04  lits_eq:                                36
% 1.14/1.04  fd_pure:                                0
% 1.14/1.04  fd_pseudo:                              0
% 1.14/1.04  fd_cond:                                2
% 1.14/1.04  fd_pseudo_cond:                         1
% 1.14/1.04  ac_symbols:                             0
% 1.14/1.04  
% 1.14/1.04  ------ Propositional Solver
% 1.14/1.04  
% 1.14/1.04  prop_solver_calls:                      27
% 1.14/1.04  prop_fast_solver_calls:                 1070
% 1.14/1.04  smt_solver_calls:                       0
% 1.14/1.04  smt_fast_solver_calls:                  0
% 1.14/1.04  prop_num_of_clauses:                    1844
% 1.14/1.04  prop_preprocess_simplified:             6575
% 1.14/1.04  prop_fo_subsumed:                       25
% 1.14/1.04  prop_solver_time:                       0.
% 1.14/1.04  smt_solver_time:                        0.
% 1.14/1.04  smt_fast_solver_time:                   0.
% 1.14/1.04  prop_fast_solver_time:                  0.
% 1.14/1.04  prop_unsat_core_time:                   0.
% 1.14/1.04  
% 1.14/1.04  ------ QBF
% 1.14/1.04  
% 1.14/1.04  qbf_q_res:                              0
% 1.14/1.04  qbf_num_tautologies:                    0
% 1.14/1.04  qbf_prep_cycles:                        0
% 1.14/1.04  
% 1.14/1.04  ------ BMC1
% 1.14/1.04  
% 1.14/1.04  bmc1_current_bound:                     -1
% 1.14/1.04  bmc1_last_solved_bound:                 -1
% 1.14/1.04  bmc1_unsat_core_size:                   -1
% 1.14/1.04  bmc1_unsat_core_parents_size:           -1
% 1.14/1.04  bmc1_merge_next_fun:                    0
% 1.14/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.14/1.04  
% 1.14/1.04  ------ Instantiation
% 1.14/1.04  
% 1.14/1.04  inst_num_of_clauses:                    728
% 1.14/1.04  inst_num_in_passive:                    23
% 1.14/1.04  inst_num_in_active:                     353
% 1.14/1.04  inst_num_in_unprocessed:                352
% 1.14/1.04  inst_num_of_loops:                      400
% 1.14/1.04  inst_num_of_learning_restarts:          0
% 1.14/1.04  inst_num_moves_active_passive:          45
% 1.14/1.04  inst_lit_activity:                      0
% 1.14/1.04  inst_lit_activity_moves:                0
% 1.14/1.04  inst_num_tautologies:                   0
% 1.14/1.04  inst_num_prop_implied:                  0
% 1.14/1.04  inst_num_existing_simplified:           0
% 1.14/1.04  inst_num_eq_res_simplified:             0
% 1.14/1.04  inst_num_child_elim:                    0
% 1.14/1.04  inst_num_of_dismatching_blockings:      160
% 1.14/1.04  inst_num_of_non_proper_insts:           702
% 1.14/1.04  inst_num_of_duplicates:                 0
% 1.14/1.04  inst_inst_num_from_inst_to_res:         0
% 1.14/1.04  inst_dismatching_checking_time:         0.
% 1.14/1.04  
% 1.14/1.04  ------ Resolution
% 1.14/1.04  
% 1.14/1.04  res_num_of_clauses:                     0
% 1.14/1.04  res_num_in_passive:                     0
% 1.14/1.04  res_num_in_active:                      0
% 1.14/1.04  res_num_of_loops:                       160
% 1.14/1.04  res_forward_subset_subsumed:            34
% 1.14/1.04  res_backward_subset_subsumed:           2
% 1.14/1.04  res_forward_subsumed:                   0
% 1.14/1.04  res_backward_subsumed:                  0
% 1.14/1.04  res_forward_subsumption_resolution:     4
% 1.14/1.04  res_backward_subsumption_resolution:    0
% 1.14/1.04  res_clause_to_clause_subsumption:       278
% 1.14/1.04  res_orphan_elimination:                 0
% 1.14/1.04  res_tautology_del:                      63
% 1.14/1.04  res_num_eq_res_simplified:              0
% 1.14/1.04  res_num_sel_changes:                    0
% 1.14/1.04  res_moves_from_active_to_pass:          0
% 1.14/1.04  
% 1.14/1.04  ------ Superposition
% 1.14/1.04  
% 1.14/1.04  sup_time_total:                         0.
% 1.14/1.04  sup_time_generating:                    0.
% 1.14/1.04  sup_time_sim_full:                      0.
% 1.14/1.04  sup_time_sim_immed:                     0.
% 1.14/1.04  
% 1.14/1.04  sup_num_of_clauses:                     88
% 1.14/1.04  sup_num_in_active:                      54
% 1.14/1.04  sup_num_in_passive:                     34
% 1.14/1.04  sup_num_of_loops:                       78
% 1.14/1.04  sup_fw_superposition:                   63
% 1.14/1.04  sup_bw_superposition:                   48
% 1.14/1.04  sup_immediate_simplified:               46
% 1.14/1.04  sup_given_eliminated:                   0
% 1.14/1.04  comparisons_done:                       0
% 1.14/1.04  comparisons_avoided:                    11
% 1.14/1.04  
% 1.14/1.04  ------ Simplifications
% 1.14/1.04  
% 1.14/1.04  
% 1.14/1.04  sim_fw_subset_subsumed:                 9
% 1.14/1.04  sim_bw_subset_subsumed:                 3
% 1.14/1.04  sim_fw_subsumed:                        8
% 1.14/1.04  sim_bw_subsumed:                        2
% 1.14/1.04  sim_fw_subsumption_res:                 2
% 1.14/1.04  sim_bw_subsumption_res:                 0
% 1.14/1.04  sim_tautology_del:                      3
% 1.14/1.04  sim_eq_tautology_del:                   4
% 1.14/1.04  sim_eq_res_simp:                        3
% 1.14/1.04  sim_fw_demodulated:                     19
% 1.14/1.04  sim_bw_demodulated:                     23
% 1.14/1.04  sim_light_normalised:                   21
% 1.14/1.04  sim_joinable_taut:                      0
% 1.14/1.04  sim_joinable_simp:                      0
% 1.14/1.04  sim_ac_normalised:                      0
% 1.14/1.04  sim_smt_subsumption:                    0
% 1.14/1.04  
%------------------------------------------------------------------------------
