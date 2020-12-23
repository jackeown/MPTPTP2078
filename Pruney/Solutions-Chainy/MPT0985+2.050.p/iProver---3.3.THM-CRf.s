%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:29 EST 2020

% Result     : Theorem 3.90s
% Output     : CNFRefutation 3.90s
% Verified   : 
% Statistics : Number of formulae       :  307 (3403 expanded)
%              Number of clauses        :  180 (1133 expanded)
%              Number of leaves         :   34 ( 651 expanded)
%              Depth                    :   25
%              Number of atoms          :  915 (16604 expanded)
%              Number of equality atoms :  409 (3571 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f32,conjecture,(
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

fof(f33,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f67,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f68,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f67])).

fof(f80,plain,
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

fof(f81,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
      | ~ v1_funct_1(k2_funct_1(sK3)) )
    & k2_relset_1(sK1,sK2,sK3) = sK2
    & v2_funct_1(sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK3,sK1,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f68,f80])).

fof(f140,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f21,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f53,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f116,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f139,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f81])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f141,plain,(
    k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f81])).

fof(f137,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f75])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f156,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f90])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f93,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f73])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f154,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f86])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f108,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f117,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f30,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f64,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f63])).

fof(f129,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f79,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f102,plain,(
    ! [X0] :
      ( k1_xboole_0 = k1_relat_1(X0)
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f130,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_tarski(k2_relat_1(X3),X1)
       => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f59])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ r1_tarski(k2_relat_1(X3),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f142,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f81])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(X1,X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        & v1_funct_2(X3,X0,X2)
        & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f65])).

fof(f133,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_2(X3,X0,X2)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f69])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f70,f71])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f85,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f76])).

fof(f155,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f91])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f138,plain,(
    v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f81])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f46])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f41,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f40])).

fof(f100,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f127,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f29])).

fof(f146,plain,(
    k1_xboole_0 = k6_partfun1(k1_xboole_0) ),
    inference(definition_unfolding,[],[f106,f127])).

fof(f17,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f111,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f150,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f111,f127])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f105,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f145,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f105,f127])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f104,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f143,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f104,f127])).

fof(f22,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f152,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f118,f127])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f151,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f115,f127])).

fof(f103,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f144,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f103,f127])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f110,plain,(
    ! [X0] : v1_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f147,plain,(
    ! [X0] : v1_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f110,f127])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f61])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f28,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f125,plain,(
    ! [X0] : v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f28])).

cnf(c_56,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_2437,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_35,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_2449,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_9958,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_2449])).

cnf(c_57,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_2436,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_39,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2447,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_7836,plain,
    ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2436,c_2447])).

cnf(c_55,negated_conjecture,
    ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_7882,plain,
    ( k2_relat_1(sK3) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_7836,c_55])).

cnf(c_9970,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9958,c_7882])).

cnf(c_59,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_60,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_62,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2867,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_37])).

cnf(c_2868,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2867])).

cnf(c_10823,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9970,c_60,c_62,c_2868])).

cnf(c_8,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f156])).

cnf(c_10,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_2467,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_38,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_14,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_691,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_38,c_14])).

cnf(c_695,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_691,c_37])).

cnf(c_696,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_695])).

cnf(c_2430,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_4675,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_2467,c_2430])).

cnf(c_17180,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_4675])).

cnf(c_17301,plain,
    ( r1_tarski(k2_funct_1(sK3),k1_xboole_0) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_10823,c_17180])).

cnf(c_9,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_170,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_171,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_172,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_174,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_172])).

cnf(c_25,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2825,plain,
    ( v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_26,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2833,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2834,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2833])).

cnf(c_2940,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(instantiation,[status(thm)],[c_696])).

cnf(c_1451,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3362,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_4725,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_3362])).

cnf(c_1450,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_4726,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1450])).

cnf(c_34,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_2450,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_11497,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2437,c_2450])).

cnf(c_840,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_56])).

cnf(c_841,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_840])).

cnf(c_11853,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11497,c_59,c_57,c_841,c_2867])).

cnf(c_46,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_2443,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_11858,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11853,c_2443])).

cnf(c_11869,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11858,c_10823])).

cnf(c_11888,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11869])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_2461,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_relat_1(X0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_11857,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11853,c_2461])).

cnf(c_11876,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | sK2 = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11857,c_10823])).

cnf(c_45,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_2444,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_11856,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_11853,c_2444])).

cnf(c_11883,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_11856,c_10823])).

cnf(c_11890,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | ~ v1_relat_1(k2_funct_1(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11883])).

cnf(c_2826,plain,
    ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2825])).

cnf(c_13323,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_11883,c_60,c_62,c_2826,c_2834,c_2868])).

cnf(c_40,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(k2_relat_1(X0),X3) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_2446,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_13329,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13323,c_2446])).

cnf(c_13364,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13329,c_11853])).

cnf(c_54,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_2438,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_64,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_2873,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2438,c_60,c_62,c_64,c_2826,c_2868])).

cnf(c_2874,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2873])).

cnf(c_13949,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_13364,c_2874])).

cnf(c_14004,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_13949])).

cnf(c_1452,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_15558,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,X2)
    | X2 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1452])).

cnf(c_15559,plain,
    ( X0 != X1
    | sK2 != X2
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK2,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15558])).

cnf(c_15561,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_15559])).

cnf(c_51,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X0,X1,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f133])).

cnf(c_6339,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X0,X1,k1_relat_1(sK3))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relat_1(sK3))))
    | ~ r1_tarski(k1_relat_1(sK3),X2)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_16851,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
    | v1_funct_2(k2_funct_1(sK3),sK2,sK1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
    | ~ r1_tarski(k1_relat_1(sK3),sK1)
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_6339])).

cnf(c_17627,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17301,c_59,c_60,c_57,c_62,c_170,c_171,c_174,c_2825,c_2833,c_2834,c_2867,c_2868,c_2940,c_4725,c_4726,c_11888,c_11876,c_11890,c_14004,c_15561,c_16851])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_2471,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_403,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_10])).

cnf(c_404,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_403])).

cnf(c_489,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_12,c_404])).

cnf(c_655,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_489])).

cnf(c_656,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_2432,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_656])).

cnf(c_5129,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2471,c_2432])).

cnf(c_17644,plain,
    ( r1_tarski(sK2,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_17627,c_5129])).

cnf(c_7,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f155])).

cnf(c_49,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ r1_tarski(X2,X3)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f135])).

cnf(c_2441,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_5876,plain,
    ( sK2 = k1_xboole_0
    | v1_funct_2(sK3,sK1,sK2) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2436,c_2441])).

cnf(c_58,negated_conjecture,
    ( v1_funct_2(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_61,plain,
    ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_6141,plain,
    ( r1_tarski(sK2,X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5876,c_60,c_61])).

cnf(c_6142,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6141])).

cnf(c_6150,plain,
    ( sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_6142])).

cnf(c_2956,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_7,c_2430])).

cnf(c_6235,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6150,c_2956])).

cnf(c_31,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2453,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_13731,plain,
    ( k9_relat_1(sK3,k10_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,sK2) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7882,c_2453])).

cnf(c_13861,plain,
    ( k9_relat_1(sK3,k10_relat_1(sK3,X0)) = X0
    | r1_tarski(X0,sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13731,c_60,c_62,c_2868])).

cnf(c_13870,plain,
    ( k9_relat_1(sK3,k10_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3)
    | sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6235,c_13861])).

cnf(c_3272,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0)
    | r1_tarski(X0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3278,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) = iProver_top
    | r1_tarski(X0,k1_relat_1(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3272])).

cnf(c_3280,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3278])).

cnf(c_6609,plain,
    ( ~ r2_hidden(sK0(X0,k1_relat_1(sK3)),X0)
    | ~ r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_656])).

cnf(c_6615,plain,
    ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) != iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6609])).

cnf(c_6617,plain,
    ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_6615])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_2469,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_11649,plain,
    ( k1_relat_1(sK3) = X0
    | sK2 = k1_xboole_0
    | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6235,c_2469])).

cnf(c_11717,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_11649])).

cnf(c_11889,plain,
    ( ~ v1_relat_1(k2_funct_1(sK3))
    | k1_relat_1(sK3) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11876])).

cnf(c_13117,plain,
    ( sK2 = k1_xboole_0
    | k1_relat_1(sK3) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11876,c_60,c_62,c_2834,c_2868])).

cnf(c_13118,plain,
    ( k1_relat_1(sK3) != k1_xboole_0
    | sK2 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_13117])).

cnf(c_15913,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13870,c_60,c_62,c_174,c_2834,c_2868,c_3280,c_6617,c_11717,c_11876])).

cnf(c_17671,plain,
    ( sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_17644,c_15913])).

cnf(c_2941,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2940])).

cnf(c_14011,plain,
    ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_13949,c_62,c_2941])).

cnf(c_17786,plain,
    ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_17671,c_14011])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2463,plain,
    ( k2_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8096,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7882,c_2463])).

cnf(c_8570,plain,
    ( sK3 = k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8096,c_62,c_2868])).

cnf(c_8571,plain,
    ( sK2 != k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_8570])).

cnf(c_17812,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_17671,c_8571])).

cnf(c_17849,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_17812])).

cnf(c_17948,plain,
    ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17786,c_17849])).

cnf(c_24,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f146])).

cnf(c_30,plain,
    ( v1_relat_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_2455,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
    inference(cnf_transformation,[],[f145])).

cnf(c_2459,plain,
    ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_4091,plain,
    ( k5_relat_1(k6_partfun1(X0),k6_partfun1(k2_relat_1(k6_partfun1(X0)))) = k6_partfun1(X0) ),
    inference(superposition,[status(thm)],[c_2455,c_2459])).

cnf(c_21,plain,
    ( k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f143])).

cnf(c_4097,plain,
    ( k5_relat_1(k6_partfun1(X0),k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(light_normalisation,[status(thm)],[c_4091,c_21])).

cnf(c_36,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_33,plain,
    ( v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f151])).

cnf(c_308,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_36,c_33])).

cnf(c_2433,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_308])).

cnf(c_4231,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
    | k6_partfun1(k1_relat_1(k6_partfun1(X0))) != k6_partfun1(X0)
    | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0))
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4097,c_2433])).

cnf(c_22,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f144])).

cnf(c_4237,plain,
    ( X0 != X0
    | k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
    | k6_partfun1(X0) != k6_partfun1(X0)
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4231,c_21,c_22])).

cnf(c_4238,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
    | v1_funct_1(k6_partfun1(X0)) != iProver_top
    | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4237])).

cnf(c_116,plain,
    ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_27,plain,
    ( v1_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_123,plain,
    ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_15392,plain,
    ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4238,c_116,c_123])).

cnf(c_15412,plain,
    ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_24,c_15392])).

cnf(c_15416,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_15412,c_24])).

cnf(c_17950,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17948,c_15416])).

cnf(c_41,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_44,plain,
    ( v1_partfun1(k6_partfun1(X0),X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_670,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | X3 != X1
    | k6_partfun1(X3) != X0 ),
    inference(resolution_lifted,[status(thm)],[c_41,c_44])).

cnf(c_671,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1)
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(k6_partfun1(X0)) ),
    inference(unflattening,[status(thm)],[c_670])).

cnf(c_675,plain,
    ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_2(k6_partfun1(X0),X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_671,c_27])).

cnf(c_676,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1)
    | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(renaming,[status(thm)],[c_675])).

cnf(c_2431,plain,
    ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
    | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_3492,plain,
    ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_8,c_2431])).

cnf(c_3495,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3492,c_24])).

cnf(c_167,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_169,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_167])).

cnf(c_6061,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3495,c_169,c_174])).

cnf(c_18491,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_17950,c_6061])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:03:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.90/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.90/0.97  
% 3.90/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.90/0.97  
% 3.90/0.97  ------  iProver source info
% 3.90/0.97  
% 3.90/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.90/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.90/0.97  git: non_committed_changes: false
% 3.90/0.97  git: last_make_outside_of_git: false
% 3.90/0.97  
% 3.90/0.97  ------ 
% 3.90/0.97  
% 3.90/0.97  ------ Input Options
% 3.90/0.97  
% 3.90/0.97  --out_options                           all
% 3.90/0.97  --tptp_safe_out                         true
% 3.90/0.97  --problem_path                          ""
% 3.90/0.97  --include_path                          ""
% 3.90/0.97  --clausifier                            res/vclausify_rel
% 3.90/0.97  --clausifier_options                    --mode clausify
% 3.90/0.97  --stdin                                 false
% 3.90/0.97  --stats_out                             all
% 3.90/0.97  
% 3.90/0.97  ------ General Options
% 3.90/0.97  
% 3.90/0.97  --fof                                   false
% 3.90/0.97  --time_out_real                         305.
% 3.90/0.97  --time_out_virtual                      -1.
% 3.90/0.97  --symbol_type_check                     false
% 3.90/0.97  --clausify_out                          false
% 3.90/0.97  --sig_cnt_out                           false
% 3.90/0.98  --trig_cnt_out                          false
% 3.90/0.98  --trig_cnt_out_tolerance                1.
% 3.90/0.98  --trig_cnt_out_sk_spl                   false
% 3.90/0.98  --abstr_cl_out                          false
% 3.90/0.98  
% 3.90/0.98  ------ Global Options
% 3.90/0.98  
% 3.90/0.98  --schedule                              default
% 3.90/0.98  --add_important_lit                     false
% 3.90/0.98  --prop_solver_per_cl                    1000
% 3.90/0.98  --min_unsat_core                        false
% 3.90/0.98  --soft_assumptions                      false
% 3.90/0.98  --soft_lemma_size                       3
% 3.90/0.98  --prop_impl_unit_size                   0
% 3.90/0.98  --prop_impl_unit                        []
% 3.90/0.98  --share_sel_clauses                     true
% 3.90/0.98  --reset_solvers                         false
% 3.90/0.98  --bc_imp_inh                            [conj_cone]
% 3.90/0.98  --conj_cone_tolerance                   3.
% 3.90/0.98  --extra_neg_conj                        none
% 3.90/0.98  --large_theory_mode                     true
% 3.90/0.98  --prolific_symb_bound                   200
% 3.90/0.98  --lt_threshold                          2000
% 3.90/0.98  --clause_weak_htbl                      true
% 3.90/0.98  --gc_record_bc_elim                     false
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing Options
% 3.90/0.98  
% 3.90/0.98  --preprocessing_flag                    true
% 3.90/0.98  --time_out_prep_mult                    0.1
% 3.90/0.98  --splitting_mode                        input
% 3.90/0.98  --splitting_grd                         true
% 3.90/0.98  --splitting_cvd                         false
% 3.90/0.98  --splitting_cvd_svl                     false
% 3.90/0.98  --splitting_nvd                         32
% 3.90/0.98  --sub_typing                            true
% 3.90/0.98  --prep_gs_sim                           true
% 3.90/0.98  --prep_unflatten                        true
% 3.90/0.98  --prep_res_sim                          true
% 3.90/0.98  --prep_upred                            true
% 3.90/0.98  --prep_sem_filter                       exhaustive
% 3.90/0.98  --prep_sem_filter_out                   false
% 3.90/0.98  --pred_elim                             true
% 3.90/0.98  --res_sim_input                         true
% 3.90/0.98  --eq_ax_congr_red                       true
% 3.90/0.98  --pure_diseq_elim                       true
% 3.90/0.98  --brand_transform                       false
% 3.90/0.98  --non_eq_to_eq                          false
% 3.90/0.98  --prep_def_merge                        true
% 3.90/0.98  --prep_def_merge_prop_impl              false
% 3.90/0.98  --prep_def_merge_mbd                    true
% 3.90/0.98  --prep_def_merge_tr_red                 false
% 3.90/0.98  --prep_def_merge_tr_cl                  false
% 3.90/0.98  --smt_preprocessing                     true
% 3.90/0.98  --smt_ac_axioms                         fast
% 3.90/0.98  --preprocessed_out                      false
% 3.90/0.98  --preprocessed_stats                    false
% 3.90/0.98  
% 3.90/0.98  ------ Abstraction refinement Options
% 3.90/0.98  
% 3.90/0.98  --abstr_ref                             []
% 3.90/0.98  --abstr_ref_prep                        false
% 3.90/0.98  --abstr_ref_until_sat                   false
% 3.90/0.98  --abstr_ref_sig_restrict                funpre
% 3.90/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.90/0.98  --abstr_ref_under                       []
% 3.90/0.98  
% 3.90/0.98  ------ SAT Options
% 3.90/0.98  
% 3.90/0.98  --sat_mode                              false
% 3.90/0.98  --sat_fm_restart_options                ""
% 3.90/0.98  --sat_gr_def                            false
% 3.90/0.98  --sat_epr_types                         true
% 3.90/0.98  --sat_non_cyclic_types                  false
% 3.90/0.98  --sat_finite_models                     false
% 3.90/0.98  --sat_fm_lemmas                         false
% 3.90/0.98  --sat_fm_prep                           false
% 3.90/0.98  --sat_fm_uc_incr                        true
% 3.90/0.98  --sat_out_model                         small
% 3.90/0.98  --sat_out_clauses                       false
% 3.90/0.98  
% 3.90/0.98  ------ QBF Options
% 3.90/0.98  
% 3.90/0.98  --qbf_mode                              false
% 3.90/0.98  --qbf_elim_univ                         false
% 3.90/0.98  --qbf_dom_inst                          none
% 3.90/0.98  --qbf_dom_pre_inst                      false
% 3.90/0.98  --qbf_sk_in                             false
% 3.90/0.98  --qbf_pred_elim                         true
% 3.90/0.98  --qbf_split                             512
% 3.90/0.98  
% 3.90/0.98  ------ BMC1 Options
% 3.90/0.98  
% 3.90/0.98  --bmc1_incremental                      false
% 3.90/0.98  --bmc1_axioms                           reachable_all
% 3.90/0.98  --bmc1_min_bound                        0
% 3.90/0.98  --bmc1_max_bound                        -1
% 3.90/0.98  --bmc1_max_bound_default                -1
% 3.90/0.98  --bmc1_symbol_reachability              true
% 3.90/0.98  --bmc1_property_lemmas                  false
% 3.90/0.98  --bmc1_k_induction                      false
% 3.90/0.98  --bmc1_non_equiv_states                 false
% 3.90/0.98  --bmc1_deadlock                         false
% 3.90/0.98  --bmc1_ucm                              false
% 3.90/0.98  --bmc1_add_unsat_core                   none
% 3.90/0.98  --bmc1_unsat_core_children              false
% 3.90/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.90/0.98  --bmc1_out_stat                         full
% 3.90/0.98  --bmc1_ground_init                      false
% 3.90/0.98  --bmc1_pre_inst_next_state              false
% 3.90/0.98  --bmc1_pre_inst_state                   false
% 3.90/0.98  --bmc1_pre_inst_reach_state             false
% 3.90/0.98  --bmc1_out_unsat_core                   false
% 3.90/0.98  --bmc1_aig_witness_out                  false
% 3.90/0.98  --bmc1_verbose                          false
% 3.90/0.98  --bmc1_dump_clauses_tptp                false
% 3.90/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.90/0.98  --bmc1_dump_file                        -
% 3.90/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.90/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.90/0.98  --bmc1_ucm_extend_mode                  1
% 3.90/0.98  --bmc1_ucm_init_mode                    2
% 3.90/0.98  --bmc1_ucm_cone_mode                    none
% 3.90/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.90/0.98  --bmc1_ucm_relax_model                  4
% 3.90/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.90/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.90/0.98  --bmc1_ucm_layered_model                none
% 3.90/0.98  --bmc1_ucm_max_lemma_size               10
% 3.90/0.98  
% 3.90/0.98  ------ AIG Options
% 3.90/0.98  
% 3.90/0.98  --aig_mode                              false
% 3.90/0.98  
% 3.90/0.98  ------ Instantiation Options
% 3.90/0.98  
% 3.90/0.98  --instantiation_flag                    true
% 3.90/0.98  --inst_sos_flag                         false
% 3.90/0.98  --inst_sos_phase                        true
% 3.90/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.90/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.90/0.98  --inst_lit_sel_side                     num_symb
% 3.90/0.98  --inst_solver_per_active                1400
% 3.90/0.98  --inst_solver_calls_frac                1.
% 3.90/0.98  --inst_passive_queue_type               priority_queues
% 3.90/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.90/0.98  --inst_passive_queues_freq              [25;2]
% 3.90/0.98  --inst_dismatching                      true
% 3.90/0.98  --inst_eager_unprocessed_to_passive     true
% 3.90/0.98  --inst_prop_sim_given                   true
% 3.90/0.98  --inst_prop_sim_new                     false
% 3.90/0.98  --inst_subs_new                         false
% 3.90/0.98  --inst_eq_res_simp                      false
% 3.90/0.98  --inst_subs_given                       false
% 3.90/0.98  --inst_orphan_elimination               true
% 3.90/0.98  --inst_learning_loop_flag               true
% 3.90/0.98  --inst_learning_start                   3000
% 3.90/0.98  --inst_learning_factor                  2
% 3.90/0.98  --inst_start_prop_sim_after_learn       3
% 3.90/0.98  --inst_sel_renew                        solver
% 3.90/0.98  --inst_lit_activity_flag                true
% 3.90/0.98  --inst_restr_to_given                   false
% 3.90/0.98  --inst_activity_threshold               500
% 3.90/0.98  --inst_out_proof                        true
% 3.90/0.98  
% 3.90/0.98  ------ Resolution Options
% 3.90/0.98  
% 3.90/0.98  --resolution_flag                       true
% 3.90/0.98  --res_lit_sel                           adaptive
% 3.90/0.98  --res_lit_sel_side                      none
% 3.90/0.98  --res_ordering                          kbo
% 3.90/0.98  --res_to_prop_solver                    active
% 3.90/0.98  --res_prop_simpl_new                    false
% 3.90/0.98  --res_prop_simpl_given                  true
% 3.90/0.98  --res_passive_queue_type                priority_queues
% 3.90/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.90/0.98  --res_passive_queues_freq               [15;5]
% 3.90/0.98  --res_forward_subs                      full
% 3.90/0.98  --res_backward_subs                     full
% 3.90/0.98  --res_forward_subs_resolution           true
% 3.90/0.98  --res_backward_subs_resolution          true
% 3.90/0.98  --res_orphan_elimination                true
% 3.90/0.98  --res_time_limit                        2.
% 3.90/0.98  --res_out_proof                         true
% 3.90/0.98  
% 3.90/0.98  ------ Superposition Options
% 3.90/0.98  
% 3.90/0.98  --superposition_flag                    true
% 3.90/0.98  --sup_passive_queue_type                priority_queues
% 3.90/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.90/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.90/0.98  --demod_completeness_check              fast
% 3.90/0.98  --demod_use_ground                      true
% 3.90/0.98  --sup_to_prop_solver                    passive
% 3.90/0.98  --sup_prop_simpl_new                    true
% 3.90/0.98  --sup_prop_simpl_given                  true
% 3.90/0.98  --sup_fun_splitting                     false
% 3.90/0.98  --sup_smt_interval                      50000
% 3.90/0.98  
% 3.90/0.98  ------ Superposition Simplification Setup
% 3.90/0.98  
% 3.90/0.98  --sup_indices_passive                   []
% 3.90/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.90/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.98  --sup_full_bw                           [BwDemod]
% 3.90/0.98  --sup_immed_triv                        [TrivRules]
% 3.90/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.98  --sup_immed_bw_main                     []
% 3.90/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.90/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/0.98  
% 3.90/0.98  ------ Combination Options
% 3.90/0.98  
% 3.90/0.98  --comb_res_mult                         3
% 3.90/0.98  --comb_sup_mult                         2
% 3.90/0.98  --comb_inst_mult                        10
% 3.90/0.98  
% 3.90/0.98  ------ Debug Options
% 3.90/0.98  
% 3.90/0.98  --dbg_backtrace                         false
% 3.90/0.98  --dbg_dump_prop_clauses                 false
% 3.90/0.98  --dbg_dump_prop_clauses_file            -
% 3.90/0.98  --dbg_out_stat                          false
% 3.90/0.98  ------ Parsing...
% 3.90/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.90/0.98  ------ Proving...
% 3.90/0.98  ------ Problem Properties 
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  clauses                                 50
% 3.90/0.98  conjectures                             6
% 3.90/0.98  EPR                                     7
% 3.90/0.98  Horn                                    46
% 3.90/0.98  unary                                   15
% 3.90/0.98  binary                                  12
% 3.90/0.98  lits                                    130
% 3.90/0.98  lits eq                                 32
% 3.90/0.98  fd_pure                                 0
% 3.90/0.98  fd_pseudo                               0
% 3.90/0.98  fd_cond                                 5
% 3.90/0.98  fd_pseudo_cond                          2
% 3.90/0.98  AC symbols                              0
% 3.90/0.98  
% 3.90/0.98  ------ Schedule dynamic 5 is on 
% 3.90/0.98  
% 3.90/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  ------ 
% 3.90/0.98  Current options:
% 3.90/0.98  ------ 
% 3.90/0.98  
% 3.90/0.98  ------ Input Options
% 3.90/0.98  
% 3.90/0.98  --out_options                           all
% 3.90/0.98  --tptp_safe_out                         true
% 3.90/0.98  --problem_path                          ""
% 3.90/0.98  --include_path                          ""
% 3.90/0.98  --clausifier                            res/vclausify_rel
% 3.90/0.98  --clausifier_options                    --mode clausify
% 3.90/0.98  --stdin                                 false
% 3.90/0.98  --stats_out                             all
% 3.90/0.98  
% 3.90/0.98  ------ General Options
% 3.90/0.98  
% 3.90/0.98  --fof                                   false
% 3.90/0.98  --time_out_real                         305.
% 3.90/0.98  --time_out_virtual                      -1.
% 3.90/0.98  --symbol_type_check                     false
% 3.90/0.98  --clausify_out                          false
% 3.90/0.98  --sig_cnt_out                           false
% 3.90/0.98  --trig_cnt_out                          false
% 3.90/0.98  --trig_cnt_out_tolerance                1.
% 3.90/0.98  --trig_cnt_out_sk_spl                   false
% 3.90/0.98  --abstr_cl_out                          false
% 3.90/0.98  
% 3.90/0.98  ------ Global Options
% 3.90/0.98  
% 3.90/0.98  --schedule                              default
% 3.90/0.98  --add_important_lit                     false
% 3.90/0.98  --prop_solver_per_cl                    1000
% 3.90/0.98  --min_unsat_core                        false
% 3.90/0.98  --soft_assumptions                      false
% 3.90/0.98  --soft_lemma_size                       3
% 3.90/0.98  --prop_impl_unit_size                   0
% 3.90/0.98  --prop_impl_unit                        []
% 3.90/0.98  --share_sel_clauses                     true
% 3.90/0.98  --reset_solvers                         false
% 3.90/0.98  --bc_imp_inh                            [conj_cone]
% 3.90/0.98  --conj_cone_tolerance                   3.
% 3.90/0.98  --extra_neg_conj                        none
% 3.90/0.98  --large_theory_mode                     true
% 3.90/0.98  --prolific_symb_bound                   200
% 3.90/0.98  --lt_threshold                          2000
% 3.90/0.98  --clause_weak_htbl                      true
% 3.90/0.98  --gc_record_bc_elim                     false
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing Options
% 3.90/0.98  
% 3.90/0.98  --preprocessing_flag                    true
% 3.90/0.98  --time_out_prep_mult                    0.1
% 3.90/0.98  --splitting_mode                        input
% 3.90/0.98  --splitting_grd                         true
% 3.90/0.98  --splitting_cvd                         false
% 3.90/0.98  --splitting_cvd_svl                     false
% 3.90/0.98  --splitting_nvd                         32
% 3.90/0.98  --sub_typing                            true
% 3.90/0.98  --prep_gs_sim                           true
% 3.90/0.98  --prep_unflatten                        true
% 3.90/0.98  --prep_res_sim                          true
% 3.90/0.98  --prep_upred                            true
% 3.90/0.98  --prep_sem_filter                       exhaustive
% 3.90/0.98  --prep_sem_filter_out                   false
% 3.90/0.98  --pred_elim                             true
% 3.90/0.98  --res_sim_input                         true
% 3.90/0.98  --eq_ax_congr_red                       true
% 3.90/0.98  --pure_diseq_elim                       true
% 3.90/0.98  --brand_transform                       false
% 3.90/0.98  --non_eq_to_eq                          false
% 3.90/0.98  --prep_def_merge                        true
% 3.90/0.98  --prep_def_merge_prop_impl              false
% 3.90/0.98  --prep_def_merge_mbd                    true
% 3.90/0.98  --prep_def_merge_tr_red                 false
% 3.90/0.98  --prep_def_merge_tr_cl                  false
% 3.90/0.98  --smt_preprocessing                     true
% 3.90/0.98  --smt_ac_axioms                         fast
% 3.90/0.98  --preprocessed_out                      false
% 3.90/0.98  --preprocessed_stats                    false
% 3.90/0.98  
% 3.90/0.98  ------ Abstraction refinement Options
% 3.90/0.98  
% 3.90/0.98  --abstr_ref                             []
% 3.90/0.98  --abstr_ref_prep                        false
% 3.90/0.98  --abstr_ref_until_sat                   false
% 3.90/0.98  --abstr_ref_sig_restrict                funpre
% 3.90/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.90/0.98  --abstr_ref_under                       []
% 3.90/0.98  
% 3.90/0.98  ------ SAT Options
% 3.90/0.98  
% 3.90/0.98  --sat_mode                              false
% 3.90/0.98  --sat_fm_restart_options                ""
% 3.90/0.98  --sat_gr_def                            false
% 3.90/0.98  --sat_epr_types                         true
% 3.90/0.98  --sat_non_cyclic_types                  false
% 3.90/0.98  --sat_finite_models                     false
% 3.90/0.98  --sat_fm_lemmas                         false
% 3.90/0.98  --sat_fm_prep                           false
% 3.90/0.98  --sat_fm_uc_incr                        true
% 3.90/0.98  --sat_out_model                         small
% 3.90/0.98  --sat_out_clauses                       false
% 3.90/0.98  
% 3.90/0.98  ------ QBF Options
% 3.90/0.98  
% 3.90/0.98  --qbf_mode                              false
% 3.90/0.98  --qbf_elim_univ                         false
% 3.90/0.98  --qbf_dom_inst                          none
% 3.90/0.98  --qbf_dom_pre_inst                      false
% 3.90/0.98  --qbf_sk_in                             false
% 3.90/0.98  --qbf_pred_elim                         true
% 3.90/0.98  --qbf_split                             512
% 3.90/0.98  
% 3.90/0.98  ------ BMC1 Options
% 3.90/0.98  
% 3.90/0.98  --bmc1_incremental                      false
% 3.90/0.98  --bmc1_axioms                           reachable_all
% 3.90/0.98  --bmc1_min_bound                        0
% 3.90/0.98  --bmc1_max_bound                        -1
% 3.90/0.98  --bmc1_max_bound_default                -1
% 3.90/0.98  --bmc1_symbol_reachability              true
% 3.90/0.98  --bmc1_property_lemmas                  false
% 3.90/0.98  --bmc1_k_induction                      false
% 3.90/0.98  --bmc1_non_equiv_states                 false
% 3.90/0.98  --bmc1_deadlock                         false
% 3.90/0.98  --bmc1_ucm                              false
% 3.90/0.98  --bmc1_add_unsat_core                   none
% 3.90/0.98  --bmc1_unsat_core_children              false
% 3.90/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.90/0.98  --bmc1_out_stat                         full
% 3.90/0.98  --bmc1_ground_init                      false
% 3.90/0.98  --bmc1_pre_inst_next_state              false
% 3.90/0.98  --bmc1_pre_inst_state                   false
% 3.90/0.98  --bmc1_pre_inst_reach_state             false
% 3.90/0.98  --bmc1_out_unsat_core                   false
% 3.90/0.98  --bmc1_aig_witness_out                  false
% 3.90/0.98  --bmc1_verbose                          false
% 3.90/0.98  --bmc1_dump_clauses_tptp                false
% 3.90/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.90/0.98  --bmc1_dump_file                        -
% 3.90/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.90/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.90/0.98  --bmc1_ucm_extend_mode                  1
% 3.90/0.98  --bmc1_ucm_init_mode                    2
% 3.90/0.98  --bmc1_ucm_cone_mode                    none
% 3.90/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.90/0.98  --bmc1_ucm_relax_model                  4
% 3.90/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.90/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.90/0.98  --bmc1_ucm_layered_model                none
% 3.90/0.98  --bmc1_ucm_max_lemma_size               10
% 3.90/0.98  
% 3.90/0.98  ------ AIG Options
% 3.90/0.98  
% 3.90/0.98  --aig_mode                              false
% 3.90/0.98  
% 3.90/0.98  ------ Instantiation Options
% 3.90/0.98  
% 3.90/0.98  --instantiation_flag                    true
% 3.90/0.98  --inst_sos_flag                         false
% 3.90/0.98  --inst_sos_phase                        true
% 3.90/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.90/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.90/0.98  --inst_lit_sel_side                     none
% 3.90/0.98  --inst_solver_per_active                1400
% 3.90/0.98  --inst_solver_calls_frac                1.
% 3.90/0.98  --inst_passive_queue_type               priority_queues
% 3.90/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.90/0.98  --inst_passive_queues_freq              [25;2]
% 3.90/0.98  --inst_dismatching                      true
% 3.90/0.98  --inst_eager_unprocessed_to_passive     true
% 3.90/0.98  --inst_prop_sim_given                   true
% 3.90/0.98  --inst_prop_sim_new                     false
% 3.90/0.98  --inst_subs_new                         false
% 3.90/0.98  --inst_eq_res_simp                      false
% 3.90/0.98  --inst_subs_given                       false
% 3.90/0.98  --inst_orphan_elimination               true
% 3.90/0.98  --inst_learning_loop_flag               true
% 3.90/0.98  --inst_learning_start                   3000
% 3.90/0.98  --inst_learning_factor                  2
% 3.90/0.98  --inst_start_prop_sim_after_learn       3
% 3.90/0.98  --inst_sel_renew                        solver
% 3.90/0.98  --inst_lit_activity_flag                true
% 3.90/0.98  --inst_restr_to_given                   false
% 3.90/0.98  --inst_activity_threshold               500
% 3.90/0.98  --inst_out_proof                        true
% 3.90/0.98  
% 3.90/0.98  ------ Resolution Options
% 3.90/0.98  
% 3.90/0.98  --resolution_flag                       false
% 3.90/0.98  --res_lit_sel                           adaptive
% 3.90/0.98  --res_lit_sel_side                      none
% 3.90/0.98  --res_ordering                          kbo
% 3.90/0.98  --res_to_prop_solver                    active
% 3.90/0.98  --res_prop_simpl_new                    false
% 3.90/0.98  --res_prop_simpl_given                  true
% 3.90/0.98  --res_passive_queue_type                priority_queues
% 3.90/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.90/0.98  --res_passive_queues_freq               [15;5]
% 3.90/0.98  --res_forward_subs                      full
% 3.90/0.98  --res_backward_subs                     full
% 3.90/0.98  --res_forward_subs_resolution           true
% 3.90/0.98  --res_backward_subs_resolution          true
% 3.90/0.98  --res_orphan_elimination                true
% 3.90/0.98  --res_time_limit                        2.
% 3.90/0.98  --res_out_proof                         true
% 3.90/0.98  
% 3.90/0.98  ------ Superposition Options
% 3.90/0.98  
% 3.90/0.98  --superposition_flag                    true
% 3.90/0.98  --sup_passive_queue_type                priority_queues
% 3.90/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.90/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.90/0.98  --demod_completeness_check              fast
% 3.90/0.98  --demod_use_ground                      true
% 3.90/0.98  --sup_to_prop_solver                    passive
% 3.90/0.98  --sup_prop_simpl_new                    true
% 3.90/0.98  --sup_prop_simpl_given                  true
% 3.90/0.98  --sup_fun_splitting                     false
% 3.90/0.98  --sup_smt_interval                      50000
% 3.90/0.98  
% 3.90/0.98  ------ Superposition Simplification Setup
% 3.90/0.98  
% 3.90/0.98  --sup_indices_passive                   []
% 3.90/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.90/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.90/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.98  --sup_full_bw                           [BwDemod]
% 3.90/0.98  --sup_immed_triv                        [TrivRules]
% 3.90/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.90/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.98  --sup_immed_bw_main                     []
% 3.90/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.90/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.90/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.90/0.98  
% 3.90/0.98  ------ Combination Options
% 3.90/0.98  
% 3.90/0.98  --comb_res_mult                         3
% 3.90/0.98  --comb_sup_mult                         2
% 3.90/0.98  --comb_inst_mult                        10
% 3.90/0.98  
% 3.90/0.98  ------ Debug Options
% 3.90/0.98  
% 3.90/0.98  --dbg_backtrace                         false
% 3.90/0.98  --dbg_dump_prop_clauses                 false
% 3.90/0.98  --dbg_dump_prop_clauses_file            -
% 3.90/0.98  --dbg_out_stat                          false
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  ------ Proving...
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  % SZS status Theorem for theBenchmark.p
% 3.90/0.98  
% 3.90/0.98   Resolution empty clause
% 3.90/0.98  
% 3.90/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.90/0.98  
% 3.90/0.98  fof(f32,conjecture,(
% 3.90/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f33,negated_conjecture,(
% 3.90/0.98    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.90/0.98    inference(negated_conjecture,[],[f32])).
% 3.90/0.98  
% 3.90/0.98  fof(f67,plain,(
% 3.90/0.98    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.90/0.98    inference(ennf_transformation,[],[f33])).
% 3.90/0.98  
% 3.90/0.98  fof(f68,plain,(
% 3.90/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.90/0.98    inference(flattening,[],[f67])).
% 3.90/0.98  
% 3.90/0.98  fof(f80,plain,(
% 3.90/0.98    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3))),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f81,plain,(
% 3.90/0.98    (~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))) & k2_relset_1(sK1,sK2,sK3) = sK2 & v2_funct_1(sK3) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK3,sK1,sK2) & v1_funct_1(sK3)),
% 3.90/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f68,f80])).
% 3.90/0.98  
% 3.90/0.98  fof(f140,plain,(
% 3.90/0.98    v2_funct_1(sK3)),
% 3.90/0.98    inference(cnf_transformation,[],[f81])).
% 3.90/0.98  
% 3.90/0.98  fof(f21,axiom,(
% 3.90/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f52,plain,(
% 3.90/0.98    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f21])).
% 3.90/0.98  
% 3.90/0.98  fof(f53,plain,(
% 3.90/0.98    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.90/0.98    inference(flattening,[],[f52])).
% 3.90/0.98  
% 3.90/0.98  fof(f116,plain,(
% 3.90/0.98    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f53])).
% 3.90/0.98  
% 3.90/0.98  fof(f139,plain,(
% 3.90/0.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 3.90/0.98    inference(cnf_transformation,[],[f81])).
% 3.90/0.98  
% 3.90/0.98  fof(f25,axiom,(
% 3.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f58,plain,(
% 3.90/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.90/0.98    inference(ennf_transformation,[],[f25])).
% 3.90/0.98  
% 3.90/0.98  fof(f121,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f58])).
% 3.90/0.98  
% 3.90/0.98  fof(f141,plain,(
% 3.90/0.98    k2_relset_1(sK1,sK2,sK3) = sK2),
% 3.90/0.98    inference(cnf_transformation,[],[f81])).
% 3.90/0.98  
% 3.90/0.98  fof(f137,plain,(
% 3.90/0.98    v1_funct_1(sK3)),
% 3.90/0.98    inference(cnf_transformation,[],[f81])).
% 3.90/0.98  
% 3.90/0.98  fof(f23,axiom,(
% 3.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f56,plain,(
% 3.90/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.90/0.98    inference(ennf_transformation,[],[f23])).
% 3.90/0.98  
% 3.90/0.98  fof(f119,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f56])).
% 3.90/0.98  
% 3.90/0.98  fof(f4,axiom,(
% 3.90/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f75,plain,(
% 3.90/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.90/0.98    inference(nnf_transformation,[],[f4])).
% 3.90/0.98  
% 3.90/0.98  fof(f76,plain,(
% 3.90/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.90/0.98    inference(flattening,[],[f75])).
% 3.90/0.98  
% 3.90/0.98  fof(f90,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.90/0.98    inference(cnf_transformation,[],[f76])).
% 3.90/0.98  
% 3.90/0.98  fof(f156,plain,(
% 3.90/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.90/0.98    inference(equality_resolution,[],[f90])).
% 3.90/0.98  
% 3.90/0.98  fof(f5,axiom,(
% 3.90/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f77,plain,(
% 3.90/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.90/0.98    inference(nnf_transformation,[],[f5])).
% 3.90/0.98  
% 3.90/0.98  fof(f93,plain,(
% 3.90/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f77])).
% 3.90/0.98  
% 3.90/0.98  fof(f24,axiom,(
% 3.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f34,plain,(
% 3.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.90/0.98    inference(pure_predicate_removal,[],[f24])).
% 3.90/0.98  
% 3.90/0.98  fof(f57,plain,(
% 3.90/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.90/0.98    inference(ennf_transformation,[],[f34])).
% 3.90/0.98  
% 3.90/0.98  fof(f120,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f57])).
% 3.90/0.98  
% 3.90/0.98  fof(f7,axiom,(
% 3.90/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f37,plain,(
% 3.90/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.90/0.98    inference(ennf_transformation,[],[f7])).
% 3.90/0.98  
% 3.90/0.98  fof(f78,plain,(
% 3.90/0.98    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.90/0.98    inference(nnf_transformation,[],[f37])).
% 3.90/0.98  
% 3.90/0.98  fof(f95,plain,(
% 3.90/0.98    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f78])).
% 3.90/0.98  
% 3.90/0.98  fof(f89,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f76])).
% 3.90/0.98  
% 3.90/0.98  fof(f3,axiom,(
% 3.90/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f73,plain,(
% 3.90/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.90/0.98    inference(nnf_transformation,[],[f3])).
% 3.90/0.98  
% 3.90/0.98  fof(f74,plain,(
% 3.90/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.90/0.98    inference(flattening,[],[f73])).
% 3.90/0.98  
% 3.90/0.98  fof(f86,plain,(
% 3.90/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.90/0.98    inference(cnf_transformation,[],[f74])).
% 3.90/0.98  
% 3.90/0.98  fof(f154,plain,(
% 3.90/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.90/0.98    inference(equality_resolution,[],[f86])).
% 3.90/0.98  
% 3.90/0.98  fof(f15,axiom,(
% 3.90/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f44,plain,(
% 3.90/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f15])).
% 3.90/0.98  
% 3.90/0.98  fof(f45,plain,(
% 3.90/0.98    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.90/0.98    inference(flattening,[],[f44])).
% 3.90/0.98  
% 3.90/0.98  fof(f108,plain,(
% 3.90/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f45])).
% 3.90/0.98  
% 3.90/0.98  fof(f107,plain,(
% 3.90/0.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f45])).
% 3.90/0.98  
% 3.90/0.98  fof(f117,plain,(
% 3.90/0.98    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f53])).
% 3.90/0.98  
% 3.90/0.98  fof(f30,axiom,(
% 3.90/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f63,plain,(
% 3.90/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f30])).
% 3.90/0.98  
% 3.90/0.98  fof(f64,plain,(
% 3.90/0.98    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.90/0.98    inference(flattening,[],[f63])).
% 3.90/0.98  
% 3.90/0.98  fof(f129,plain,(
% 3.90/0.98    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f64])).
% 3.90/0.98  
% 3.90/0.98  fof(f11,axiom,(
% 3.90/0.98    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f42,plain,(
% 3.90/0.98    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.90/0.98    inference(ennf_transformation,[],[f11])).
% 3.90/0.98  
% 3.90/0.98  fof(f79,plain,(
% 3.90/0.98    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.90/0.98    inference(nnf_transformation,[],[f42])).
% 3.90/0.98  
% 3.90/0.98  fof(f102,plain,(
% 3.90/0.98    ( ! [X0] : (k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f79])).
% 3.90/0.98  
% 3.90/0.98  fof(f130,plain,(
% 3.90/0.98    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f64])).
% 3.90/0.98  
% 3.90/0.98  fof(f26,axiom,(
% 3.90/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_tarski(k2_relat_1(X3),X1) => m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f59,plain,(
% 3.90/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.90/0.98    inference(ennf_transformation,[],[f26])).
% 3.90/0.98  
% 3.90/0.98  fof(f60,plain,(
% 3.90/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 3.90/0.98    inference(flattening,[],[f59])).
% 3.90/0.98  
% 3.90/0.98  fof(f122,plain,(
% 3.90/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~r1_tarski(k2_relat_1(X3),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f60])).
% 3.90/0.98  
% 3.90/0.98  fof(f142,plain,(
% 3.90/0.98    ~m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(k2_funct_1(sK3),sK2,sK1) | ~v1_funct_1(k2_funct_1(sK3))),
% 3.90/0.98    inference(cnf_transformation,[],[f81])).
% 3.90/0.98  
% 3.90/0.98  fof(f31,axiom,(
% 3.90/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f65,plain,(
% 3.90/0.98    ! [X0,X1,X2,X3] : ((((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | ~r1_tarski(X1,X2)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.90/0.98    inference(ennf_transformation,[],[f31])).
% 3.90/0.98  
% 3.90/0.98  fof(f66,plain,(
% 3.90/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.90/0.98    inference(flattening,[],[f65])).
% 3.90/0.98  
% 3.90/0.98  fof(f133,plain,(
% 3.90/0.98    ( ! [X2,X0,X3,X1] : (v1_funct_2(X3,X0,X2) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f66])).
% 3.90/0.98  
% 3.90/0.98  fof(f1,axiom,(
% 3.90/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f35,plain,(
% 3.90/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f1])).
% 3.90/0.98  
% 3.90/0.98  fof(f69,plain,(
% 3.90/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.90/0.98    inference(nnf_transformation,[],[f35])).
% 3.90/0.98  
% 3.90/0.98  fof(f70,plain,(
% 3.90/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.90/0.98    inference(rectify,[],[f69])).
% 3.90/0.98  
% 3.90/0.98  fof(f71,plain,(
% 3.90/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.90/0.98    introduced(choice_axiom,[])).
% 3.90/0.98  
% 3.90/0.98  fof(f72,plain,(
% 3.90/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.90/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f70,f71])).
% 3.90/0.98  
% 3.90/0.98  fof(f83,plain,(
% 3.90/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f72])).
% 3.90/0.98  
% 3.90/0.98  fof(f2,axiom,(
% 3.90/0.98    v1_xboole_0(k1_xboole_0)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f85,plain,(
% 3.90/0.98    v1_xboole_0(k1_xboole_0)),
% 3.90/0.98    inference(cnf_transformation,[],[f2])).
% 3.90/0.98  
% 3.90/0.98  fof(f6,axiom,(
% 3.90/0.98    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f36,plain,(
% 3.90/0.98    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.90/0.98    inference(ennf_transformation,[],[f6])).
% 3.90/0.98  
% 3.90/0.98  fof(f94,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f36])).
% 3.90/0.98  
% 3.90/0.98  fof(f91,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.90/0.98    inference(cnf_transformation,[],[f76])).
% 3.90/0.98  
% 3.90/0.98  fof(f155,plain,(
% 3.90/0.98    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.90/0.98    inference(equality_resolution,[],[f91])).
% 3.90/0.98  
% 3.90/0.98  fof(f135,plain,(
% 3.90/0.98    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | k1_xboole_0 = X1 | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f66])).
% 3.90/0.98  
% 3.90/0.98  fof(f138,plain,(
% 3.90/0.98    v1_funct_2(sK3,sK1,sK2)),
% 3.90/0.98    inference(cnf_transformation,[],[f81])).
% 3.90/0.98  
% 3.90/0.98  fof(f18,axiom,(
% 3.90/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f46,plain,(
% 3.90/0.98    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.90/0.98    inference(ennf_transformation,[],[f18])).
% 3.90/0.98  
% 3.90/0.98  fof(f47,plain,(
% 3.90/0.98    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.90/0.98    inference(flattening,[],[f46])).
% 3.90/0.98  
% 3.90/0.98  fof(f113,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f47])).
% 3.90/0.98  
% 3.90/0.98  fof(f88,plain,(
% 3.90/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f74])).
% 3.90/0.98  
% 3.90/0.98  fof(f10,axiom,(
% 3.90/0.98    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f40,plain,(
% 3.90/0.98    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.90/0.98    inference(ennf_transformation,[],[f10])).
% 3.90/0.98  
% 3.90/0.98  fof(f41,plain,(
% 3.90/0.98    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.90/0.98    inference(flattening,[],[f40])).
% 3.90/0.98  
% 3.90/0.98  fof(f100,plain,(
% 3.90/0.98    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f41])).
% 3.90/0.98  
% 3.90/0.98  fof(f14,axiom,(
% 3.90/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f106,plain,(
% 3.90/0.98    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 3.90/0.98    inference(cnf_transformation,[],[f14])).
% 3.90/0.98  
% 3.90/0.98  fof(f29,axiom,(
% 3.90/0.98    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f127,plain,(
% 3.90/0.98    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f29])).
% 3.90/0.98  
% 3.90/0.98  fof(f146,plain,(
% 3.90/0.98    k1_xboole_0 = k6_partfun1(k1_xboole_0)),
% 3.90/0.98    inference(definition_unfolding,[],[f106,f127])).
% 3.90/0.98  
% 3.90/0.98  fof(f17,axiom,(
% 3.90/0.98    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f111,plain,(
% 3.90/0.98    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f17])).
% 3.90/0.98  
% 3.90/0.98  fof(f150,plain,(
% 3.90/0.98    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 3.90/0.98    inference(definition_unfolding,[],[f111,f127])).
% 3.90/0.98  
% 3.90/0.98  fof(f13,axiom,(
% 3.90/0.98    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f43,plain,(
% 3.90/0.98    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.90/0.98    inference(ennf_transformation,[],[f13])).
% 3.90/0.98  
% 3.90/0.98  fof(f105,plain,(
% 3.90/0.98    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f43])).
% 3.90/0.98  
% 3.90/0.98  fof(f145,plain,(
% 3.90/0.98    ( ! [X0] : (k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(definition_unfolding,[],[f105,f127])).
% 3.90/0.98  
% 3.90/0.98  fof(f12,axiom,(
% 3.90/0.98    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f104,plain,(
% 3.90/0.98    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.90/0.98    inference(cnf_transformation,[],[f12])).
% 3.90/0.98  
% 3.90/0.98  fof(f143,plain,(
% 3.90/0.98    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 3.90/0.98    inference(definition_unfolding,[],[f104,f127])).
% 3.90/0.98  
% 3.90/0.98  fof(f22,axiom,(
% 3.90/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f54,plain,(
% 3.90/0.98    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f22])).
% 3.90/0.98  
% 3.90/0.98  fof(f55,plain,(
% 3.90/0.98    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.90/0.98    inference(flattening,[],[f54])).
% 3.90/0.98  
% 3.90/0.98  fof(f118,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f55])).
% 3.90/0.98  
% 3.90/0.98  fof(f152,plain,(
% 3.90/0.98    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(definition_unfolding,[],[f118,f127])).
% 3.90/0.98  
% 3.90/0.98  fof(f20,axiom,(
% 3.90/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f50,plain,(
% 3.90/0.98    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.90/0.98    inference(ennf_transformation,[],[f20])).
% 3.90/0.98  
% 3.90/0.98  fof(f51,plain,(
% 3.90/0.98    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.90/0.98    inference(flattening,[],[f50])).
% 3.90/0.98  
% 3.90/0.98  fof(f115,plain,(
% 3.90/0.98    ( ! [X0,X1] : (v2_funct_1(X0) | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f51])).
% 3.90/0.98  
% 3.90/0.98  fof(f151,plain,(
% 3.90/0.98    ( ! [X0,X1] : (v2_funct_1(X0) | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.90/0.98    inference(definition_unfolding,[],[f115,f127])).
% 3.90/0.98  
% 3.90/0.98  fof(f103,plain,(
% 3.90/0.98    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.90/0.98    inference(cnf_transformation,[],[f12])).
% 3.90/0.98  
% 3.90/0.98  fof(f144,plain,(
% 3.90/0.98    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.90/0.98    inference(definition_unfolding,[],[f103,f127])).
% 3.90/0.98  
% 3.90/0.98  fof(f16,axiom,(
% 3.90/0.98    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f110,plain,(
% 3.90/0.98    ( ! [X0] : (v1_funct_1(k6_relat_1(X0))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f16])).
% 3.90/0.98  
% 3.90/0.98  fof(f147,plain,(
% 3.90/0.98    ( ! [X0] : (v1_funct_1(k6_partfun1(X0))) )),
% 3.90/0.98    inference(definition_unfolding,[],[f110,f127])).
% 3.90/0.98  
% 3.90/0.98  fof(f27,axiom,(
% 3.90/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f61,plain,(
% 3.90/0.98    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.90/0.98    inference(ennf_transformation,[],[f27])).
% 3.90/0.98  
% 3.90/0.98  fof(f62,plain,(
% 3.90/0.98    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.90/0.98    inference(flattening,[],[f61])).
% 3.90/0.98  
% 3.90/0.98  fof(f124,plain,(
% 3.90/0.98    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.90/0.98    inference(cnf_transformation,[],[f62])).
% 3.90/0.98  
% 3.90/0.98  fof(f28,axiom,(
% 3.90/0.98    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 3.90/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.90/0.98  
% 3.90/0.98  fof(f125,plain,(
% 3.90/0.98    ( ! [X0] : (v1_partfun1(k6_partfun1(X0),X0)) )),
% 3.90/0.98    inference(cnf_transformation,[],[f28])).
% 3.90/0.98  
% 3.90/0.98  cnf(c_56,negated_conjecture,
% 3.90/0.98      ( v2_funct_1(sK3) ),
% 3.90/0.98      inference(cnf_transformation,[],[f140]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2437,plain,
% 3.90/0.98      ( v2_funct_1(sK3) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_35,plain,
% 3.90/0.98      ( ~ v2_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_relat_1(X0)
% 3.90/0.98      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f116]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2449,plain,
% 3.90/0.98      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.90/0.98      | v2_funct_1(X0) != iProver_top
% 3.90/0.98      | v1_funct_1(X0) != iProver_top
% 3.90/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_9958,plain,
% 3.90/0.98      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 3.90/0.98      | v1_funct_1(sK3) != iProver_top
% 3.90/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_2437,c_2449]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_57,negated_conjecture,
% 3.90/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 3.90/0.98      inference(cnf_transformation,[],[f139]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2436,plain,
% 3.90/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_39,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f121]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2447,plain,
% 3.90/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.90/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_7836,plain,
% 3.90/0.98      ( k2_relset_1(sK1,sK2,sK3) = k2_relat_1(sK3) ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_2436,c_2447]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_55,negated_conjecture,
% 3.90/0.98      ( k2_relset_1(sK1,sK2,sK3) = sK2 ),
% 3.90/0.98      inference(cnf_transformation,[],[f141]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_7882,plain,
% 3.90/0.98      ( k2_relat_1(sK3) = sK2 ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_7836,c_55]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_9970,plain,
% 3.90/0.98      ( k1_relat_1(k2_funct_1(sK3)) = sK2
% 3.90/0.98      | v1_funct_1(sK3) != iProver_top
% 3.90/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_9958,c_7882]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_59,negated_conjecture,
% 3.90/0.98      ( v1_funct_1(sK3) ),
% 3.90/0.98      inference(cnf_transformation,[],[f137]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_60,plain,
% 3.90/0.98      ( v1_funct_1(sK3) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_62,plain,
% 3.90/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_37,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f119]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2867,plain,
% 3.90/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.90/0.98      | v1_relat_1(sK3) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_37]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2868,plain,
% 3.90/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.90/0.98      | v1_relat_1(sK3) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_2867]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_10823,plain,
% 3.90/0.98      ( k1_relat_1(k2_funct_1(sK3)) = sK2 ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_9970,c_60,c_62,c_2868]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_8,plain,
% 3.90/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f156]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_10,plain,
% 3.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2467,plain,
% 3.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.90/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_38,plain,
% 3.90/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.90/0.98      inference(cnf_transformation,[],[f120]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_14,plain,
% 3.90/0.98      ( ~ v4_relat_1(X0,X1) | r1_tarski(k1_relat_1(X0),X1) | ~ v1_relat_1(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_691,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | r1_tarski(k1_relat_1(X0),X1)
% 3.90/0.98      | ~ v1_relat_1(X0) ),
% 3.90/0.98      inference(resolution,[status(thm)],[c_38,c_14]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_695,plain,
% 3.90/0.98      ( r1_tarski(k1_relat_1(X0),X1)
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.90/0.98      inference(global_propositional_subsumption,[status(thm)],[c_691,c_37]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_696,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.90/0.98      inference(renaming,[status(thm)],[c_695]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2430,plain,
% 3.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.90/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4675,plain,
% 3.90/0.98      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.90/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_2467,c_2430]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_17180,plain,
% 3.90/0.98      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.90/0.98      | r1_tarski(k1_relat_1(X0),k1_xboole_0) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_8,c_4675]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_17301,plain,
% 3.90/0.98      ( r1_tarski(k2_funct_1(sK3),k1_xboole_0) != iProver_top
% 3.90/0.98      | r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_10823,c_17180]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_9,plain,
% 3.90/0.98      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.90/0.98      | k1_xboole_0 = X1
% 3.90/0.98      | k1_xboole_0 = X0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_170,plain,
% 3.90/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.90/0.98      | k1_xboole_0 = k1_xboole_0 ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_171,plain,
% 3.90/0.98      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_8]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f154]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_172,plain,
% 3.90/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_174,plain,
% 3.90/0.98      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_172]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_25,plain,
% 3.90/0.98      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f108]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2825,plain,
% 3.90/0.98      ( v1_funct_1(k2_funct_1(sK3)) | ~ v1_funct_1(sK3) | ~ v1_relat_1(sK3) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_25]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_26,plain,
% 3.90/0.98      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f107]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2833,plain,
% 3.90/0.98      ( ~ v1_funct_1(sK3) | v1_relat_1(k2_funct_1(sK3)) | ~ v1_relat_1(sK3) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_26]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2834,plain,
% 3.90/0.98      ( v1_funct_1(sK3) != iProver_top
% 3.90/0.98      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 3.90/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_2833]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2940,plain,
% 3.90/0.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 3.90/0.98      | r1_tarski(k1_relat_1(sK3),sK1) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_696]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1451,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3362,plain,
% 3.90/0.98      ( k1_relat_1(sK3) != X0
% 3.90/0.98      | k1_relat_1(sK3) = k1_xboole_0
% 3.90/0.98      | k1_xboole_0 != X0 ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_1451]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4725,plain,
% 3.90/0.98      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 3.90/0.98      | k1_relat_1(sK3) = k1_xboole_0
% 3.90/0.98      | k1_xboole_0 != k1_relat_1(sK3) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_3362]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1450,plain,( X0 = X0 ),theory(equality) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4726,plain,
% 3.90/0.98      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_1450]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_34,plain,
% 3.90/0.98      ( ~ v2_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_relat_1(X0)
% 3.90/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f117]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2450,plain,
% 3.90/0.98      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.90/0.98      | v2_funct_1(X0) != iProver_top
% 3.90/0.98      | v1_funct_1(X0) != iProver_top
% 3.90/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11497,plain,
% 3.90/0.98      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 3.90/0.98      | v1_funct_1(sK3) != iProver_top
% 3.90/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_2437,c_2450]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_840,plain,
% 3.90/0.98      ( ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_relat_1(X0)
% 3.90/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.90/0.98      | sK3 != X0 ),
% 3.90/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_56]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_841,plain,
% 3.90/0.98      ( ~ v1_funct_1(sK3)
% 3.90/0.98      | ~ v1_relat_1(sK3)
% 3.90/0.98      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.90/0.98      inference(unflattening,[status(thm)],[c_840]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11853,plain,
% 3.90/0.98      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_11497,c_59,c_57,c_841,c_2867]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_46,plain,
% 3.90/0.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_relat_1(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f129]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2443,plain,
% 3.90/0.98      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) = iProver_top
% 3.90/0.98      | v1_funct_1(X0) != iProver_top
% 3.90/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11858,plain,
% 3.90/0.98      ( v1_funct_2(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)) = iProver_top
% 3.90/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.90/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_11853,c_2443]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11869,plain,
% 3.90/0.98      ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3)) = iProver_top
% 3.90/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.90/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_11858,c_10823]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11888,plain,
% 3.90/0.98      ( v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
% 3.90/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.90/0.98      | ~ v1_relat_1(k2_funct_1(sK3)) ),
% 3.90/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_11869]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_19,plain,
% 3.90/0.98      ( ~ v1_relat_1(X0)
% 3.90/0.98      | k2_relat_1(X0) != k1_xboole_0
% 3.90/0.98      | k1_relat_1(X0) = k1_xboole_0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2461,plain,
% 3.90/0.98      ( k2_relat_1(X0) != k1_xboole_0
% 3.90/0.98      | k1_relat_1(X0) = k1_xboole_0
% 3.90/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11857,plain,
% 3.90/0.98      ( k1_relat_1(k2_funct_1(sK3)) = k1_xboole_0
% 3.90/0.98      | k1_relat_1(sK3) != k1_xboole_0
% 3.90/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_11853,c_2461]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11876,plain,
% 3.90/0.98      ( k1_relat_1(sK3) != k1_xboole_0
% 3.90/0.98      | sK2 = k1_xboole_0
% 3.90/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.90/0.98      inference(demodulation,[status(thm)],[c_11857,c_10823]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_45,plain,
% 3.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_relat_1(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f130]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2444,plain,
% 3.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.90/0.98      | v1_funct_1(X0) != iProver_top
% 3.90/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11856,plain,
% 3.90/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 3.90/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.90/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_11853,c_2444]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11883,plain,
% 3.90/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top
% 3.90/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 3.90/0.98      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_11856,c_10823]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11890,plain,
% 3.90/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
% 3.90/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.90/0.98      | ~ v1_relat_1(k2_funct_1(sK3)) ),
% 3.90/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_11883]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2826,plain,
% 3.90/0.98      ( v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 3.90/0.98      | v1_funct_1(sK3) != iProver_top
% 3.90/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_2825]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_13323,plain,
% 3.90/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3)))) = iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_11883,c_60,c_62,c_2826,c_2834,c_2868]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_40,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.90/0.98      | ~ r1_tarski(k2_relat_1(X0),X3) ),
% 3.90/0.98      inference(cnf_transformation,[],[f122]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2446,plain,
% 3.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.90/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) = iProver_top
% 3.90/0.98      | r1_tarski(k2_relat_1(X0),X3) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_13329,plain,
% 3.90/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.90/0.98      | r1_tarski(k2_relat_1(k2_funct_1(sK3)),X0) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_13323,c_2446]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_13364,plain,
% 3.90/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) = iProver_top
% 3.90/0.98      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_13329,c_11853]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_54,negated_conjecture,
% 3.90/0.98      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.90/0.98      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
% 3.90/0.98      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f142]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2438,plain,
% 3.90/0.98      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.90/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.90/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_64,plain,
% 3.90/0.98      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.90/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.90/0.98      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2873,plain,
% 3.90/0.98      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top
% 3.90/0.98      | v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_2438,c_60,c_62,c_64,c_2826,c_2868]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2874,plain,
% 3.90/0.98      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.90/0.98      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) != iProver_top ),
% 3.90/0.98      inference(renaming,[status(thm)],[c_2873]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_13949,plain,
% 3.90/0.98      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top
% 3.90/0.98      | r1_tarski(k1_relat_1(sK3),sK1) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_13364,c_2874]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_14004,plain,
% 3.90/0.98      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.90/0.98      | ~ r1_tarski(k1_relat_1(sK3),sK1) ),
% 3.90/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_13949]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1452,plain,
% 3.90/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.90/0.98      theory(equality) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_15558,plain,
% 3.90/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,X2) | X2 != X1 | sK2 != X0 ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_1452]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_15559,plain,
% 3.90/0.98      ( X0 != X1
% 3.90/0.98      | sK2 != X2
% 3.90/0.98      | r1_tarski(X2,X1) != iProver_top
% 3.90/0.98      | r1_tarski(sK2,X0) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_15558]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_15561,plain,
% 3.90/0.98      ( sK2 != k1_xboole_0
% 3.90/0.98      | k1_xboole_0 != k1_xboole_0
% 3.90/0.98      | r1_tarski(sK2,k1_xboole_0) = iProver_top
% 3.90/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_15559]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_51,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.98      | v1_funct_2(X0,X1,X3)
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ r1_tarski(X2,X3)
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | k1_xboole_0 = X2 ),
% 3.90/0.98      inference(cnf_transformation,[],[f133]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6339,plain,
% 3.90/0.98      ( v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ v1_funct_2(X0,X1,k1_relat_1(sK3))
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_relat_1(sK3))))
% 3.90/0.98      | ~ r1_tarski(k1_relat_1(sK3),X2)
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | k1_xboole_0 = k1_relat_1(sK3) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_51]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_16851,plain,
% 3.90/0.98      ( ~ v1_funct_2(k2_funct_1(sK3),sK2,k1_relat_1(sK3))
% 3.90/0.98      | v1_funct_2(k2_funct_1(sK3),sK2,sK1)
% 3.90/0.98      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(sK2,k1_relat_1(sK3))))
% 3.90/0.98      | ~ r1_tarski(k1_relat_1(sK3),sK1)
% 3.90/0.98      | ~ v1_funct_1(k2_funct_1(sK3))
% 3.90/0.98      | k1_xboole_0 = k1_relat_1(sK3) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_6339]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_17627,plain,
% 3.90/0.98      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_17301,c_59,c_60,c_57,c_62,c_170,c_171,c_174,c_2825,c_2833,
% 3.90/0.98                 c_2834,c_2867,c_2868,c_2940,c_4725,c_4726,c_11888,c_11876,
% 3.90/0.98                 c_11890,c_14004,c_15561,c_16851]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_1,plain,
% 3.90/0.98      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2471,plain,
% 3.90/0.98      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 3.90/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3,plain,
% 3.90/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f85]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_12,plain,
% 3.90/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.90/0.98      | ~ r2_hidden(X2,X0)
% 3.90/0.98      | ~ v1_xboole_0(X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_403,plain,
% 3.90/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.90/0.98      inference(prop_impl,[status(thm)],[c_10]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_404,plain,
% 3.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.90/0.98      inference(renaming,[status(thm)],[c_403]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_489,plain,
% 3.90/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 3.90/0.98      inference(bin_hyper_res,[status(thm)],[c_12,c_404]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_655,plain,
% 3.90/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | k1_xboole_0 != X2 ),
% 3.90/0.98      inference(resolution_lifted,[status(thm)],[c_3,c_489]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_656,plain,
% 3.90/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,k1_xboole_0) ),
% 3.90/0.98      inference(unflattening,[status(thm)],[c_655]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2432,plain,
% 3.90/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.90/0.98      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_656]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5129,plain,
% 3.90/0.98      ( r1_tarski(X0,X1) = iProver_top
% 3.90/0.98      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_2471,c_2432]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_17644,plain,
% 3.90/0.98      ( r1_tarski(sK2,X0) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_17627,c_5129]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_7,plain,
% 3.90/0.98      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f155]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_49,plain,
% 3.90/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.90/0.98      | ~ r1_tarski(X2,X3)
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | k1_xboole_0 = X2 ),
% 3.90/0.98      inference(cnf_transformation,[],[f135]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2441,plain,
% 3.90/0.98      ( k1_xboole_0 = X0
% 3.90/0.98      | v1_funct_2(X1,X2,X0) != iProver_top
% 3.90/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 3.90/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top
% 3.90/0.98      | r1_tarski(X0,X3) != iProver_top
% 3.90/0.98      | v1_funct_1(X1) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_5876,plain,
% 3.90/0.98      ( sK2 = k1_xboole_0
% 3.90/0.98      | v1_funct_2(sK3,sK1,sK2) != iProver_top
% 3.90/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.90/0.98      | r1_tarski(sK2,X0) != iProver_top
% 3.90/0.98      | v1_funct_1(sK3) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_2436,c_2441]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_58,negated_conjecture,
% 3.90/0.98      ( v1_funct_2(sK3,sK1,sK2) ),
% 3.90/0.98      inference(cnf_transformation,[],[f138]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_61,plain,
% 3.90/0.98      ( v1_funct_2(sK3,sK1,sK2) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6141,plain,
% 3.90/0.98      ( r1_tarski(sK2,X0) != iProver_top
% 3.90/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.90/0.98      | sK2 = k1_xboole_0 ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_5876,c_60,c_61]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6142,plain,
% 3.90/0.98      ( sK2 = k1_xboole_0
% 3.90/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) = iProver_top
% 3.90/0.98      | r1_tarski(sK2,X0) != iProver_top ),
% 3.90/0.98      inference(renaming,[status(thm)],[c_6141]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6150,plain,
% 3.90/0.98      ( sK2 = k1_xboole_0
% 3.90/0.98      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.90/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_7,c_6142]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2956,plain,
% 3.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.90/0.98      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_7,c_2430]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6235,plain,
% 3.90/0.98      ( sK2 = k1_xboole_0
% 3.90/0.98      | r1_tarski(k1_relat_1(sK3),X0) = iProver_top
% 3.90/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_6150,c_2956]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_31,plain,
% 3.90/0.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 3.90/0.98      | ~ v1_funct_1(X1)
% 3.90/0.98      | ~ v1_relat_1(X1)
% 3.90/0.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f113]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2453,plain,
% 3.90/0.98      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 3.90/0.98      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 3.90/0.98      | v1_funct_1(X0) != iProver_top
% 3.90/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_13731,plain,
% 3.90/0.98      ( k9_relat_1(sK3,k10_relat_1(sK3,X0)) = X0
% 3.90/0.98      | r1_tarski(X0,sK2) != iProver_top
% 3.90/0.98      | v1_funct_1(sK3) != iProver_top
% 3.90/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_7882,c_2453]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_13861,plain,
% 3.90/0.98      ( k9_relat_1(sK3,k10_relat_1(sK3,X0)) = X0
% 3.90/0.98      | r1_tarski(X0,sK2) != iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_13731,c_60,c_62,c_2868]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_13870,plain,
% 3.90/0.98      ( k9_relat_1(sK3,k10_relat_1(sK3,k1_relat_1(sK3))) = k1_relat_1(sK3)
% 3.90/0.98      | sK2 = k1_xboole_0
% 3.90/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_6235,c_13861]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3272,plain,
% 3.90/0.98      ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) | r1_tarski(X0,k1_relat_1(sK3)) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3278,plain,
% 3.90/0.98      ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) = iProver_top
% 3.90/0.98      | r1_tarski(X0,k1_relat_1(sK3)) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_3272]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3280,plain,
% 3.90/0.98      ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) = iProver_top
% 3.90/0.98      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) = iProver_top ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_3278]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6609,plain,
% 3.90/0.98      ( ~ r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) | ~ r1_tarski(X0,k1_xboole_0) ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_656]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6615,plain,
% 3.90/0.98      ( r2_hidden(sK0(X0,k1_relat_1(sK3)),X0) != iProver_top
% 3.90/0.98      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_6609]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6617,plain,
% 3.90/0.98      ( r2_hidden(sK0(k1_xboole_0,k1_relat_1(sK3)),k1_xboole_0) != iProver_top
% 3.90/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_6615]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4,plain,
% 3.90/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2469,plain,
% 3.90/0.98      ( X0 = X1
% 3.90/0.98      | r1_tarski(X1,X0) != iProver_top
% 3.90/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11649,plain,
% 3.90/0.98      ( k1_relat_1(sK3) = X0
% 3.90/0.98      | sK2 = k1_xboole_0
% 3.90/0.98      | r1_tarski(X0,k1_relat_1(sK3)) != iProver_top
% 3.90/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_6235,c_2469]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11717,plain,
% 3.90/0.98      ( k1_relat_1(sK3) = k1_xboole_0
% 3.90/0.98      | sK2 = k1_xboole_0
% 3.90/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.90/0.98      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) != iProver_top ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_11649]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_11889,plain,
% 3.90/0.98      ( ~ v1_relat_1(k2_funct_1(sK3))
% 3.90/0.98      | k1_relat_1(sK3) != k1_xboole_0
% 3.90/0.98      | sK2 = k1_xboole_0 ),
% 3.90/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_11876]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_13117,plain,
% 3.90/0.98      ( sK2 = k1_xboole_0 | k1_relat_1(sK3) != k1_xboole_0 ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_11876,c_60,c_62,c_2834,c_2868]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_13118,plain,
% 3.90/0.98      ( k1_relat_1(sK3) != k1_xboole_0 | sK2 = k1_xboole_0 ),
% 3.90/0.98      inference(renaming,[status(thm)],[c_13117]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_15913,plain,
% 3.90/0.98      ( sK2 = k1_xboole_0 | r1_tarski(sK2,k1_xboole_0) != iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_13870,c_60,c_62,c_174,c_2834,c_2868,c_3280,c_6617,c_11717,
% 3.90/0.98                 c_11876]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_17671,plain,
% 3.90/0.98      ( sK2 = k1_xboole_0 ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_17644,c_15913]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2941,plain,
% 3.90/0.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 3.90/0.98      | r1_tarski(k1_relat_1(sK3),sK1) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_2940]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_14011,plain,
% 3.90/0.98      ( v1_funct_2(k2_funct_1(sK3),sK2,sK1) != iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_13949,c_62,c_2941]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_17786,plain,
% 3.90/0.98      ( v1_funct_2(k2_funct_1(sK3),k1_xboole_0,sK1) != iProver_top ),
% 3.90/0.98      inference(demodulation,[status(thm)],[c_17671,c_14011]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_17,plain,
% 3.90/0.98      ( ~ v1_relat_1(X0) | k2_relat_1(X0) != k1_xboole_0 | k1_xboole_0 = X0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2463,plain,
% 3.90/0.98      ( k2_relat_1(X0) != k1_xboole_0
% 3.90/0.98      | k1_xboole_0 = X0
% 3.90/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_8096,plain,
% 3.90/0.98      ( sK2 != k1_xboole_0
% 3.90/0.98      | sK3 = k1_xboole_0
% 3.90/0.98      | v1_relat_1(sK3) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_7882,c_2463]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_8570,plain,
% 3.90/0.98      ( sK3 = k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_8096,c_62,c_2868]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_8571,plain,
% 3.90/0.98      ( sK2 != k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.90/0.98      inference(renaming,[status(thm)],[c_8570]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_17812,plain,
% 3.90/0.98      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.90/0.98      inference(demodulation,[status(thm)],[c_17671,c_8571]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_17849,plain,
% 3.90/0.98      ( sK3 = k1_xboole_0 ),
% 3.90/0.98      inference(equality_resolution_simp,[status(thm)],[c_17812]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_17948,plain,
% 3.90/0.98      ( v1_funct_2(k2_funct_1(k1_xboole_0),k1_xboole_0,sK1) != iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_17786,c_17849]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_24,plain,
% 3.90/0.98      ( k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f146]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_30,plain,
% 3.90/0.98      ( v1_relat_1(k6_partfun1(X0)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f150]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2455,plain,
% 3.90/0.98      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_23,plain,
% 3.90/0.98      ( ~ v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f145]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2459,plain,
% 3.90/0.98      ( k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0
% 3.90/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4091,plain,
% 3.90/0.98      ( k5_relat_1(k6_partfun1(X0),k6_partfun1(k2_relat_1(k6_partfun1(X0)))) = k6_partfun1(X0) ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_2455,c_2459]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_21,plain,
% 3.90/0.98      ( k2_relat_1(k6_partfun1(X0)) = X0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f143]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4097,plain,
% 3.90/0.98      ( k5_relat_1(k6_partfun1(X0),k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_4091,c_21]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_36,plain,
% 3.90/0.98      ( ~ v2_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X1)
% 3.90/0.98      | ~ v1_relat_1(X1)
% 3.90/0.98      | ~ v1_relat_1(X0)
% 3.90/0.98      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.90/0.98      | k2_funct_1(X0) = X1
% 3.90/0.98      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 3.90/0.98      inference(cnf_transformation,[],[f152]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_33,plain,
% 3.90/0.98      ( v2_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X1)
% 3.90/0.98      | ~ v1_relat_1(X1)
% 3.90/0.98      | ~ v1_relat_1(X0)
% 3.90/0.98      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f151]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_308,plain,
% 3.90/0.98      ( ~ v1_funct_1(X0)
% 3.90/0.98      | ~ v1_funct_1(X1)
% 3.90/0.98      | ~ v1_relat_1(X1)
% 3.90/0.98      | ~ v1_relat_1(X0)
% 3.90/0.98      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.90/0.98      | k2_funct_1(X0) = X1
% 3.90/0.98      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 3.90/0.98      inference(global_propositional_subsumption,[status(thm)],[c_36,c_33]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2433,plain,
% 3.90/0.98      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 3.90/0.98      | k2_funct_1(X0) = X1
% 3.90/0.98      | k2_relat_1(X0) != k1_relat_1(X1)
% 3.90/0.98      | v1_funct_1(X0) != iProver_top
% 3.90/0.98      | v1_funct_1(X1) != iProver_top
% 3.90/0.98      | v1_relat_1(X0) != iProver_top
% 3.90/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_308]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4231,plain,
% 3.90/0.98      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
% 3.90/0.98      | k6_partfun1(k1_relat_1(k6_partfun1(X0))) != k6_partfun1(X0)
% 3.90/0.98      | k2_relat_1(k6_partfun1(X0)) != k1_relat_1(k6_partfun1(X0))
% 3.90/0.98      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 3.90/0.98      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_4097,c_2433]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_22,plain,
% 3.90/0.98      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.90/0.98      inference(cnf_transformation,[],[f144]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4237,plain,
% 3.90/0.98      ( X0 != X0
% 3.90/0.98      | k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
% 3.90/0.98      | k6_partfun1(X0) != k6_partfun1(X0)
% 3.90/0.98      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 3.90/0.98      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_4231,c_21,c_22]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_4238,plain,
% 3.90/0.98      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0)
% 3.90/0.98      | v1_funct_1(k6_partfun1(X0)) != iProver_top
% 3.90/0.98      | v1_relat_1(k6_partfun1(X0)) != iProver_top ),
% 3.90/0.98      inference(equality_resolution_simp,[status(thm)],[c_4237]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_116,plain,
% 3.90/0.98      ( v1_relat_1(k6_partfun1(X0)) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_27,plain,
% 3.90/0.98      ( v1_funct_1(k6_partfun1(X0)) ),
% 3.90/0.98      inference(cnf_transformation,[],[f147]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_123,plain,
% 3.90/0.98      ( v1_funct_1(k6_partfun1(X0)) = iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_15392,plain,
% 3.90/0.98      ( k2_funct_1(k6_partfun1(X0)) = k6_partfun1(X0) ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_4238,c_116,c_123]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_15412,plain,
% 3.90/0.98      ( k2_funct_1(k1_xboole_0) = k6_partfun1(k1_xboole_0) ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_24,c_15392]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_15416,plain,
% 3.90/0.98      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_15412,c_24]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_17950,plain,
% 3.90/0.98      ( v1_funct_2(k1_xboole_0,k1_xboole_0,sK1) != iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_17948,c_15416]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_41,plain,
% 3.90/0.98      ( v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ v1_partfun1(X0,X1)
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ v1_funct_1(X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f124]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_44,plain,
% 3.90/0.98      ( v1_partfun1(k6_partfun1(X0),X0) ),
% 3.90/0.98      inference(cnf_transformation,[],[f125]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_670,plain,
% 3.90/0.98      ( v1_funct_2(X0,X1,X2)
% 3.90/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.90/0.98      | ~ v1_funct_1(X0)
% 3.90/0.98      | X3 != X1
% 3.90/0.98      | k6_partfun1(X3) != X0 ),
% 3.90/0.98      inference(resolution_lifted,[status(thm)],[c_41,c_44]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_671,plain,
% 3.90/0.98      ( v1_funct_2(k6_partfun1(X0),X0,X1)
% 3.90/0.98      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.90/0.98      | ~ v1_funct_1(k6_partfun1(X0)) ),
% 3.90/0.98      inference(unflattening,[status(thm)],[c_670]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_675,plain,
% 3.90/0.98      ( ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.90/0.98      | v1_funct_2(k6_partfun1(X0),X0,X1) ),
% 3.90/0.98      inference(global_propositional_subsumption,[status(thm)],[c_671,c_27]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_676,plain,
% 3.90/0.98      ( v1_funct_2(k6_partfun1(X0),X0,X1)
% 3.90/0.98      | ~ m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.90/0.98      inference(renaming,[status(thm)],[c_675]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_2431,plain,
% 3.90/0.98      ( v1_funct_2(k6_partfun1(X0),X0,X1) = iProver_top
% 3.90/0.98      | m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3492,plain,
% 3.90/0.98      ( v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,X0) = iProver_top
% 3.90/0.98      | m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.90/0.98      inference(superposition,[status(thm)],[c_8,c_2431]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_3495,plain,
% 3.90/0.98      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top
% 3.90/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.90/0.98      inference(light_normalisation,[status(thm)],[c_3492,c_24]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_167,plain,
% 3.90/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.90/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.90/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_169,plain,
% 3.90/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.90/0.98      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.90/0.98      inference(instantiation,[status(thm)],[c_167]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_6061,plain,
% 3.90/0.98      ( v1_funct_2(k1_xboole_0,k1_xboole_0,X0) = iProver_top ),
% 3.90/0.98      inference(global_propositional_subsumption,
% 3.90/0.98                [status(thm)],
% 3.90/0.98                [c_3495,c_169,c_174]) ).
% 3.90/0.98  
% 3.90/0.98  cnf(c_18491,plain,
% 3.90/0.98      ( $false ),
% 3.90/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_17950,c_6061]) ).
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.90/0.98  
% 3.90/0.98  ------                               Statistics
% 3.90/0.98  
% 3.90/0.98  ------ General
% 3.90/0.98  
% 3.90/0.98  abstr_ref_over_cycles:                  0
% 3.90/0.98  abstr_ref_under_cycles:                 0
% 3.90/0.98  gc_basic_clause_elim:                   0
% 3.90/0.98  forced_gc_time:                         0
% 3.90/0.98  parsing_time:                           0.01
% 3.90/0.98  unif_index_cands_time:                  0.
% 3.90/0.98  unif_index_add_time:                    0.
% 3.90/0.98  orderings_time:                         0.
% 3.90/0.98  out_proof_time:                         0.02
% 3.90/0.98  total_time:                             0.434
% 3.90/0.98  num_of_symbols:                         56
% 3.90/0.98  num_of_terms:                           14347
% 3.90/0.98  
% 3.90/0.98  ------ Preprocessing
% 3.90/0.98  
% 3.90/0.98  num_of_splits:                          0
% 3.90/0.98  num_of_split_atoms:                     0
% 3.90/0.98  num_of_reused_defs:                     0
% 3.90/0.98  num_eq_ax_congr_red:                    18
% 3.90/0.98  num_of_sem_filtered_clauses:            1
% 3.90/0.98  num_of_subtypes:                        0
% 3.90/0.98  monotx_restored_types:                  0
% 3.90/0.98  sat_num_of_epr_types:                   0
% 3.90/0.98  sat_num_of_non_cyclic_types:            0
% 3.90/0.98  sat_guarded_non_collapsed_types:        0
% 3.90/0.98  num_pure_diseq_elim:                    0
% 3.90/0.98  simp_replaced_by:                       0
% 3.90/0.98  res_preprocessed:                       243
% 3.90/0.98  prep_upred:                             0
% 3.90/0.98  prep_unflattend:                        17
% 3.90/0.98  smt_new_axioms:                         0
% 3.90/0.98  pred_elim_cands:                        7
% 3.90/0.98  pred_elim:                              3
% 3.90/0.98  pred_elim_cl:                           4
% 3.90/0.98  pred_elim_cycles:                       5
% 3.90/0.98  merged_defs:                            8
% 3.90/0.98  merged_defs_ncl:                        0
% 3.90/0.98  bin_hyper_res:                          9
% 3.90/0.98  prep_cycles:                            4
% 3.90/0.98  pred_elim_time:                         0.009
% 3.90/0.98  splitting_time:                         0.
% 3.90/0.98  sem_filter_time:                        0.
% 3.90/0.98  monotx_time:                            0.
% 3.90/0.98  subtype_inf_time:                       0.
% 3.90/0.98  
% 3.90/0.98  ------ Problem properties
% 3.90/0.98  
% 3.90/0.98  clauses:                                50
% 3.90/0.98  conjectures:                            6
% 3.90/0.98  epr:                                    7
% 3.90/0.98  horn:                                   46
% 3.90/0.98  ground:                                 7
% 3.90/0.98  unary:                                  15
% 3.90/0.98  binary:                                 12
% 3.90/0.98  lits:                                   130
% 3.90/0.98  lits_eq:                                32
% 3.90/0.98  fd_pure:                                0
% 3.90/0.98  fd_pseudo:                              0
% 3.90/0.98  fd_cond:                                5
% 3.90/0.98  fd_pseudo_cond:                         2
% 3.90/0.98  ac_symbols:                             0
% 3.90/0.98  
% 3.90/0.98  ------ Propositional Solver
% 3.90/0.98  
% 3.90/0.98  prop_solver_calls:                      27
% 3.90/0.98  prop_fast_solver_calls:                 2017
% 3.90/0.98  smt_solver_calls:                       0
% 3.90/0.98  smt_fast_solver_calls:                  0
% 3.90/0.98  prop_num_of_clauses:                    6043
% 3.90/0.98  prop_preprocess_simplified:             15813
% 3.90/0.98  prop_fo_subsumed:                       97
% 3.90/0.98  prop_solver_time:                       0.
% 3.90/0.98  smt_solver_time:                        0.
% 3.90/0.98  smt_fast_solver_time:                   0.
% 3.90/0.98  prop_fast_solver_time:                  0.
% 3.90/0.98  prop_unsat_core_time:                   0.
% 3.90/0.98  
% 3.90/0.98  ------ QBF
% 3.90/0.98  
% 3.90/0.98  qbf_q_res:                              0
% 3.90/0.98  qbf_num_tautologies:                    0
% 3.90/0.98  qbf_prep_cycles:                        0
% 3.90/0.98  
% 3.90/0.98  ------ BMC1
% 3.90/0.98  
% 3.90/0.98  bmc1_current_bound:                     -1
% 3.90/0.98  bmc1_last_solved_bound:                 -1
% 3.90/0.98  bmc1_unsat_core_size:                   -1
% 3.90/0.98  bmc1_unsat_core_parents_size:           -1
% 3.90/0.98  bmc1_merge_next_fun:                    0
% 3.90/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.90/0.98  
% 3.90/0.98  ------ Instantiation
% 3.90/0.98  
% 3.90/0.98  inst_num_of_clauses:                    1796
% 3.90/0.98  inst_num_in_passive:                    308
% 3.90/0.98  inst_num_in_active:                     839
% 3.90/0.98  inst_num_in_unprocessed:                649
% 3.90/0.98  inst_num_of_loops:                      1010
% 3.90/0.98  inst_num_of_learning_restarts:          0
% 3.90/0.98  inst_num_moves_active_passive:          166
% 3.90/0.98  inst_lit_activity:                      0
% 3.90/0.98  inst_lit_activity_moves:                0
% 3.90/0.98  inst_num_tautologies:                   0
% 3.90/0.98  inst_num_prop_implied:                  0
% 3.90/0.98  inst_num_existing_simplified:           0
% 3.90/0.98  inst_num_eq_res_simplified:             0
% 3.90/0.98  inst_num_child_elim:                    0
% 3.90/0.98  inst_num_of_dismatching_blockings:      882
% 3.90/0.98  inst_num_of_non_proper_insts:           1831
% 3.90/0.98  inst_num_of_duplicates:                 0
% 3.90/0.98  inst_inst_num_from_inst_to_res:         0
% 3.90/0.98  inst_dismatching_checking_time:         0.
% 3.90/0.98  
% 3.90/0.98  ------ Resolution
% 3.90/0.98  
% 3.90/0.98  res_num_of_clauses:                     0
% 3.90/0.98  res_num_in_passive:                     0
% 3.90/0.98  res_num_in_active:                      0
% 3.90/0.98  res_num_of_loops:                       247
% 3.90/0.98  res_forward_subset_subsumed:            115
% 3.90/0.98  res_backward_subset_subsumed:           8
% 3.90/0.98  res_forward_subsumed:                   0
% 3.90/0.98  res_backward_subsumed:                  0
% 3.90/0.98  res_forward_subsumption_resolution:     2
% 3.90/0.98  res_backward_subsumption_resolution:    0
% 3.90/0.98  res_clause_to_clause_subsumption:       1462
% 3.90/0.98  res_orphan_elimination:                 0
% 3.90/0.98  res_tautology_del:                      96
% 3.90/0.98  res_num_eq_res_simplified:              0
% 3.90/0.98  res_num_sel_changes:                    0
% 3.90/0.98  res_moves_from_active_to_pass:          0
% 3.90/0.98  
% 3.90/0.98  ------ Superposition
% 3.90/0.98  
% 3.90/0.98  sup_time_total:                         0.
% 3.90/0.98  sup_time_generating:                    0.
% 3.90/0.98  sup_time_sim_full:                      0.
% 3.90/0.98  sup_time_sim_immed:                     0.
% 3.90/0.98  
% 3.90/0.98  sup_num_of_clauses:                     250
% 3.90/0.98  sup_num_in_active:                      90
% 3.90/0.98  sup_num_in_passive:                     160
% 3.90/0.98  sup_num_of_loops:                       201
% 3.90/0.98  sup_fw_superposition:                   285
% 3.90/0.98  sup_bw_superposition:                   240
% 3.90/0.98  sup_immediate_simplified:               301
% 3.90/0.98  sup_given_eliminated:                   2
% 3.90/0.98  comparisons_done:                       0
% 3.90/0.98  comparisons_avoided:                    9
% 3.90/0.98  
% 3.90/0.98  ------ Simplifications
% 3.90/0.98  
% 3.90/0.98  
% 3.90/0.98  sim_fw_subset_subsumed:                 46
% 3.90/0.98  sim_bw_subset_subsumed:                 45
% 3.90/0.98  sim_fw_subsumed:                        56
% 3.90/0.98  sim_bw_subsumed:                        5
% 3.90/0.98  sim_fw_subsumption_res:                 7
% 3.90/0.98  sim_bw_subsumption_res:                 0
% 3.90/0.98  sim_tautology_del:                      18
% 3.90/0.98  sim_eq_tautology_del:                   53
% 3.90/0.98  sim_eq_res_simp:                        8
% 3.90/0.98  sim_fw_demodulated:                     34
% 3.90/0.98  sim_bw_demodulated:                     106
% 3.90/0.98  sim_light_normalised:                   210
% 3.90/0.98  sim_joinable_taut:                      0
% 3.90/0.98  sim_joinable_simp:                      0
% 3.90/0.98  sim_ac_normalised:                      0
% 3.90/0.98  sim_smt_subsumption:                    0
% 3.90/0.98  
%------------------------------------------------------------------------------
