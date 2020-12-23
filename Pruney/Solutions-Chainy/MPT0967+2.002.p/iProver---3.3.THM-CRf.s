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
% DateTime   : Thu Dec  3 12:00:37 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_754)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

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

fof(f57,plain,(
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

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f22,conjecture,(
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

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(X1,X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f43,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f44,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f43])).

fof(f58,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(X1,X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
        | ~ v1_funct_2(sK5,sK2,sK4)
        | ~ v1_funct_1(sK5) )
      & ( k1_xboole_0 = sK2
        | k1_xboole_0 != sK3 )
      & r1_tarski(sK3,sK4)
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
      | ~ v1_funct_2(sK5,sK2,sK4)
      | ~ v1_funct_1(sK5) )
    & ( k1_xboole_0 = sK2
      | k1_xboole_0 != sK3 )
    & r1_tarski(sK3,sK4)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f44,f58])).

fof(f100,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f59])).

fof(f101,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f59])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,(
    r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f104,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_2(sK5,sK2,sK4)
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f99,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f59])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f103,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f59])).

fof(f5,axiom,(
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
    inference(nnf_transformation,[],[f5])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f47])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f107,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f68])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f108,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_43,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_604,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_43])).

cnf(c_605,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_604])).

cnf(c_42,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_607,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_605,c_42])).

cnf(c_1558,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1564,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3099,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_1558,c_1564])).

cnf(c_3134,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_607,c_3099])).

cnf(c_41,negated_conjecture,
    ( r1_tarski(sK3,sK4) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1559,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_23,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1565,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2697,plain,
    ( v5_relat_1(sK5,sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_1565])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X0,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1569,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3527,plain,
    ( v5_relat_1(sK5,X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2697,c_1569])).

cnf(c_47,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_1900,plain,
    ( v5_relat_1(sK5,sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_1901,plain,
    ( v5_relat_1(sK5,sK3) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1900])).

cnf(c_1957,plain,
    ( v5_relat_1(sK5,X0)
    | ~ v5_relat_1(sK5,sK3)
    | ~ r1_tarski(sK3,X0)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1961,plain,
    ( v5_relat_1(sK5,X0) = iProver_top
    | v5_relat_1(sK5,sK3) != iProver_top
    | r1_tarski(sK3,X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1957])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1885,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2015,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
    | v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1885])).

cnf(c_2016,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(c_16,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2081,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2082,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2081])).

cnf(c_4001,plain,
    ( r1_tarski(sK3,X0) != iProver_top
    | v5_relat_1(sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3527,c_47,c_1901,c_1961,c_2016,c_2082])).

cnf(c_4002,plain,
    ( v5_relat_1(sK5,X0) = iProver_top
    | r1_tarski(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4001])).

cnf(c_4010,plain,
    ( v5_relat_1(sK5,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1559,c_4002])).

cnf(c_15,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1571,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_24,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_457,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_24,c_13])).

cnf(c_1556,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_457])).

cnf(c_2252,plain,
    ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1558,c_1556])).

cnf(c_1909,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | r1_tarski(k1_relat_1(sK5),sK2)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_457])).

cnf(c_1910,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | r1_tarski(k1_relat_1(sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1909])).

cnf(c_2430,plain,
    ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2252,c_47,c_1910,c_2016,c_2082])).

cnf(c_26,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1563,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3098,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1563,c_1564])).

cnf(c_11146,plain,
    ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2430,c_3098])).

cnf(c_11306,plain,
    ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
    | k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11146,c_47,c_2016,c_2082])).

cnf(c_11307,plain,
    ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11306])).

cnf(c_11315,plain,
    ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
    | v5_relat_1(sK5,X0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1571,c_11307])).

cnf(c_11628,plain,
    ( v5_relat_1(sK5,X0) != iProver_top
    | k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_11315,c_47,c_2016,c_2082])).

cnf(c_11629,plain,
    ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
    | v5_relat_1(sK5,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_11628])).

cnf(c_11638,plain,
    ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_4010,c_11629])).

cnf(c_33,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_39,negated_conjecture,
    ( ~ v1_funct_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_44,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_223,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ v1_funct_2(sK5,sK2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_39,c_44])).

cnf(c_224,negated_conjecture,
    ( ~ v1_funct_2(sK5,sK2,sK4)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
    inference(renaming,[status(thm)],[c_223])).

cnf(c_591,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK4 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_224])).

cnf(c_592,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | k1_relset_1(sK2,sK4,sK5) != sK2
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_591])).

cnf(c_1549,plain,
    ( k1_relset_1(sK2,sK4,sK5) != sK2
    | k1_xboole_0 = sK4
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_592])).

cnf(c_11736,plain,
    ( k1_relat_1(sK5) != sK2
    | sK4 = k1_xboole_0
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11638,c_1549])).

cnf(c_48,plain,
    ( r1_tarski(sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_632,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | sK3 != sK4
    | sK2 != sK2
    | sK5 != sK5 ),
    inference(resolution_lifted,[status(thm)],[c_224,c_43])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1906,plain,
    ( ~ r1_tarski(sK3,sK4)
    | ~ r1_tarski(sK4,sK3)
    | sK3 = sK4 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_951,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1993,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_951])).

cnf(c_2022,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_951])).

cnf(c_2042,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_951])).

cnf(c_2098,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
    | ~ r1_tarski(k2_relat_1(sK5),sK4)
    | ~ r1_tarski(k1_relat_1(sK5),sK2)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2099,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top
    | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top
    | r1_tarski(k1_relat_1(sK5),sK2) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2098])).

cnf(c_2203,plain,
    ( ~ v5_relat_1(sK5,sK4)
    | r1_tarski(k2_relat_1(sK5),sK4)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2204,plain,
    ( v5_relat_1(sK5,sK4) != iProver_top
    | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2203])).

cnf(c_2213,plain,
    ( ~ v5_relat_1(sK5,sK3)
    | v5_relat_1(sK5,sK4)
    | ~ r1_tarski(sK3,sK4)
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_1957])).

cnf(c_2214,plain,
    ( v5_relat_1(sK5,sK3) != iProver_top
    | v5_relat_1(sK5,sK4) = iProver_top
    | r1_tarski(sK3,sK4) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_4,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_2513,plain,
    ( r1_tarski(k1_xboole_0,sK3) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_954,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2031,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK4,sK3)
    | sK3 != X1
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_2537,plain,
    ( ~ r1_tarski(X0,sK3)
    | r1_tarski(sK4,sK3)
    | sK3 != sK3
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_2539,plain,
    ( r1_tarski(sK4,sK3)
    | ~ r1_tarski(k1_xboole_0,sK3)
    | sK3 != sK3
    | sK4 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2537])).

cnf(c_11740,plain,
    ( k1_relat_1(sK5) != sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11736,c_42,c_47,c_41,c_48,c_754,c_1900,c_1901,c_1906,c_1909,c_1910,c_2015,c_2016,c_2042,c_2081,c_2082,c_2098,c_2099,c_2203,c_2204,c_2213,c_2214,c_2513,c_2539])).

cnf(c_11743,plain,
    ( sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3134,c_11740])).

cnf(c_40,negated_conjecture,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f103])).

cnf(c_11946,plain,
    ( sK2 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11743,c_40])).

cnf(c_11947,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_11946])).

cnf(c_12371,plain,
    ( k1_relat_1(sK5) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11947,c_11740])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f107])).

cnf(c_2869,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1563])).

cnf(c_4878,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2430,c_2869])).

cnf(c_5273,plain,
    ( r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4878,c_47,c_2016,c_2082])).

cnf(c_5274,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5273])).

cnf(c_5279,plain,
    ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1571,c_5274])).

cnf(c_5437,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | v5_relat_1(sK5,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5279,c_47,c_2016,c_2082])).

cnf(c_5438,plain,
    ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(renaming,[status(thm)],[c_5437])).

cnf(c_2254,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6,c_1556])).

cnf(c_5445,plain,
    ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5438,c_2254])).

cnf(c_8089,plain,
    ( r1_tarski(k1_relat_1(sK5),X0) = iProver_top
    | v5_relat_1(sK5,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5445,c_47,c_2016,c_2082])).

cnf(c_8090,plain,
    ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(sK5),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8089])).

cnf(c_1577,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1579,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3656,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1577,c_1579])).

cnf(c_8099,plain,
    ( k1_relat_1(sK5) = k1_xboole_0
    | v5_relat_1(sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8090,c_3656])).

cnf(c_8131,plain,
    ( ~ v5_relat_1(sK5,k1_xboole_0)
    | k1_relat_1(sK5) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8099])).

cnf(c_4003,plain,
    ( v5_relat_1(sK5,X0)
    | ~ r1_tarski(sK3,X0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4002])).

cnf(c_4005,plain,
    ( v5_relat_1(sK5,k1_xboole_0)
    | ~ r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4003])).

cnf(c_2216,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK3,X2)
    | X2 != X1
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_954])).

cnf(c_2218,plain,
    ( r1_tarski(sK3,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2216])).

cnf(c_132,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_7,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f108])).

cnf(c_127,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_8,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_126,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_12371,c_11736,c_8131,c_4005,c_3134,c_2539,c_2513,c_2218,c_2214,c_2213,c_2204,c_2203,c_2099,c_2098,c_2082,c_2081,c_2042,c_2022,c_2016,c_2015,c_1993,c_1910,c_1909,c_1906,c_1901,c_1900,c_632,c_132,c_127,c_126,c_48,c_41,c_47,c_42])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:33:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.04/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.99  
% 3.04/0.99  ------  iProver source info
% 3.04/0.99  
% 3.04/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.99  git: non_committed_changes: false
% 3.04/0.99  git: last_make_outside_of_git: false
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     num_symb
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       true
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  ------ Parsing...
% 3.04/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/0.99  ------ Proving...
% 3.04/0.99  ------ Problem Properties 
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  clauses                                 42
% 3.04/0.99  conjectures                             3
% 3.04/0.99  EPR                                     10
% 3.04/0.99  Horn                                    36
% 3.04/0.99  unary                                   10
% 3.04/0.99  binary                                  9
% 3.04/0.99  lits                                    108
% 3.04/0.99  lits eq                                 43
% 3.04/0.99  fd_pure                                 0
% 3.04/0.99  fd_pseudo                               0
% 3.04/0.99  fd_cond                                 2
% 3.04/0.99  fd_pseudo_cond                          1
% 3.04/0.99  AC symbols                              0
% 3.04/0.99  
% 3.04/0.99  ------ Schedule dynamic 5 is on 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  Current options:
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     none
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       false
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ Proving...
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS status Theorem for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  fof(f20,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f39,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f20])).
% 3.04/0.99  
% 3.04/0.99  fof(f40,plain,(
% 3.04/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(flattening,[],[f39])).
% 3.04/0.99  
% 3.04/0.99  fof(f57,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(nnf_transformation,[],[f40])).
% 3.04/0.99  
% 3.04/0.99  fof(f90,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f57])).
% 3.04/0.99  
% 3.04/0.99  fof(f22,conjecture,(
% 3.04/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f23,negated_conjecture,(
% 3.04/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.04/0.99    inference(negated_conjecture,[],[f22])).
% 3.04/0.99  
% 3.04/0.99  fof(f43,plain,(
% 3.04/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.04/0.99    inference(ennf_transformation,[],[f23])).
% 3.04/0.99  
% 3.04/0.99  fof(f44,plain,(
% 3.04/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.04/0.99    inference(flattening,[],[f43])).
% 3.04/0.99  
% 3.04/0.99  fof(f58,plain,(
% 3.04/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_tarski(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f59,plain,(
% 3.04/0.99    (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)) & (k1_xboole_0 = sK2 | k1_xboole_0 != sK3) & r1_tarski(sK3,sK4) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f44,f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f100,plain,(
% 3.04/0.99    v1_funct_2(sK5,sK2,sK3)),
% 3.04/0.99    inference(cnf_transformation,[],[f59])).
% 3.04/0.99  
% 3.04/0.99  fof(f101,plain,(
% 3.04/0.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.04/0.99    inference(cnf_transformation,[],[f59])).
% 3.04/0.99  
% 3.04/0.99  fof(f17,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f35,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f17])).
% 3.04/0.99  
% 3.04/0.99  fof(f85,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f35])).
% 3.04/0.99  
% 3.04/0.99  fof(f102,plain,(
% 3.04/0.99    r1_tarski(sK3,sK4)),
% 3.04/0.99    inference(cnf_transformation,[],[f59])).
% 3.04/0.99  
% 3.04/0.99  fof(f16,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f34,plain,(
% 3.04/0.99    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f16])).
% 3.04/0.99  
% 3.04/0.99  fof(f84,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f34])).
% 3.04/0.99  
% 3.04/0.99  fof(f12,axiom,(
% 3.04/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f30,plain,(
% 3.04/0.99    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | (~v5_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 3.04/0.99    inference(ennf_transformation,[],[f12])).
% 3.04/0.99  
% 3.04/0.99  fof(f31,plain,(
% 3.04/0.99    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 3.04/0.99    inference(flattening,[],[f30])).
% 3.04/0.99  
% 3.04/0.99  fof(f77,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f31])).
% 3.04/0.99  
% 3.04/0.99  fof(f8,axiom,(
% 3.04/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.04/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f27,plain,(
% 3.04/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.04/1.00    inference(ennf_transformation,[],[f8])).
% 3.04/1.00  
% 3.04/1.00  fof(f71,plain,(
% 3.04/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f27])).
% 3.04/1.00  
% 3.04/1.00  fof(f11,axiom,(
% 3.04/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f76,plain,(
% 3.04/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.04/1.00    inference(cnf_transformation,[],[f11])).
% 3.04/1.00  
% 3.04/1.00  fof(f10,axiom,(
% 3.04/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f29,plain,(
% 3.04/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.04/1.00    inference(ennf_transformation,[],[f10])).
% 3.04/1.00  
% 3.04/1.00  fof(f50,plain,(
% 3.04/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.04/1.00    inference(nnf_transformation,[],[f29])).
% 3.04/1.00  
% 3.04/1.00  fof(f74,plain,(
% 3.04/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f50])).
% 3.04/1.00  
% 3.04/1.00  fof(f83,plain,(
% 3.04/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/1.00    inference(cnf_transformation,[],[f34])).
% 3.04/1.00  
% 3.04/1.00  fof(f9,axiom,(
% 3.04/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f28,plain,(
% 3.04/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.04/1.00    inference(ennf_transformation,[],[f9])).
% 3.04/1.00  
% 3.04/1.00  fof(f49,plain,(
% 3.04/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.04/1.00    inference(nnf_transformation,[],[f28])).
% 3.04/1.00  
% 3.04/1.00  fof(f72,plain,(
% 3.04/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f49])).
% 3.04/1.00  
% 3.04/1.00  fof(f18,axiom,(
% 3.04/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f36,plain,(
% 3.04/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.04/1.00    inference(ennf_transformation,[],[f18])).
% 3.04/1.00  
% 3.04/1.00  fof(f37,plain,(
% 3.04/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.04/1.00    inference(flattening,[],[f36])).
% 3.04/1.00  
% 3.04/1.00  fof(f86,plain,(
% 3.04/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f37])).
% 3.04/1.00  
% 3.04/1.00  fof(f92,plain,(
% 3.04/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/1.00    inference(cnf_transformation,[],[f57])).
% 3.04/1.00  
% 3.04/1.00  fof(f104,plain,(
% 3.04/1.00    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) | ~v1_funct_2(sK5,sK2,sK4) | ~v1_funct_1(sK5)),
% 3.04/1.00    inference(cnf_transformation,[],[f59])).
% 3.04/1.00  
% 3.04/1.00  fof(f99,plain,(
% 3.04/1.00    v1_funct_1(sK5)),
% 3.04/1.00    inference(cnf_transformation,[],[f59])).
% 3.04/1.00  
% 3.04/1.00  fof(f2,axiom,(
% 3.04/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f45,plain,(
% 3.04/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.04/1.00    inference(nnf_transformation,[],[f2])).
% 3.04/1.00  
% 3.04/1.00  fof(f46,plain,(
% 3.04/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.04/1.00    inference(flattening,[],[f45])).
% 3.04/1.00  
% 3.04/1.00  fof(f63,plain,(
% 3.04/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f46])).
% 3.04/1.00  
% 3.04/1.00  fof(f3,axiom,(
% 3.04/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f64,plain,(
% 3.04/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f3])).
% 3.04/1.00  
% 3.04/1.00  fof(f103,plain,(
% 3.04/1.00    k1_xboole_0 = sK2 | k1_xboole_0 != sK3),
% 3.04/1.00    inference(cnf_transformation,[],[f59])).
% 3.04/1.00  
% 3.04/1.00  fof(f5,axiom,(
% 3.04/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.04/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.04/1.00  
% 3.04/1.00  fof(f47,plain,(
% 3.04/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.04/1.00    inference(nnf_transformation,[],[f5])).
% 3.04/1.00  
% 3.04/1.00  fof(f48,plain,(
% 3.04/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.04/1.00    inference(flattening,[],[f47])).
% 3.04/1.00  
% 3.04/1.00  fof(f68,plain,(
% 3.04/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.04/1.00    inference(cnf_transformation,[],[f48])).
% 3.04/1.00  
% 3.04/1.00  fof(f107,plain,(
% 3.04/1.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.04/1.00    inference(equality_resolution,[],[f68])).
% 3.04/1.00  
% 3.04/1.00  fof(f67,plain,(
% 3.04/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.04/1.00    inference(cnf_transformation,[],[f48])).
% 3.04/1.00  
% 3.04/1.00  fof(f108,plain,(
% 3.04/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.04/1.00    inference(equality_resolution,[],[f67])).
% 3.04/1.00  
% 3.04/1.00  fof(f66,plain,(
% 3.04/1.00    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.04/1.00    inference(cnf_transformation,[],[f48])).
% 3.04/1.00  
% 3.04/1.00  cnf(c_35,plain,
% 3.04/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.04/1.00      | k1_xboole_0 = X2 ),
% 3.04/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_43,negated_conjecture,
% 3.04/1.00      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.04/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_604,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.04/1.00      | sK3 != X2
% 3.04/1.00      | sK2 != X1
% 3.04/1.00      | sK5 != X0
% 3.04/1.00      | k1_xboole_0 = X2 ),
% 3.04/1.00      inference(resolution_lifted,[status(thm)],[c_35,c_43]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_605,plain,
% 3.04/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.04/1.00      | k1_relset_1(sK2,sK3,sK5) = sK2
% 3.04/1.00      | k1_xboole_0 = sK3 ),
% 3.04/1.00      inference(unflattening,[status(thm)],[c_604]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_42,negated_conjecture,
% 3.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.04/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_607,plain,
% 3.04/1.00      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_605,c_42]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1558,plain,
% 3.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_25,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1564,plain,
% 3.04/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.04/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_3099,plain,
% 3.04/1.00      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_1558,c_1564]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_3134,plain,
% 3.04/1.00      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_607,c_3099]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_41,negated_conjecture,
% 3.04/1.00      ( r1_tarski(sK3,sK4) ),
% 3.04/1.00      inference(cnf_transformation,[],[f102]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1559,plain,
% 3.04/1.00      ( r1_tarski(sK3,sK4) = iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_23,plain,
% 3.04/1.00      ( v5_relat_1(X0,X1)
% 3.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.04/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1565,plain,
% 3.04/1.00      ( v5_relat_1(X0,X1) = iProver_top
% 3.04/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2697,plain,
% 3.04/1.00      ( v5_relat_1(sK5,sK3) = iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_1558,c_1565]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_17,plain,
% 3.04/1.00      ( ~ v5_relat_1(X0,X1)
% 3.04/1.00      | v5_relat_1(X0,X2)
% 3.04/1.00      | ~ r1_tarski(X1,X2)
% 3.04/1.00      | ~ v1_relat_1(X0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1569,plain,
% 3.04/1.00      ( v5_relat_1(X0,X1) != iProver_top
% 3.04/1.00      | v5_relat_1(X0,X2) = iProver_top
% 3.04/1.00      | r1_tarski(X1,X2) != iProver_top
% 3.04/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_3527,plain,
% 3.04/1.00      ( v5_relat_1(sK5,X0) = iProver_top
% 3.04/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_2697,c_1569]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_47,plain,
% 3.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1900,plain,
% 3.04/1.00      ( v5_relat_1(sK5,sK3)
% 3.04/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1901,plain,
% 3.04/1.00      ( v5_relat_1(sK5,sK3) = iProver_top
% 3.04/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_1900]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1957,plain,
% 3.04/1.00      ( v5_relat_1(sK5,X0)
% 3.04/1.00      | ~ v5_relat_1(sK5,sK3)
% 3.04/1.00      | ~ r1_tarski(sK3,X0)
% 3.04/1.00      | ~ v1_relat_1(sK5) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_17]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1961,plain,
% 3.04/1.00      ( v5_relat_1(sK5,X0) = iProver_top
% 3.04/1.00      | v5_relat_1(sK5,sK3) != iProver_top
% 3.04/1.00      | r1_tarski(sK3,X0) != iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_1957]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.04/1.00      | ~ v1_relat_1(X1)
% 3.04/1.00      | v1_relat_1(X0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1885,plain,
% 3.04/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(X0))
% 3.04/1.00      | ~ v1_relat_1(X0)
% 3.04/1.00      | v1_relat_1(sK5) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_11]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2015,plain,
% 3.04/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.04/1.00      | ~ v1_relat_1(k2_zfmisc_1(sK2,sK3))
% 3.04/1.00      | v1_relat_1(sK5) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_1885]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2016,plain,
% 3.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.04/1.00      | v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 3.04/1.00      | v1_relat_1(sK5) = iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_2015]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_16,plain,
% 3.04/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.04/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2081,plain,
% 3.04/1.00      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_16]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2082,plain,
% 3.04/1.00      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_2081]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_4001,plain,
% 3.04/1.00      ( r1_tarski(sK3,X0) != iProver_top
% 3.04/1.00      | v5_relat_1(sK5,X0) = iProver_top ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_3527,c_47,c_1901,c_1961,c_2016,c_2082]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_4002,plain,
% 3.04/1.00      ( v5_relat_1(sK5,X0) = iProver_top
% 3.04/1.00      | r1_tarski(sK3,X0) != iProver_top ),
% 3.04/1.00      inference(renaming,[status(thm)],[c_4001]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_4010,plain,
% 3.04/1.00      ( v5_relat_1(sK5,sK4) = iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_1559,c_4002]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_15,plain,
% 3.04/1.00      ( ~ v5_relat_1(X0,X1)
% 3.04/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 3.04/1.00      | ~ v1_relat_1(X0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1571,plain,
% 3.04/1.00      ( v5_relat_1(X0,X1) != iProver_top
% 3.04/1.00      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 3.04/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_24,plain,
% 3.04/1.00      ( v4_relat_1(X0,X1)
% 3.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.04/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_13,plain,
% 3.04/1.00      ( ~ v4_relat_1(X0,X1)
% 3.04/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.04/1.00      | ~ v1_relat_1(X0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_457,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.04/1.00      | ~ v1_relat_1(X0) ),
% 3.04/1.00      inference(resolution,[status(thm)],[c_24,c_13]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1556,plain,
% 3.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.04/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.04/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_457]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2252,plain,
% 3.04/1.00      ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_1558,c_1556]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1909,plain,
% 3.04/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.04/1.00      | r1_tarski(k1_relat_1(sK5),sK2)
% 3.04/1.00      | ~ v1_relat_1(sK5) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_457]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1910,plain,
% 3.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.04/1.00      | r1_tarski(k1_relat_1(sK5),sK2) = iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_1909]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2430,plain,
% 3.04/1.00      ( r1_tarski(k1_relat_1(sK5),sK2) = iProver_top ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_2252,c_47,c_1910,c_2016,c_2082]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_26,plain,
% 3.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.04/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.04/1.00      | ~ v1_relat_1(X0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1563,plain,
% 3.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.04/1.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.04/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.04/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_3098,plain,
% 3.04/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.04/1.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.04/1.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.04/1.00      | v1_relat_1(X2) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_1563,c_1564]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11146,plain,
% 3.04/1.00      ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
% 3.04/1.00      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_2430,c_3098]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11306,plain,
% 3.04/1.00      ( r1_tarski(k2_relat_1(sK5),X0) != iProver_top
% 3.04/1.00      | k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5) ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_11146,c_47,c_2016,c_2082]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11307,plain,
% 3.04/1.00      ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
% 3.04/1.00      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.04/1.00      inference(renaming,[status(thm)],[c_11306]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11315,plain,
% 3.04/1.00      ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
% 3.04/1.00      | v5_relat_1(sK5,X0) != iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_1571,c_11307]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11628,plain,
% 3.04/1.00      ( v5_relat_1(sK5,X0) != iProver_top
% 3.04/1.00      | k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5) ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_11315,c_47,c_2016,c_2082]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11629,plain,
% 3.04/1.00      ( k1_relset_1(sK2,X0,sK5) = k1_relat_1(sK5)
% 3.04/1.00      | v5_relat_1(sK5,X0) != iProver_top ),
% 3.04/1.00      inference(renaming,[status(thm)],[c_11628]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11638,plain,
% 3.04/1.00      ( k1_relset_1(sK2,sK4,sK5) = k1_relat_1(sK5) ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_4010,c_11629]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_33,plain,
% 3.04/1.00      ( v1_funct_2(X0,X1,X2)
% 3.04/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.04/1.00      | k1_xboole_0 = X2 ),
% 3.04/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_39,negated_conjecture,
% 3.04/1.00      ( ~ v1_funct_2(sK5,sK2,sK4)
% 3.04/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.04/1.00      | ~ v1_funct_1(sK5) ),
% 3.04/1.00      inference(cnf_transformation,[],[f104]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_44,negated_conjecture,
% 3.04/1.00      ( v1_funct_1(sK5) ),
% 3.04/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_223,plain,
% 3.04/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.04/1.00      | ~ v1_funct_2(sK5,sK2,sK4) ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_39,c_44]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_224,negated_conjecture,
% 3.04/1.00      ( ~ v1_funct_2(sK5,sK2,sK4)
% 3.04/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) ),
% 3.04/1.00      inference(renaming,[status(thm)],[c_223]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_591,plain,
% 3.04/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/1.00      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.04/1.00      | k1_relset_1(X1,X2,X0) != X1
% 3.04/1.00      | sK4 != X2
% 3.04/1.00      | sK2 != X1
% 3.04/1.00      | sK5 != X0
% 3.04/1.00      | k1_xboole_0 = X2 ),
% 3.04/1.00      inference(resolution_lifted,[status(thm)],[c_33,c_224]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_592,plain,
% 3.04/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.04/1.00      | k1_relset_1(sK2,sK4,sK5) != sK2
% 3.04/1.00      | k1_xboole_0 = sK4 ),
% 3.04/1.00      inference(unflattening,[status(thm)],[c_591]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1549,plain,
% 3.04/1.00      ( k1_relset_1(sK2,sK4,sK5) != sK2
% 3.04/1.00      | k1_xboole_0 = sK4
% 3.04/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_592]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11736,plain,
% 3.04/1.00      ( k1_relat_1(sK5) != sK2
% 3.04/1.00      | sK4 = k1_xboole_0
% 3.04/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) != iProver_top ),
% 3.04/1.00      inference(demodulation,[status(thm)],[c_11638,c_1549]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_48,plain,
% 3.04/1.00      ( r1_tarski(sK3,sK4) = iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_632,plain,
% 3.04/1.00      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.04/1.00      | sK3 != sK4
% 3.04/1.00      | sK2 != sK2
% 3.04/1.00      | sK5 != sK5 ),
% 3.04/1.00      inference(resolution_lifted,[status(thm)],[c_224,c_43]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1,plain,
% 3.04/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.04/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1906,plain,
% 3.04/1.00      ( ~ r1_tarski(sK3,sK4) | ~ r1_tarski(sK4,sK3) | sK3 = sK4 ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_1]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_951,plain,( X0 = X0 ),theory(equality) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1993,plain,
% 3.04/1.00      ( sK5 = sK5 ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_951]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2022,plain,
% 3.04/1.00      ( sK2 = sK2 ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_951]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2042,plain,
% 3.04/1.00      ( sK3 = sK3 ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_951]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2098,plain,
% 3.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4)))
% 3.04/1.00      | ~ r1_tarski(k2_relat_1(sK5),sK4)
% 3.04/1.00      | ~ r1_tarski(k1_relat_1(sK5),sK2)
% 3.04/1.00      | ~ v1_relat_1(sK5) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_26]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2099,plain,
% 3.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK4))) = iProver_top
% 3.04/1.00      | r1_tarski(k2_relat_1(sK5),sK4) != iProver_top
% 3.04/1.00      | r1_tarski(k1_relat_1(sK5),sK2) != iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_2098]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2203,plain,
% 3.04/1.00      ( ~ v5_relat_1(sK5,sK4)
% 3.04/1.00      | r1_tarski(k2_relat_1(sK5),sK4)
% 3.04/1.00      | ~ v1_relat_1(sK5) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2204,plain,
% 3.04/1.00      ( v5_relat_1(sK5,sK4) != iProver_top
% 3.04/1.00      | r1_tarski(k2_relat_1(sK5),sK4) = iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_2203]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2213,plain,
% 3.04/1.00      ( ~ v5_relat_1(sK5,sK3)
% 3.04/1.00      | v5_relat_1(sK5,sK4)
% 3.04/1.00      | ~ r1_tarski(sK3,sK4)
% 3.04/1.00      | ~ v1_relat_1(sK5) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_1957]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2214,plain,
% 3.04/1.00      ( v5_relat_1(sK5,sK3) != iProver_top
% 3.04/1.00      | v5_relat_1(sK5,sK4) = iProver_top
% 3.04/1.00      | r1_tarski(sK3,sK4) != iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_2213]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_4,plain,
% 3.04/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 3.04/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2513,plain,
% 3.04/1.00      ( r1_tarski(k1_xboole_0,sK3) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_954,plain,
% 3.04/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.04/1.00      theory(equality) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2031,plain,
% 3.04/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK4,sK3) | sK3 != X1 | sK4 != X0 ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_954]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2537,plain,
% 3.04/1.00      ( ~ r1_tarski(X0,sK3)
% 3.04/1.00      | r1_tarski(sK4,sK3)
% 3.04/1.00      | sK3 != sK3
% 3.04/1.00      | sK4 != X0 ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_2031]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2539,plain,
% 3.04/1.00      ( r1_tarski(sK4,sK3)
% 3.04/1.00      | ~ r1_tarski(k1_xboole_0,sK3)
% 3.04/1.00      | sK3 != sK3
% 3.04/1.00      | sK4 != k1_xboole_0 ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_2537]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11740,plain,
% 3.04/1.00      ( k1_relat_1(sK5) != sK2 ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_11736,c_42,c_47,c_41,c_48,c_754,c_1900,c_1901,c_1906,
% 3.04/1.00                 c_1909,c_1910,c_2015,c_2016,c_2042,c_2081,c_2082,c_2098,
% 3.04/1.00                 c_2099,c_2203,c_2204,c_2213,c_2214,c_2513,c_2539]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11743,plain,
% 3.04/1.00      ( sK3 = k1_xboole_0 ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_3134,c_11740]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_40,negated_conjecture,
% 3.04/1.00      ( k1_xboole_0 != sK3 | k1_xboole_0 = sK2 ),
% 3.04/1.00      inference(cnf_transformation,[],[f103]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11946,plain,
% 3.04/1.00      ( sK2 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 3.04/1.00      inference(demodulation,[status(thm)],[c_11743,c_40]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_11947,plain,
% 3.04/1.00      ( sK2 = k1_xboole_0 ),
% 3.04/1.00      inference(equality_resolution_simp,[status(thm)],[c_11946]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_12371,plain,
% 3.04/1.00      ( k1_relat_1(sK5) != k1_xboole_0 ),
% 3.04/1.00      inference(demodulation,[status(thm)],[c_11947,c_11740]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_6,plain,
% 3.04/1.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.04/1.00      inference(cnf_transformation,[],[f107]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2869,plain,
% 3.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.04/1.00      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.04/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.04/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_6,c_1563]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_4878,plain,
% 3.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.04/1.00      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_2430,c_2869]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_5273,plain,
% 3.04/1.00      ( r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top
% 3.04/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_4878,c_47,c_2016,c_2082]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_5274,plain,
% 3.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.04/1.00      | r1_tarski(k2_relat_1(sK5),k1_xboole_0) != iProver_top ),
% 3.04/1.00      inference(renaming,[status(thm)],[c_5273]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_5279,plain,
% 3.04/1.00      ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
% 3.04/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_1571,c_5274]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_5437,plain,
% 3.04/1.00      ( m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.04/1.00      | v5_relat_1(sK5,k1_xboole_0) != iProver_top ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_5279,c_47,c_2016,c_2082]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_5438,plain,
% 3.04/1.00      ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
% 3.04/1.00      | m1_subset_1(sK5,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.04/1.00      inference(renaming,[status(thm)],[c_5437]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2254,plain,
% 3.04/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.04/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top
% 3.04/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_6,c_1556]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_5445,plain,
% 3.04/1.00      ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
% 3.04/1.00      | r1_tarski(k1_relat_1(sK5),X0) = iProver_top
% 3.04/1.00      | v1_relat_1(sK5) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_5438,c_2254]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_8089,plain,
% 3.04/1.00      ( r1_tarski(k1_relat_1(sK5),X0) = iProver_top
% 3.04/1.00      | v5_relat_1(sK5,k1_xboole_0) != iProver_top ),
% 3.04/1.00      inference(global_propositional_subsumption,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_5445,c_47,c_2016,c_2082]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_8090,plain,
% 3.04/1.00      ( v5_relat_1(sK5,k1_xboole_0) != iProver_top
% 3.04/1.00      | r1_tarski(k1_relat_1(sK5),X0) = iProver_top ),
% 3.04/1.00      inference(renaming,[status(thm)],[c_8089]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1577,plain,
% 3.04/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_1579,plain,
% 3.04/1.00      ( X0 = X1
% 3.04/1.00      | r1_tarski(X1,X0) != iProver_top
% 3.04/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.04/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_3656,plain,
% 3.04/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_1577,c_1579]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_8099,plain,
% 3.04/1.00      ( k1_relat_1(sK5) = k1_xboole_0
% 3.04/1.00      | v5_relat_1(sK5,k1_xboole_0) != iProver_top ),
% 3.04/1.00      inference(superposition,[status(thm)],[c_8090,c_3656]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_8131,plain,
% 3.04/1.00      ( ~ v5_relat_1(sK5,k1_xboole_0) | k1_relat_1(sK5) = k1_xboole_0 ),
% 3.04/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_8099]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_4003,plain,
% 3.04/1.00      ( v5_relat_1(sK5,X0) | ~ r1_tarski(sK3,X0) ),
% 3.04/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4002]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_4005,plain,
% 3.04/1.00      ( v5_relat_1(sK5,k1_xboole_0) | ~ r1_tarski(sK3,k1_xboole_0) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_4003]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2216,plain,
% 3.04/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK3,X2) | X2 != X1 | sK3 != X0 ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_954]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_2218,plain,
% 3.04/1.00      ( r1_tarski(sK3,k1_xboole_0)
% 3.04/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 3.04/1.00      | sK3 != k1_xboole_0
% 3.04/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_2216]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_132,plain,
% 3.04/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_4]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_7,plain,
% 3.04/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.04/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_127,plain,
% 3.04/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_8,plain,
% 3.04/1.00      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.04/1.00      | k1_xboole_0 = X0
% 3.04/1.00      | k1_xboole_0 = X1 ),
% 3.04/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(c_126,plain,
% 3.04/1.00      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.04/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 3.04/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.04/1.00  
% 3.04/1.00  cnf(contradiction,plain,
% 3.04/1.00      ( $false ),
% 3.04/1.00      inference(minisat,
% 3.04/1.00                [status(thm)],
% 3.04/1.00                [c_12371,c_11736,c_8131,c_4005,c_3134,c_2539,c_2513,
% 3.04/1.00                 c_2218,c_2214,c_2213,c_2204,c_2203,c_2099,c_2098,c_2082,
% 3.04/1.00                 c_2081,c_2042,c_2022,c_2016,c_2015,c_1993,c_1910,c_1909,
% 3.04/1.00                 c_1906,c_1901,c_1900,c_632,c_132,c_127,c_126,c_48,c_41,
% 3.04/1.00                 c_47,c_42]) ).
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/1.00  
% 3.04/1.00  ------                               Statistics
% 3.04/1.00  
% 3.04/1.00  ------ General
% 3.04/1.00  
% 3.04/1.00  abstr_ref_over_cycles:                  0
% 3.04/1.00  abstr_ref_under_cycles:                 0
% 3.04/1.00  gc_basic_clause_elim:                   0
% 3.04/1.00  forced_gc_time:                         0
% 3.04/1.00  parsing_time:                           0.014
% 3.04/1.00  unif_index_cands_time:                  0.
% 3.04/1.00  unif_index_add_time:                    0.
% 3.04/1.00  orderings_time:                         0.
% 3.04/1.00  out_proof_time:                         0.012
% 3.04/1.00  total_time:                             0.326
% 3.04/1.00  num_of_symbols:                         53
% 3.04/1.00  num_of_terms:                           9797
% 3.04/1.00  
% 3.04/1.00  ------ Preprocessing
% 3.04/1.00  
% 3.04/1.00  num_of_splits:                          0
% 3.04/1.00  num_of_split_atoms:                     0
% 3.04/1.00  num_of_reused_defs:                     0
% 3.04/1.00  num_eq_ax_congr_red:                    25
% 3.04/1.00  num_of_sem_filtered_clauses:            1
% 3.04/1.00  num_of_subtypes:                        0
% 3.04/1.00  monotx_restored_types:                  0
% 3.04/1.00  sat_num_of_epr_types:                   0
% 3.04/1.00  sat_num_of_non_cyclic_types:            0
% 3.04/1.00  sat_guarded_non_collapsed_types:        0
% 3.04/1.00  num_pure_diseq_elim:                    0
% 3.04/1.00  simp_replaced_by:                       0
% 3.04/1.00  res_preprocessed:                       196
% 3.04/1.00  prep_upred:                             0
% 3.04/1.00  prep_unflattend:                        42
% 3.04/1.00  smt_new_axioms:                         0
% 3.04/1.00  pred_elim_cands:                        6
% 3.04/1.00  pred_elim:                              3
% 3.04/1.00  pred_elim_cl:                           1
% 3.04/1.00  pred_elim_cycles:                       5
% 3.04/1.00  merged_defs:                            0
% 3.04/1.00  merged_defs_ncl:                        0
% 3.04/1.00  bin_hyper_res:                          0
% 3.04/1.00  prep_cycles:                            4
% 3.04/1.00  pred_elim_time:                         0.008
% 3.04/1.00  splitting_time:                         0.
% 3.04/1.00  sem_filter_time:                        0.
% 3.04/1.00  monotx_time:                            0.001
% 3.04/1.00  subtype_inf_time:                       0.
% 3.04/1.00  
% 3.04/1.00  ------ Problem properties
% 3.04/1.00  
% 3.04/1.00  clauses:                                42
% 3.04/1.00  conjectures:                            3
% 3.04/1.00  epr:                                    10
% 3.04/1.00  horn:                                   36
% 3.04/1.00  ground:                                 18
% 3.04/1.00  unary:                                  10
% 3.04/1.00  binary:                                 9
% 3.04/1.00  lits:                                   108
% 3.04/1.00  lits_eq:                                43
% 3.04/1.00  fd_pure:                                0
% 3.04/1.00  fd_pseudo:                              0
% 3.04/1.00  fd_cond:                                2
% 3.04/1.00  fd_pseudo_cond:                         1
% 3.04/1.00  ac_symbols:                             0
% 3.04/1.00  
% 3.04/1.00  ------ Propositional Solver
% 3.04/1.00  
% 3.04/1.00  prop_solver_calls:                      30
% 3.04/1.00  prop_fast_solver_calls:                 1623
% 3.04/1.00  smt_solver_calls:                       0
% 3.04/1.00  smt_fast_solver_calls:                  0
% 3.04/1.00  prop_num_of_clauses:                    4451
% 3.04/1.00  prop_preprocess_simplified:             11139
% 3.04/1.00  prop_fo_subsumed:                       57
% 3.04/1.00  prop_solver_time:                       0.
% 3.04/1.00  smt_solver_time:                        0.
% 3.04/1.00  smt_fast_solver_time:                   0.
% 3.04/1.00  prop_fast_solver_time:                  0.
% 3.04/1.00  prop_unsat_core_time:                   0.
% 3.04/1.00  
% 3.04/1.00  ------ QBF
% 3.04/1.00  
% 3.04/1.00  qbf_q_res:                              0
% 3.04/1.00  qbf_num_tautologies:                    0
% 3.04/1.00  qbf_prep_cycles:                        0
% 3.04/1.00  
% 3.04/1.00  ------ BMC1
% 3.04/1.00  
% 3.04/1.00  bmc1_current_bound:                     -1
% 3.04/1.00  bmc1_last_solved_bound:                 -1
% 3.04/1.00  bmc1_unsat_core_size:                   -1
% 3.04/1.00  bmc1_unsat_core_parents_size:           -1
% 3.04/1.00  bmc1_merge_next_fun:                    0
% 3.04/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.04/1.00  
% 3.04/1.00  ------ Instantiation
% 3.04/1.00  
% 3.04/1.00  inst_num_of_clauses:                    1500
% 3.04/1.00  inst_num_in_passive:                    254
% 3.04/1.00  inst_num_in_active:                     710
% 3.04/1.00  inst_num_in_unprocessed:                536
% 3.04/1.00  inst_num_of_loops:                      800
% 3.04/1.00  inst_num_of_learning_restarts:          0
% 3.04/1.00  inst_num_moves_active_passive:          86
% 3.04/1.00  inst_lit_activity:                      0
% 3.04/1.00  inst_lit_activity_moves:                0
% 3.04/1.00  inst_num_tautologies:                   0
% 3.04/1.00  inst_num_prop_implied:                  0
% 3.04/1.00  inst_num_existing_simplified:           0
% 3.04/1.00  inst_num_eq_res_simplified:             0
% 3.04/1.00  inst_num_child_elim:                    0
% 3.04/1.00  inst_num_of_dismatching_blockings:      394
% 3.04/1.00  inst_num_of_non_proper_insts:           1696
% 3.04/1.00  inst_num_of_duplicates:                 0
% 3.04/1.00  inst_inst_num_from_inst_to_res:         0
% 3.04/1.00  inst_dismatching_checking_time:         0.
% 3.04/1.00  
% 3.04/1.00  ------ Resolution
% 3.04/1.00  
% 3.04/1.00  res_num_of_clauses:                     0
% 3.04/1.00  res_num_in_passive:                     0
% 3.04/1.00  res_num_in_active:                      0
% 3.04/1.00  res_num_of_loops:                       200
% 3.04/1.00  res_forward_subset_subsumed:            117
% 3.04/1.00  res_backward_subset_subsumed:           4
% 3.04/1.00  res_forward_subsumed:                   0
% 3.04/1.00  res_backward_subsumed:                  0
% 3.04/1.00  res_forward_subsumption_resolution:     0
% 3.04/1.00  res_backward_subsumption_resolution:    0
% 3.04/1.00  res_clause_to_clause_subsumption:       677
% 3.04/1.00  res_orphan_elimination:                 0
% 3.04/1.00  res_tautology_del:                      135
% 3.04/1.00  res_num_eq_res_simplified:              2
% 3.04/1.00  res_num_sel_changes:                    0
% 3.04/1.00  res_moves_from_active_to_pass:          0
% 3.04/1.00  
% 3.04/1.00  ------ Superposition
% 3.04/1.00  
% 3.04/1.00  sup_time_total:                         0.
% 3.04/1.00  sup_time_generating:                    0.
% 3.04/1.00  sup_time_sim_full:                      0.
% 3.04/1.00  sup_time_sim_immed:                     0.
% 3.04/1.00  
% 3.04/1.00  sup_num_of_clauses:                     115
% 3.04/1.00  sup_num_in_active:                      83
% 3.04/1.00  sup_num_in_passive:                     32
% 3.04/1.00  sup_num_of_loops:                       159
% 3.04/1.00  sup_fw_superposition:                   192
% 3.04/1.00  sup_bw_superposition:                   85
% 3.04/1.00  sup_immediate_simplified:               89
% 3.04/1.00  sup_given_eliminated:                   3
% 3.04/1.00  comparisons_done:                       0
% 3.04/1.00  comparisons_avoided:                    39
% 3.04/1.00  
% 3.04/1.00  ------ Simplifications
% 3.04/1.00  
% 3.04/1.00  
% 3.04/1.00  sim_fw_subset_subsumed:                 47
% 3.04/1.00  sim_bw_subset_subsumed:                 27
% 3.04/1.00  sim_fw_subsumed:                        27
% 3.04/1.00  sim_bw_subsumed:                        9
% 3.04/1.00  sim_fw_subsumption_res:                 3
% 3.04/1.00  sim_bw_subsumption_res:                 0
% 3.04/1.00  sim_tautology_del:                      8
% 3.04/1.00  sim_eq_tautology_del:                   27
% 3.04/1.00  sim_eq_res_simp:                        4
% 3.04/1.00  sim_fw_demodulated:                     20
% 3.04/1.00  sim_bw_demodulated:                     53
% 3.04/1.00  sim_light_normalised:                   18
% 3.04/1.00  sim_joinable_taut:                      0
% 3.04/1.00  sim_joinable_simp:                      0
% 3.04/1.00  sim_ac_normalised:                      0
% 3.04/1.00  sim_smt_subsumption:                    0
% 3.04/1.00  
%------------------------------------------------------------------------------
