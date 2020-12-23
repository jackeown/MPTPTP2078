%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:31 EST 2020

% Result     : Theorem 3.50s
% Output     : CNFRefutation 3.50s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_546)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
       => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
            & v1_funct_2(X3,X0,X2)
            & v1_funct_1(X3) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( r1_tarski(k2_relset_1(X0,X1,X3),X2)
         => ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
              & v1_funct_2(X3,X0,X2)
              & v1_funct_1(X3) )
            | ( k1_xboole_0 != X0
              & k1_xboole_0 = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
        | ~ v1_funct_2(X3,X0,X2)
        | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & r1_tarski(k2_relset_1(X0,X1,X3),X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f37,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2)))
          | ~ v1_funct_2(X3,X0,X2)
          | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_tarski(k2_relset_1(X0,X1,X3),X2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f37])).

fof(f64,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f38])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f65,plain,(
    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f13,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f67,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f62,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f32])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X1
      | k1_xboole_0 = X0
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f74,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f63,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f70,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f45])).

fof(f66,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f30])).

fof(f41,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f72])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X2,X1] :
      ( v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f59])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1188,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_11,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_338,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_13,c_11])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_342,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_338,c_12])).

cnf(c_343,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_342])).

cnf(c_1187,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_343])).

cnf(c_1535,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1187])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1191,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2748,plain,
    ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1188,c_1191])).

cnf(c_25,negated_conjecture,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1189,plain,
    ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2853,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2748,c_1189])).

cnf(c_16,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1190,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1192,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3231,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1190,c_1192])).

cnf(c_9230,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2853,c_3231])).

cnf(c_31,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1369,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1370,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1369])).

cnf(c_9892,plain,
    ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9230,c_31,c_1370])).

cnf(c_9893,plain,
    ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_9892])).

cnf(c_9903,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1535,c_9893])).

cnf(c_20,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_23,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_147,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_28])).

cnf(c_148,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_147])).

cnf(c_458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_148])).

cnf(c_459,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_1182,plain,
    ( k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_459])).

cnf(c_9945,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9903,c_1182])).

cnf(c_6,plain,
    ( k2_zfmisc_1(X0,X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_82,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_83,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1379,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(instantiation,[status(thm)],[c_343])).

cnf(c_1380,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1379])).

cnf(c_729,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1552,plain,
    ( sK0 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK0 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_1553,plain,
    ( sK0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1552])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_409,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_410,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_1185,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_410])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1277,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0
    | sK3 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1185,c_4])).

cnf(c_24,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1388,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_1443,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1388])).

cnf(c_728,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1444,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_728])).

cnf(c_1561,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_1562,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1561])).

cnf(c_1771,plain,
    ( sK1 != k1_xboole_0
    | sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1277,c_24,c_82,c_83,c_1443,c_1444,c_1562])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_2355,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK3))
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | k1_relat_1(sK3) = X0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2357,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
    | k1_relat_1(sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2355])).

cnf(c_2361,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_728])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_471,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_472,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_474,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_472,c_26])).

cnf(c_3232,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1188,c_1192])).

cnf(c_3402,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_474,c_3232])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_3915,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(sK3)))
    | r1_tarski(X0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3917,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK3)))
    | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_3915])).

cnf(c_730,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1870,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(sK3),X2)
    | X2 != X1
    | k1_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_2360,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),X0)
    | r1_tarski(k1_relat_1(sK3),X1)
    | X1 != X0
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1870])).

cnf(c_4182,plain,
    ( r1_tarski(k1_relat_1(sK3),X0)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | X0 != sK0
    | k1_relat_1(sK3) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2360])).

cnf(c_4184,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_4182])).

cnf(c_2129,plain,
    ( X0 != X1
    | X0 = sK0
    | sK0 != X1 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_4203,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = sK0
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_2129])).

cnf(c_4206,plain,
    ( k1_relat_1(sK3) = sK0
    | k1_relat_1(sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4203])).

cnf(c_2225,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ r1_tarski(k1_relat_1(X0),sK0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_4450,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2225])).

cnf(c_4451,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4450])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_9872,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK3))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_10095,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9945,c_26,c_31,c_82,c_83,c_1370,c_1379,c_1380,c_1553,c_1771,c_2357,c_2361,c_2853,c_3402,c_3917,c_4184,c_4206,c_4451,c_9872])).

cnf(c_17,plain,
    ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_386,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK0 != X0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_148])).

cnf(c_387,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_399,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_387,c_7])).

cnf(c_1186,plain,
    ( sK2 != k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 = sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_10115,plain,
    ( sK0 = k1_xboole_0
    | sK3 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10095,c_1186])).

cnf(c_10122,plain,
    ( sK0 = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10115])).

cnf(c_10126,plain,
    ( sK0 = k1_xboole_0
    | sK3 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10122,c_4])).

cnf(c_482,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_148,c_27])).

cnf(c_1382,plain,
    ( ~ r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,sK0)
    | sK0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1389,plain,
    ( sK1 != X0
    | sK1 = sK2
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_1390,plain,
    ( sK1 = sK2
    | sK1 != k1_xboole_0
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1389])).

cnf(c_1570,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
    | r1_tarski(X0,sK0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1572,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
    | r1_tarski(k1_xboole_0,sK0) ),
    inference(instantiation,[status(thm)],[c_1570])).

cnf(c_1606,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_728])).

cnf(c_1977,plain,
    ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_728])).

cnf(c_2078,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2095,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
    | r1_tarski(sK3,X0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2097,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(sK3,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2095])).

cnf(c_2854,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2853])).

cnf(c_2894,plain,
    ( sK2 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK2 ),
    inference(instantiation,[status(thm)],[c_729])).

cnf(c_2895,plain,
    ( sK2 != k1_xboole_0
    | k1_xboole_0 = sK2
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2894])).

cnf(c_2042,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1190])).

cnf(c_3104,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1535,c_2042])).

cnf(c_3494,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3104,c_31,c_1370])).

cnf(c_3495,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3494])).

cnf(c_3496,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3495])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1195,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1538,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1187])).

cnf(c_2669,plain,
    ( r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_1538])).

cnf(c_3544,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(sK0,X0) = iProver_top
    | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3402,c_2669])).

cnf(c_3569,plain,
    ( r1_tarski(sK0,X0)
    | ~ r1_tarski(sK3,k1_xboole_0)
    | sK1 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3544])).

cnf(c_3571,plain,
    ( r1_tarski(sK0,k1_xboole_0)
    | ~ r1_tarski(sK3,k1_xboole_0)
    | sK1 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3569])).

cnf(c_1525,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK3),X2)
    | X2 != X1
    | k2_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_730])).

cnf(c_1976,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),X0)
    | r1_tarski(k2_relat_1(sK3),X1)
    | X1 != X0
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1525])).

cnf(c_7456,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | X0 != sK2
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1976])).

cnf(c_7463,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK2)
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_xboole_0 != sK2 ),
    inference(instantiation,[status(thm)],[c_7456])).

cnf(c_11136,plain,
    ( sK0 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10126,c_26,c_31,c_82,c_83,c_546,c_1369,c_1370,c_1379,c_1380,c_1382,c_1390,c_1553,c_1572,c_1771,c_1977,c_2078,c_2097,c_2357,c_2361,c_2853,c_2854,c_2895,c_3402,c_3496,c_3571,c_3917,c_4184,c_4206,c_4450,c_4451,c_7463,c_9872,c_9945])).

cnf(c_1194,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2145,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1194])).

cnf(c_11175,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11136,c_2145])).

cnf(c_11195,plain,
    ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11175,c_5])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1197,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3547,plain,
    ( k1_relat_1(X0) = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2669,c_1197])).

cnf(c_11426,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_11195,c_3547])).

cnf(c_3234,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5,c_1192])).

cnf(c_3392,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
    | r1_tarski(X1,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1195,c_3234])).

cnf(c_11430,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_11195,c_3392])).

cnf(c_11464,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_11426,c_11430])).

cnf(c_11470,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_11464])).

cnf(c_19,plain,
    ( v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_429,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
    | sK2 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_148])).

cnf(c_430,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_1184,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_430])).

cnf(c_1302,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1184,c_5])).

cnf(c_10114,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10095,c_1302])).

cnf(c_10134,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10114,c_4])).

cnf(c_7462,plain,
    ( X0 != sK2
    | k2_relat_1(sK3) != k2_relat_1(sK3)
    | r1_tarski(k2_relat_1(sK3),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7456])).

cnf(c_7464,plain,
    ( k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_xboole_0 != sK2
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7462])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11470,c_10134,c_10095,c_7464,c_7463,c_4450,c_3571,c_3496,c_3495,c_2895,c_2854,c_2853,c_2097,c_2078,c_1977,c_1606,c_1572,c_1444,c_1390,c_1382,c_1379,c_1369,c_482,c_83,c_82,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.50/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.50/0.99  
% 3.50/0.99  ------  iProver source info
% 3.50/0.99  
% 3.50/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.50/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.50/0.99  git: non_committed_changes: false
% 3.50/0.99  git: last_make_outside_of_git: false
% 3.50/0.99  
% 3.50/0.99  ------ 
% 3.50/0.99  
% 3.50/0.99  ------ Input Options
% 3.50/0.99  
% 3.50/0.99  --out_options                           all
% 3.50/0.99  --tptp_safe_out                         true
% 3.50/0.99  --problem_path                          ""
% 3.50/0.99  --include_path                          ""
% 3.50/0.99  --clausifier                            res/vclausify_rel
% 3.50/0.99  --clausifier_options                    --mode clausify
% 3.50/0.99  --stdin                                 false
% 3.50/0.99  --stats_out                             all
% 3.50/0.99  
% 3.50/0.99  ------ General Options
% 3.50/0.99  
% 3.50/0.99  --fof                                   false
% 3.50/0.99  --time_out_real                         305.
% 3.50/0.99  --time_out_virtual                      -1.
% 3.50/0.99  --symbol_type_check                     false
% 3.50/0.99  --clausify_out                          false
% 3.50/0.99  --sig_cnt_out                           false
% 3.50/0.99  --trig_cnt_out                          false
% 3.50/0.99  --trig_cnt_out_tolerance                1.
% 3.50/0.99  --trig_cnt_out_sk_spl                   false
% 3.50/0.99  --abstr_cl_out                          false
% 3.50/0.99  
% 3.50/0.99  ------ Global Options
% 3.50/0.99  
% 3.50/0.99  --schedule                              default
% 3.50/0.99  --add_important_lit                     false
% 3.50/0.99  --prop_solver_per_cl                    1000
% 3.50/0.99  --min_unsat_core                        false
% 3.50/0.99  --soft_assumptions                      false
% 3.50/0.99  --soft_lemma_size                       3
% 3.50/0.99  --prop_impl_unit_size                   0
% 3.50/0.99  --prop_impl_unit                        []
% 3.50/0.99  --share_sel_clauses                     true
% 3.50/0.99  --reset_solvers                         false
% 3.50/0.99  --bc_imp_inh                            [conj_cone]
% 3.50/0.99  --conj_cone_tolerance                   3.
% 3.50/0.99  --extra_neg_conj                        none
% 3.50/0.99  --large_theory_mode                     true
% 3.50/0.99  --prolific_symb_bound                   200
% 3.50/0.99  --lt_threshold                          2000
% 3.50/0.99  --clause_weak_htbl                      true
% 3.50/0.99  --gc_record_bc_elim                     false
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing Options
% 3.50/0.99  
% 3.50/0.99  --preprocessing_flag                    true
% 3.50/0.99  --time_out_prep_mult                    0.1
% 3.50/0.99  --splitting_mode                        input
% 3.50/0.99  --splitting_grd                         true
% 3.50/0.99  --splitting_cvd                         false
% 3.50/0.99  --splitting_cvd_svl                     false
% 3.50/0.99  --splitting_nvd                         32
% 3.50/0.99  --sub_typing                            true
% 3.50/0.99  --prep_gs_sim                           true
% 3.50/0.99  --prep_unflatten                        true
% 3.50/0.99  --prep_res_sim                          true
% 3.50/0.99  --prep_upred                            true
% 3.50/0.99  --prep_sem_filter                       exhaustive
% 3.50/0.99  --prep_sem_filter_out                   false
% 3.50/0.99  --pred_elim                             true
% 3.50/0.99  --res_sim_input                         true
% 3.50/0.99  --eq_ax_congr_red                       true
% 3.50/0.99  --pure_diseq_elim                       true
% 3.50/0.99  --brand_transform                       false
% 3.50/0.99  --non_eq_to_eq                          false
% 3.50/0.99  --prep_def_merge                        true
% 3.50/0.99  --prep_def_merge_prop_impl              false
% 3.50/0.99  --prep_def_merge_mbd                    true
% 3.50/0.99  --prep_def_merge_tr_red                 false
% 3.50/0.99  --prep_def_merge_tr_cl                  false
% 3.50/0.99  --smt_preprocessing                     true
% 3.50/0.99  --smt_ac_axioms                         fast
% 3.50/0.99  --preprocessed_out                      false
% 3.50/0.99  --preprocessed_stats                    false
% 3.50/0.99  
% 3.50/0.99  ------ Abstraction refinement Options
% 3.50/0.99  
% 3.50/0.99  --abstr_ref                             []
% 3.50/0.99  --abstr_ref_prep                        false
% 3.50/0.99  --abstr_ref_until_sat                   false
% 3.50/0.99  --abstr_ref_sig_restrict                funpre
% 3.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.99  --abstr_ref_under                       []
% 3.50/0.99  
% 3.50/0.99  ------ SAT Options
% 3.50/0.99  
% 3.50/0.99  --sat_mode                              false
% 3.50/0.99  --sat_fm_restart_options                ""
% 3.50/0.99  --sat_gr_def                            false
% 3.50/0.99  --sat_epr_types                         true
% 3.50/0.99  --sat_non_cyclic_types                  false
% 3.50/0.99  --sat_finite_models                     false
% 3.50/0.99  --sat_fm_lemmas                         false
% 3.50/0.99  --sat_fm_prep                           false
% 3.50/0.99  --sat_fm_uc_incr                        true
% 3.50/0.99  --sat_out_model                         small
% 3.50/0.99  --sat_out_clauses                       false
% 3.50/0.99  
% 3.50/0.99  ------ QBF Options
% 3.50/0.99  
% 3.50/0.99  --qbf_mode                              false
% 3.50/0.99  --qbf_elim_univ                         false
% 3.50/0.99  --qbf_dom_inst                          none
% 3.50/0.99  --qbf_dom_pre_inst                      false
% 3.50/0.99  --qbf_sk_in                             false
% 3.50/0.99  --qbf_pred_elim                         true
% 3.50/0.99  --qbf_split                             512
% 3.50/0.99  
% 3.50/0.99  ------ BMC1 Options
% 3.50/0.99  
% 3.50/0.99  --bmc1_incremental                      false
% 3.50/0.99  --bmc1_axioms                           reachable_all
% 3.50/0.99  --bmc1_min_bound                        0
% 3.50/0.99  --bmc1_max_bound                        -1
% 3.50/0.99  --bmc1_max_bound_default                -1
% 3.50/0.99  --bmc1_symbol_reachability              true
% 3.50/0.99  --bmc1_property_lemmas                  false
% 3.50/0.99  --bmc1_k_induction                      false
% 3.50/0.99  --bmc1_non_equiv_states                 false
% 3.50/0.99  --bmc1_deadlock                         false
% 3.50/0.99  --bmc1_ucm                              false
% 3.50/0.99  --bmc1_add_unsat_core                   none
% 3.50/0.99  --bmc1_unsat_core_children              false
% 3.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.99  --bmc1_out_stat                         full
% 3.50/0.99  --bmc1_ground_init                      false
% 3.50/0.99  --bmc1_pre_inst_next_state              false
% 3.50/0.99  --bmc1_pre_inst_state                   false
% 3.50/0.99  --bmc1_pre_inst_reach_state             false
% 3.50/0.99  --bmc1_out_unsat_core                   false
% 3.50/0.99  --bmc1_aig_witness_out                  false
% 3.50/0.99  --bmc1_verbose                          false
% 3.50/0.99  --bmc1_dump_clauses_tptp                false
% 3.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.99  --bmc1_dump_file                        -
% 3.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.99  --bmc1_ucm_extend_mode                  1
% 3.50/0.99  --bmc1_ucm_init_mode                    2
% 3.50/0.99  --bmc1_ucm_cone_mode                    none
% 3.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.99  --bmc1_ucm_relax_model                  4
% 3.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.99  --bmc1_ucm_layered_model                none
% 3.50/0.99  --bmc1_ucm_max_lemma_size               10
% 3.50/0.99  
% 3.50/0.99  ------ AIG Options
% 3.50/0.99  
% 3.50/0.99  --aig_mode                              false
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation Options
% 3.50/0.99  
% 3.50/0.99  --instantiation_flag                    true
% 3.50/0.99  --inst_sos_flag                         false
% 3.50/0.99  --inst_sos_phase                        true
% 3.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel_side                     num_symb
% 3.50/0.99  --inst_solver_per_active                1400
% 3.50/0.99  --inst_solver_calls_frac                1.
% 3.50/0.99  --inst_passive_queue_type               priority_queues
% 3.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.99  --inst_passive_queues_freq              [25;2]
% 3.50/0.99  --inst_dismatching                      true
% 3.50/0.99  --inst_eager_unprocessed_to_passive     true
% 3.50/0.99  --inst_prop_sim_given                   true
% 3.50/0.99  --inst_prop_sim_new                     false
% 3.50/0.99  --inst_subs_new                         false
% 3.50/0.99  --inst_eq_res_simp                      false
% 3.50/0.99  --inst_subs_given                       false
% 3.50/0.99  --inst_orphan_elimination               true
% 3.50/0.99  --inst_learning_loop_flag               true
% 3.50/0.99  --inst_learning_start                   3000
% 3.50/0.99  --inst_learning_factor                  2
% 3.50/0.99  --inst_start_prop_sim_after_learn       3
% 3.50/0.99  --inst_sel_renew                        solver
% 3.50/0.99  --inst_lit_activity_flag                true
% 3.50/0.99  --inst_restr_to_given                   false
% 3.50/0.99  --inst_activity_threshold               500
% 3.50/0.99  --inst_out_proof                        true
% 3.50/0.99  
% 3.50/0.99  ------ Resolution Options
% 3.50/0.99  
% 3.50/0.99  --resolution_flag                       true
% 3.50/0.99  --res_lit_sel                           adaptive
% 3.50/0.99  --res_lit_sel_side                      none
% 3.50/0.99  --res_ordering                          kbo
% 3.50/0.99  --res_to_prop_solver                    active
% 3.50/0.99  --res_prop_simpl_new                    false
% 3.50/0.99  --res_prop_simpl_given                  true
% 3.50/0.99  --res_passive_queue_type                priority_queues
% 3.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.99  --res_passive_queues_freq               [15;5]
% 3.50/0.99  --res_forward_subs                      full
% 3.50/0.99  --res_backward_subs                     full
% 3.50/0.99  --res_forward_subs_resolution           true
% 3.50/0.99  --res_backward_subs_resolution          true
% 3.50/0.99  --res_orphan_elimination                true
% 3.50/0.99  --res_time_limit                        2.
% 3.50/0.99  --res_out_proof                         true
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Options
% 3.50/0.99  
% 3.50/0.99  --superposition_flag                    true
% 3.50/0.99  --sup_passive_queue_type                priority_queues
% 3.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.99  --demod_completeness_check              fast
% 3.50/0.99  --demod_use_ground                      true
% 3.50/0.99  --sup_to_prop_solver                    passive
% 3.50/0.99  --sup_prop_simpl_new                    true
% 3.50/0.99  --sup_prop_simpl_given                  true
% 3.50/0.99  --sup_fun_splitting                     false
% 3.50/0.99  --sup_smt_interval                      50000
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Simplification Setup
% 3.50/0.99  
% 3.50/0.99  --sup_indices_passive                   []
% 3.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_full_bw                           [BwDemod]
% 3.50/0.99  --sup_immed_triv                        [TrivRules]
% 3.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_immed_bw_main                     []
% 3.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  
% 3.50/0.99  ------ Combination Options
% 3.50/0.99  
% 3.50/0.99  --comb_res_mult                         3
% 3.50/0.99  --comb_sup_mult                         2
% 3.50/0.99  --comb_inst_mult                        10
% 3.50/0.99  
% 3.50/0.99  ------ Debug Options
% 3.50/0.99  
% 3.50/0.99  --dbg_backtrace                         false
% 3.50/0.99  --dbg_dump_prop_clauses                 false
% 3.50/0.99  --dbg_dump_prop_clauses_file            -
% 3.50/0.99  --dbg_out_stat                          false
% 3.50/0.99  ------ Parsing...
% 3.50/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.50/0.99  ------ Proving...
% 3.50/0.99  ------ Problem Properties 
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  clauses                                 24
% 3.50/0.99  conjectures                             3
% 3.50/0.99  EPR                                     4
% 3.50/0.99  Horn                                    21
% 3.50/0.99  unary                                   6
% 3.50/0.99  binary                                  10
% 3.50/0.99  lits                                    54
% 3.50/0.99  lits eq                                 26
% 3.50/0.99  fd_pure                                 0
% 3.50/0.99  fd_pseudo                               0
% 3.50/0.99  fd_cond                                 2
% 3.50/0.99  fd_pseudo_cond                          1
% 3.50/0.99  AC symbols                              0
% 3.50/0.99  
% 3.50/0.99  ------ Schedule dynamic 5 is on 
% 3.50/0.99  
% 3.50/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ 
% 3.50/0.99  Current options:
% 3.50/0.99  ------ 
% 3.50/0.99  
% 3.50/0.99  ------ Input Options
% 3.50/0.99  
% 3.50/0.99  --out_options                           all
% 3.50/0.99  --tptp_safe_out                         true
% 3.50/0.99  --problem_path                          ""
% 3.50/0.99  --include_path                          ""
% 3.50/0.99  --clausifier                            res/vclausify_rel
% 3.50/0.99  --clausifier_options                    --mode clausify
% 3.50/0.99  --stdin                                 false
% 3.50/0.99  --stats_out                             all
% 3.50/0.99  
% 3.50/0.99  ------ General Options
% 3.50/0.99  
% 3.50/0.99  --fof                                   false
% 3.50/0.99  --time_out_real                         305.
% 3.50/0.99  --time_out_virtual                      -1.
% 3.50/0.99  --symbol_type_check                     false
% 3.50/0.99  --clausify_out                          false
% 3.50/0.99  --sig_cnt_out                           false
% 3.50/0.99  --trig_cnt_out                          false
% 3.50/0.99  --trig_cnt_out_tolerance                1.
% 3.50/0.99  --trig_cnt_out_sk_spl                   false
% 3.50/0.99  --abstr_cl_out                          false
% 3.50/0.99  
% 3.50/0.99  ------ Global Options
% 3.50/0.99  
% 3.50/0.99  --schedule                              default
% 3.50/0.99  --add_important_lit                     false
% 3.50/0.99  --prop_solver_per_cl                    1000
% 3.50/0.99  --min_unsat_core                        false
% 3.50/0.99  --soft_assumptions                      false
% 3.50/0.99  --soft_lemma_size                       3
% 3.50/0.99  --prop_impl_unit_size                   0
% 3.50/0.99  --prop_impl_unit                        []
% 3.50/0.99  --share_sel_clauses                     true
% 3.50/0.99  --reset_solvers                         false
% 3.50/0.99  --bc_imp_inh                            [conj_cone]
% 3.50/0.99  --conj_cone_tolerance                   3.
% 3.50/0.99  --extra_neg_conj                        none
% 3.50/0.99  --large_theory_mode                     true
% 3.50/0.99  --prolific_symb_bound                   200
% 3.50/0.99  --lt_threshold                          2000
% 3.50/0.99  --clause_weak_htbl                      true
% 3.50/0.99  --gc_record_bc_elim                     false
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing Options
% 3.50/0.99  
% 3.50/0.99  --preprocessing_flag                    true
% 3.50/0.99  --time_out_prep_mult                    0.1
% 3.50/0.99  --splitting_mode                        input
% 3.50/0.99  --splitting_grd                         true
% 3.50/0.99  --splitting_cvd                         false
% 3.50/0.99  --splitting_cvd_svl                     false
% 3.50/0.99  --splitting_nvd                         32
% 3.50/0.99  --sub_typing                            true
% 3.50/0.99  --prep_gs_sim                           true
% 3.50/0.99  --prep_unflatten                        true
% 3.50/0.99  --prep_res_sim                          true
% 3.50/0.99  --prep_upred                            true
% 3.50/0.99  --prep_sem_filter                       exhaustive
% 3.50/0.99  --prep_sem_filter_out                   false
% 3.50/0.99  --pred_elim                             true
% 3.50/0.99  --res_sim_input                         true
% 3.50/0.99  --eq_ax_congr_red                       true
% 3.50/0.99  --pure_diseq_elim                       true
% 3.50/0.99  --brand_transform                       false
% 3.50/0.99  --non_eq_to_eq                          false
% 3.50/0.99  --prep_def_merge                        true
% 3.50/0.99  --prep_def_merge_prop_impl              false
% 3.50/0.99  --prep_def_merge_mbd                    true
% 3.50/0.99  --prep_def_merge_tr_red                 false
% 3.50/0.99  --prep_def_merge_tr_cl                  false
% 3.50/0.99  --smt_preprocessing                     true
% 3.50/0.99  --smt_ac_axioms                         fast
% 3.50/0.99  --preprocessed_out                      false
% 3.50/0.99  --preprocessed_stats                    false
% 3.50/0.99  
% 3.50/0.99  ------ Abstraction refinement Options
% 3.50/0.99  
% 3.50/0.99  --abstr_ref                             []
% 3.50/0.99  --abstr_ref_prep                        false
% 3.50/0.99  --abstr_ref_until_sat                   false
% 3.50/0.99  --abstr_ref_sig_restrict                funpre
% 3.50/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.50/0.99  --abstr_ref_under                       []
% 3.50/0.99  
% 3.50/0.99  ------ SAT Options
% 3.50/0.99  
% 3.50/0.99  --sat_mode                              false
% 3.50/0.99  --sat_fm_restart_options                ""
% 3.50/0.99  --sat_gr_def                            false
% 3.50/0.99  --sat_epr_types                         true
% 3.50/0.99  --sat_non_cyclic_types                  false
% 3.50/0.99  --sat_finite_models                     false
% 3.50/0.99  --sat_fm_lemmas                         false
% 3.50/0.99  --sat_fm_prep                           false
% 3.50/0.99  --sat_fm_uc_incr                        true
% 3.50/0.99  --sat_out_model                         small
% 3.50/0.99  --sat_out_clauses                       false
% 3.50/0.99  
% 3.50/0.99  ------ QBF Options
% 3.50/0.99  
% 3.50/0.99  --qbf_mode                              false
% 3.50/0.99  --qbf_elim_univ                         false
% 3.50/0.99  --qbf_dom_inst                          none
% 3.50/0.99  --qbf_dom_pre_inst                      false
% 3.50/0.99  --qbf_sk_in                             false
% 3.50/0.99  --qbf_pred_elim                         true
% 3.50/0.99  --qbf_split                             512
% 3.50/0.99  
% 3.50/0.99  ------ BMC1 Options
% 3.50/0.99  
% 3.50/0.99  --bmc1_incremental                      false
% 3.50/0.99  --bmc1_axioms                           reachable_all
% 3.50/0.99  --bmc1_min_bound                        0
% 3.50/0.99  --bmc1_max_bound                        -1
% 3.50/0.99  --bmc1_max_bound_default                -1
% 3.50/0.99  --bmc1_symbol_reachability              true
% 3.50/0.99  --bmc1_property_lemmas                  false
% 3.50/0.99  --bmc1_k_induction                      false
% 3.50/0.99  --bmc1_non_equiv_states                 false
% 3.50/0.99  --bmc1_deadlock                         false
% 3.50/0.99  --bmc1_ucm                              false
% 3.50/0.99  --bmc1_add_unsat_core                   none
% 3.50/0.99  --bmc1_unsat_core_children              false
% 3.50/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.50/0.99  --bmc1_out_stat                         full
% 3.50/0.99  --bmc1_ground_init                      false
% 3.50/0.99  --bmc1_pre_inst_next_state              false
% 3.50/0.99  --bmc1_pre_inst_state                   false
% 3.50/0.99  --bmc1_pre_inst_reach_state             false
% 3.50/0.99  --bmc1_out_unsat_core                   false
% 3.50/0.99  --bmc1_aig_witness_out                  false
% 3.50/0.99  --bmc1_verbose                          false
% 3.50/0.99  --bmc1_dump_clauses_tptp                false
% 3.50/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.50/0.99  --bmc1_dump_file                        -
% 3.50/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.50/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.50/0.99  --bmc1_ucm_extend_mode                  1
% 3.50/0.99  --bmc1_ucm_init_mode                    2
% 3.50/0.99  --bmc1_ucm_cone_mode                    none
% 3.50/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.50/0.99  --bmc1_ucm_relax_model                  4
% 3.50/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.50/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.50/0.99  --bmc1_ucm_layered_model                none
% 3.50/0.99  --bmc1_ucm_max_lemma_size               10
% 3.50/0.99  
% 3.50/0.99  ------ AIG Options
% 3.50/0.99  
% 3.50/0.99  --aig_mode                              false
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation Options
% 3.50/0.99  
% 3.50/0.99  --instantiation_flag                    true
% 3.50/0.99  --inst_sos_flag                         false
% 3.50/0.99  --inst_sos_phase                        true
% 3.50/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.50/0.99  --inst_lit_sel_side                     none
% 3.50/0.99  --inst_solver_per_active                1400
% 3.50/0.99  --inst_solver_calls_frac                1.
% 3.50/0.99  --inst_passive_queue_type               priority_queues
% 3.50/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.50/0.99  --inst_passive_queues_freq              [25;2]
% 3.50/0.99  --inst_dismatching                      true
% 3.50/0.99  --inst_eager_unprocessed_to_passive     true
% 3.50/0.99  --inst_prop_sim_given                   true
% 3.50/0.99  --inst_prop_sim_new                     false
% 3.50/0.99  --inst_subs_new                         false
% 3.50/0.99  --inst_eq_res_simp                      false
% 3.50/0.99  --inst_subs_given                       false
% 3.50/0.99  --inst_orphan_elimination               true
% 3.50/0.99  --inst_learning_loop_flag               true
% 3.50/0.99  --inst_learning_start                   3000
% 3.50/0.99  --inst_learning_factor                  2
% 3.50/0.99  --inst_start_prop_sim_after_learn       3
% 3.50/0.99  --inst_sel_renew                        solver
% 3.50/0.99  --inst_lit_activity_flag                true
% 3.50/0.99  --inst_restr_to_given                   false
% 3.50/0.99  --inst_activity_threshold               500
% 3.50/0.99  --inst_out_proof                        true
% 3.50/0.99  
% 3.50/0.99  ------ Resolution Options
% 3.50/0.99  
% 3.50/0.99  --resolution_flag                       false
% 3.50/0.99  --res_lit_sel                           adaptive
% 3.50/0.99  --res_lit_sel_side                      none
% 3.50/0.99  --res_ordering                          kbo
% 3.50/0.99  --res_to_prop_solver                    active
% 3.50/0.99  --res_prop_simpl_new                    false
% 3.50/0.99  --res_prop_simpl_given                  true
% 3.50/0.99  --res_passive_queue_type                priority_queues
% 3.50/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.50/0.99  --res_passive_queues_freq               [15;5]
% 3.50/0.99  --res_forward_subs                      full
% 3.50/0.99  --res_backward_subs                     full
% 3.50/0.99  --res_forward_subs_resolution           true
% 3.50/0.99  --res_backward_subs_resolution          true
% 3.50/0.99  --res_orphan_elimination                true
% 3.50/0.99  --res_time_limit                        2.
% 3.50/0.99  --res_out_proof                         true
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Options
% 3.50/0.99  
% 3.50/0.99  --superposition_flag                    true
% 3.50/0.99  --sup_passive_queue_type                priority_queues
% 3.50/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.50/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.50/0.99  --demod_completeness_check              fast
% 3.50/0.99  --demod_use_ground                      true
% 3.50/0.99  --sup_to_prop_solver                    passive
% 3.50/0.99  --sup_prop_simpl_new                    true
% 3.50/0.99  --sup_prop_simpl_given                  true
% 3.50/0.99  --sup_fun_splitting                     false
% 3.50/0.99  --sup_smt_interval                      50000
% 3.50/0.99  
% 3.50/0.99  ------ Superposition Simplification Setup
% 3.50/0.99  
% 3.50/0.99  --sup_indices_passive                   []
% 3.50/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.50/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.50/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_full_bw                           [BwDemod]
% 3.50/0.99  --sup_immed_triv                        [TrivRules]
% 3.50/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.50/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_immed_bw_main                     []
% 3.50/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.50/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.50/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.50/0.99  
% 3.50/0.99  ------ Combination Options
% 3.50/0.99  
% 3.50/0.99  --comb_res_mult                         3
% 3.50/0.99  --comb_sup_mult                         2
% 3.50/0.99  --comb_inst_mult                        10
% 3.50/0.99  
% 3.50/0.99  ------ Debug Options
% 3.50/0.99  
% 3.50/0.99  --dbg_backtrace                         false
% 3.50/0.99  --dbg_dump_prop_clauses                 false
% 3.50/0.99  --dbg_dump_prop_clauses_file            -
% 3.50/0.99  --dbg_out_stat                          false
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  ------ Proving...
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS status Theorem for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  fof(f14,conjecture,(
% 3.50/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f15,negated_conjecture,(
% 3.50/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(k2_relset_1(X0,X1,X3),X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.50/0.99    inference(negated_conjecture,[],[f14])).
% 3.50/0.99  
% 3.50/0.99  fof(f28,plain,(
% 3.50/0.99    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(k2_relset_1(X0,X1,X3),X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.50/0.99    inference(ennf_transformation,[],[f15])).
% 3.50/0.99  
% 3.50/0.99  fof(f29,plain,(
% 3.50/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.50/0.99    inference(flattening,[],[f28])).
% 3.50/0.99  
% 3.50/0.99  fof(f37,plain,(
% 3.50/0.99    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(k2_relset_1(X0,X1,X3),X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 3.50/0.99    introduced(choice_axiom,[])).
% 3.50/0.99  
% 3.50/0.99  fof(f38,plain,(
% 3.50/0.99    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 3.50/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f29,f37])).
% 3.50/0.99  
% 3.50/0.99  fof(f64,plain,(
% 3.50/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 3.50/0.99    inference(cnf_transformation,[],[f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f9,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f16,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.50/0.99    inference(pure_predicate_removal,[],[f9])).
% 3.50/0.99  
% 3.50/0.99  fof(f21,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(ennf_transformation,[],[f16])).
% 3.50/0.99  
% 3.50/0.99  fof(f52,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f21])).
% 3.50/0.99  
% 3.50/0.99  fof(f7,axiom,(
% 3.50/0.99    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f19,plain,(
% 3.50/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.50/0.99    inference(ennf_transformation,[],[f7])).
% 3.50/0.99  
% 3.50/0.99  fof(f35,plain,(
% 3.50/0.99    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.50/0.99    inference(nnf_transformation,[],[f19])).
% 3.50/0.99  
% 3.50/0.99  fof(f49,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f35])).
% 3.50/0.99  
% 3.50/0.99  fof(f8,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f20,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(ennf_transformation,[],[f8])).
% 3.50/0.99  
% 3.50/0.99  fof(f51,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f20])).
% 3.50/0.99  
% 3.50/0.99  fof(f11,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f23,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(ennf_transformation,[],[f11])).
% 3.50/0.99  
% 3.50/0.99  fof(f54,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f23])).
% 3.50/0.99  
% 3.50/0.99  fof(f65,plain,(
% 3.50/0.99    r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2)),
% 3.50/0.99    inference(cnf_transformation,[],[f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f12,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f24,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(ennf_transformation,[],[f12])).
% 3.50/0.99  
% 3.50/0.99  fof(f25,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 3.50/0.99    inference(flattening,[],[f24])).
% 3.50/0.99  
% 3.50/0.99  fof(f55,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f25])).
% 3.50/0.99  
% 3.50/0.99  fof(f10,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f22,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(ennf_transformation,[],[f10])).
% 3.50/0.99  
% 3.50/0.99  fof(f53,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f22])).
% 3.50/0.99  
% 3.50/0.99  fof(f13,axiom,(
% 3.50/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f26,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(ennf_transformation,[],[f13])).
% 3.50/0.99  
% 3.50/0.99  fof(f27,plain,(
% 3.50/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(flattening,[],[f26])).
% 3.50/0.99  
% 3.50/0.99  fof(f36,plain,(
% 3.50/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.50/0.99    inference(nnf_transformation,[],[f27])).
% 3.50/0.99  
% 3.50/0.99  fof(f58,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f36])).
% 3.50/0.99  
% 3.50/0.99  fof(f67,plain,(
% 3.50/0.99    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 3.50/0.99    inference(cnf_transformation,[],[f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f62,plain,(
% 3.50/0.99    v1_funct_1(sK3)),
% 3.50/0.99    inference(cnf_transformation,[],[f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f3,axiom,(
% 3.50/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f32,plain,(
% 3.50/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.50/0.99    inference(nnf_transformation,[],[f3])).
% 3.50/0.99  
% 3.50/0.99  fof(f33,plain,(
% 3.50/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.50/0.99    inference(flattening,[],[f32])).
% 3.50/0.99  
% 3.50/0.99  fof(f43,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f44,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.50/0.99    inference(cnf_transformation,[],[f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f71,plain,(
% 3.50/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.50/0.99    inference(equality_resolution,[],[f44])).
% 3.50/0.99  
% 3.50/0.99  fof(f60,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f36])).
% 3.50/0.99  
% 3.50/0.99  fof(f74,plain,(
% 3.50/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.50/0.99    inference(equality_resolution,[],[f60])).
% 3.50/0.99  
% 3.50/0.99  fof(f63,plain,(
% 3.50/0.99    v1_funct_2(sK3,sK0,sK1)),
% 3.50/0.99    inference(cnf_transformation,[],[f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f45,plain,(
% 3.50/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.50/0.99    inference(cnf_transformation,[],[f33])).
% 3.50/0.99  
% 3.50/0.99  fof(f70,plain,(
% 3.50/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.50/0.99    inference(equality_resolution,[],[f45])).
% 3.50/0.99  
% 3.50/0.99  fof(f66,plain,(
% 3.50/0.99    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 3.50/0.99    inference(cnf_transformation,[],[f38])).
% 3.50/0.99  
% 3.50/0.99  fof(f1,axiom,(
% 3.50/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f30,plain,(
% 3.50/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/0.99    inference(nnf_transformation,[],[f1])).
% 3.50/0.99  
% 3.50/0.99  fof(f31,plain,(
% 3.50/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.50/0.99    inference(flattening,[],[f30])).
% 3.50/0.99  
% 3.50/0.99  fof(f41,plain,(
% 3.50/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f31])).
% 3.50/0.99  
% 3.50/0.99  fof(f56,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f36])).
% 3.50/0.99  
% 3.50/0.99  fof(f5,axiom,(
% 3.50/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f34,plain,(
% 3.50/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.50/0.99    inference(nnf_transformation,[],[f5])).
% 3.50/0.99  
% 3.50/0.99  fof(f47,plain,(
% 3.50/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f4,axiom,(
% 3.50/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f46,plain,(
% 3.50/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f4])).
% 3.50/0.99  
% 3.50/0.99  fof(f61,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f36])).
% 3.50/0.99  
% 3.50/0.99  fof(f72,plain,(
% 3.50/0.99    ( ! [X0,X1] : (v1_funct_2(k1_xboole_0,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(equality_resolution,[],[f61])).
% 3.50/0.99  
% 3.50/0.99  fof(f73,plain,(
% 3.50/0.99    ( ! [X0] : (v1_funct_2(k1_xboole_0,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.50/0.99    inference(equality_resolution,[],[f72])).
% 3.50/0.99  
% 3.50/0.99  fof(f48,plain,(
% 3.50/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f34])).
% 3.50/0.99  
% 3.50/0.99  fof(f2,axiom,(
% 3.50/0.99    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.50/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.50/0.99  
% 3.50/0.99  fof(f18,plain,(
% 3.50/0.99    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.50/0.99    inference(ennf_transformation,[],[f2])).
% 3.50/0.99  
% 3.50/0.99  fof(f42,plain,(
% 3.50/0.99    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.50/0.99    inference(cnf_transformation,[],[f18])).
% 3.50/0.99  
% 3.50/0.99  fof(f59,plain,(
% 3.50/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.50/0.99    inference(cnf_transformation,[],[f36])).
% 3.50/0.99  
% 3.50/0.99  fof(f75,plain,(
% 3.50/0.99    ( ! [X2,X1] : (v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 != k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.50/0.99    inference(equality_resolution,[],[f59])).
% 3.50/0.99  
% 3.50/0.99  cnf(c_26,negated_conjecture,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1188,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_13,plain,
% 3.50/0.99      ( v4_relat_1(X0,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.50/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11,plain,
% 3.50/0.99      ( ~ v4_relat_1(X0,X1)
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.50/0.99      | ~ v1_relat_1(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_338,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1)
% 3.50/0.99      | ~ v1_relat_1(X0) ),
% 3.50/0.99      inference(resolution,[status(thm)],[c_13,c_11]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_12,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | v1_relat_1(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_342,plain,
% 3.50/0.99      ( r1_tarski(k1_relat_1(X0),X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_338,c_12]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_343,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_342]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1187,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_343]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1535,plain,
% 3.50/0.99      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1188,c_1187]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_15,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1191,plain,
% 3.50/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2748,plain,
% 3.50/0.99      ( k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1188,c_1191]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_25,negated_conjecture,
% 3.50/0.99      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) ),
% 3.50/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1189,plain,
% 3.50/0.99      ( r1_tarski(k2_relset_1(sK0,sK1,sK3),sK2) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2853,plain,
% 3.50/0.99      ( r1_tarski(k2_relat_1(sK3),sK2) = iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_2748,c_1189]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_16,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | ~ r1_tarski(k2_relat_1(X0),X2)
% 3.50/0.99      | ~ r1_tarski(k1_relat_1(X0),X1)
% 3.50/0.99      | ~ v1_relat_1(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1190,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.50/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_14,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.50/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1192,plain,
% 3.50/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.50/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3231,plain,
% 3.50/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.50/0.99      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 3.50/0.99      | v1_relat_1(X2) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1190,c_1192]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9230,plain,
% 3.50/0.99      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 3.50/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.50/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_2853,c_3231]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_31,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1369,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.50/0.99      | v1_relat_1(sK3) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_12]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1370,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.50/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1369]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9892,plain,
% 3.50/0.99      ( r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.50/0.99      | k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3) ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_9230,c_31,c_1370]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9893,plain,
% 3.50/0.99      ( k1_relset_1(X0,sK2,sK3) = k1_relat_1(sK3)
% 3.50/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_9892]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9903,plain,
% 3.50/0.99      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1535,c_9893]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_20,plain,
% 3.50/0.99      ( v1_funct_2(X0,X1,X2)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.50/0.99      | k1_xboole_0 = X2 ),
% 3.50/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_23,negated_conjecture,
% 3.50/0.99      ( ~ v1_funct_2(sK3,sK0,sK2)
% 3.50/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.50/0.99      | ~ v1_funct_1(sK3) ),
% 3.50/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_28,negated_conjecture,
% 3.50/0.99      ( v1_funct_1(sK3) ),
% 3.50/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_147,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.50/0.99      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_23,c_28]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_148,negated_conjecture,
% 3.50/0.99      ( ~ v1_funct_2(sK3,sK0,sK2)
% 3.50/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_147]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_458,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.50/0.99      | k1_relset_1(X1,X2,X0) != X1
% 3.50/0.99      | sK2 != X2
% 3.50/0.99      | sK0 != X1
% 3.50/0.99      | sK3 != X0
% 3.50/0.99      | k1_xboole_0 = X2 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_148]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_459,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.50/0.99      | k1_relset_1(sK0,sK2,sK3) != sK0
% 3.50/0.99      | k1_xboole_0 = sK2 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_458]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1182,plain,
% 3.50/0.99      ( k1_relset_1(sK0,sK2,sK3) != sK0
% 3.50/0.99      | k1_xboole_0 = sK2
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_459]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9945,plain,
% 3.50/0.99      ( k1_relat_1(sK3) != sK0
% 3.50/0.99      | sK2 = k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_9903,c_1182]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_6,plain,
% 3.50/0.99      ( k2_zfmisc_1(X0,X1) != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = X0
% 3.50/0.99      | k1_xboole_0 = X1 ),
% 3.50/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_82,plain,
% 3.50/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_5,plain,
% 3.50/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_83,plain,
% 3.50/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1379,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.50/0.99      | r1_tarski(k1_relat_1(sK3),sK0) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_343]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1380,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_1379]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_729,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1552,plain,
% 3.50/0.99      ( sK0 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_729]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1553,plain,
% 3.50/0.99      ( sK0 != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = sK0
% 3.50/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1552]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_18,plain,
% 3.50/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.50/0.99      | k1_xboole_0 = X1
% 3.50/0.99      | k1_xboole_0 = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_27,negated_conjecture,
% 3.50/0.99      ( v1_funct_2(sK3,sK0,sK1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_409,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.50/0.99      | sK1 != k1_xboole_0
% 3.50/0.99      | sK0 != X1
% 3.50/0.99      | sK3 != X0
% 3.50/0.99      | k1_xboole_0 = X0
% 3.50/0.99      | k1_xboole_0 = X1 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_410,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.50/0.99      | sK1 != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = sK0
% 3.50/0.99      | k1_xboole_0 = sK3 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_409]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1185,plain,
% 3.50/0.99      ( sK1 != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = sK0
% 3.50/0.99      | k1_xboole_0 = sK3
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_410]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4,plain,
% 3.50/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1277,plain,
% 3.50/0.99      ( sK1 != k1_xboole_0
% 3.50/0.99      | sK0 = k1_xboole_0
% 3.50/0.99      | sK3 = k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_1185,c_4]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_24,negated_conjecture,
% 3.50/0.99      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1388,plain,
% 3.50/0.99      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_729]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1443,plain,
% 3.50/0.99      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1388]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_728,plain,( X0 = X0 ),theory(equality) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1444,plain,
% 3.50/0.99      ( sK0 = sK0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_728]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1561,plain,
% 3.50/0.99      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_729]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1562,plain,
% 3.50/0.99      ( sK1 != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = sK1
% 3.50/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1561]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1771,plain,
% 3.50/0.99      ( sK1 != k1_xboole_0 | sK0 = k1_xboole_0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_1277,c_24,c_82,c_83,c_1443,c_1444,c_1562]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_0,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.50/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2355,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,k1_relat_1(sK3))
% 3.50/0.99      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 3.50/0.99      | k1_relat_1(sK3) = X0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2357,plain,
% 3.50/0.99      ( ~ r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 3.50/0.99      | ~ r1_tarski(k1_xboole_0,k1_relat_1(sK3))
% 3.50/0.99      | k1_relat_1(sK3) = k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2355]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2361,plain,
% 3.50/0.99      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_728]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_22,plain,
% 3.50/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.50/0.99      | k1_xboole_0 = X2 ),
% 3.50/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_471,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.50/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.50/0.99      | sK1 != X2
% 3.50/0.99      | sK0 != X1
% 3.50/0.99      | sK3 != X0
% 3.50/0.99      | k1_xboole_0 = X2 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_472,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 3.50/0.99      | k1_relset_1(sK0,sK1,sK3) = sK0
% 3.50/0.99      | k1_xboole_0 = sK1 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_471]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_474,plain,
% 3.50/0.99      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_472,c_26]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3232,plain,
% 3.50/0.99      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1188,c_1192]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3402,plain,
% 3.50/0.99      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_474,c_3232]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3915,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_relat_1(sK3)))
% 3.50/0.99      | r1_tarski(X0,k1_relat_1(sK3)) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3917,plain,
% 3.50/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK3)))
% 3.50/0.99      | r1_tarski(k1_xboole_0,k1_relat_1(sK3)) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_3915]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_730,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.50/0.99      theory(equality) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1870,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1)
% 3.50/0.99      | r1_tarski(k1_relat_1(sK3),X2)
% 3.50/0.99      | X2 != X1
% 3.50/0.99      | k1_relat_1(sK3) != X0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_730]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2360,plain,
% 3.50/0.99      ( ~ r1_tarski(k1_relat_1(sK3),X0)
% 3.50/0.99      | r1_tarski(k1_relat_1(sK3),X1)
% 3.50/0.99      | X1 != X0
% 3.50/0.99      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1870]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4182,plain,
% 3.50/0.99      ( r1_tarski(k1_relat_1(sK3),X0)
% 3.50/0.99      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 3.50/0.99      | X0 != sK0
% 3.50/0.99      | k1_relat_1(sK3) != k1_relat_1(sK3) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2360]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4184,plain,
% 3.50/0.99      ( ~ r1_tarski(k1_relat_1(sK3),sK0)
% 3.50/0.99      | r1_tarski(k1_relat_1(sK3),k1_xboole_0)
% 3.50/0.99      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 3.50/0.99      | k1_xboole_0 != sK0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_4182]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2129,plain,
% 3.50/0.99      ( X0 != X1 | X0 = sK0 | sK0 != X1 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_729]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4203,plain,
% 3.50/0.99      ( k1_relat_1(sK3) != X0 | k1_relat_1(sK3) = sK0 | sK0 != X0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2129]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4206,plain,
% 3.50/0.99      ( k1_relat_1(sK3) = sK0
% 3.50/0.99      | k1_relat_1(sK3) != k1_xboole_0
% 3.50/0.99      | sK0 != k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_4203]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2225,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))
% 3.50/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.50/0.99      | ~ r1_tarski(k1_relat_1(X0),sK0)
% 3.50/0.99      | ~ v1_relat_1(X0) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4450,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.50/0.99      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 3.50/0.99      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 3.50/0.99      | ~ v1_relat_1(sK3) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2225]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_4451,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 3.50/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_4450]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7,plain,
% 3.50/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.50/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_9872,plain,
% 3.50/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_relat_1(sK3))) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10095,plain,
% 3.50/0.99      ( sK2 = k1_xboole_0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_9945,c_26,c_31,c_82,c_83,c_1370,c_1379,c_1380,c_1553,
% 3.50/0.99                 c_1771,c_2357,c_2361,c_2853,c_3402,c_3917,c_4184,c_4206,
% 3.50/0.99                 c_4451,c_9872]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_17,plain,
% 3.50/0.99      ( v1_funct_2(k1_xboole_0,X0,k1_xboole_0)
% 3.50/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.50/0.99      | k1_xboole_0 = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_386,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.50/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.50/0.99      | sK2 != k1_xboole_0
% 3.50/0.99      | sK0 != X0
% 3.50/0.99      | sK3 != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_148]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_387,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.50/0.99      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 3.50/0.99      | sK2 != k1_xboole_0
% 3.50/0.99      | sK3 != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = sK0 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_386]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_399,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.50/0.99      | sK2 != k1_xboole_0
% 3.50/0.99      | sK3 != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = sK0 ),
% 3.50/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_387,c_7]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1186,plain,
% 3.50/0.99      ( sK2 != k1_xboole_0
% 3.50/0.99      | sK3 != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = sK0
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10115,plain,
% 3.50/0.99      ( sK0 = k1_xboole_0
% 3.50/0.99      | sK3 != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 != k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_10095,c_1186]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10122,plain,
% 3.50/0.99      ( sK0 = k1_xboole_0
% 3.50/0.99      | sK3 != k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 3.50/0.99      inference(equality_resolution_simp,[status(thm)],[c_10115]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10126,plain,
% 3.50/0.99      ( sK0 = k1_xboole_0
% 3.50/0.99      | sK3 != k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_10122,c_4]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_482,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.50/0.99      | sK1 != sK2
% 3.50/0.99      | sK0 != sK0
% 3.50/0.99      | sK3 != sK3 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_148,c_27]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1382,plain,
% 3.50/0.99      ( ~ r1_tarski(sK0,k1_xboole_0)
% 3.50/0.99      | ~ r1_tarski(k1_xboole_0,sK0)
% 3.50/0.99      | sK0 = k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1389,plain,
% 3.50/0.99      ( sK1 != X0 | sK1 = sK2 | sK2 != X0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_729]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1390,plain,
% 3.50/0.99      ( sK1 = sK2 | sK1 != k1_xboole_0 | sK2 != k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1389]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1570,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) | r1_tarski(X0,sK0) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1572,plain,
% 3.50/0.99      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0))
% 3.50/0.99      | r1_tarski(k1_xboole_0,sK0) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1570]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1606,plain,
% 3.50/0.99      ( sK3 = sK3 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_728]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1977,plain,
% 3.50/0.99      ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_728]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2078,plain,
% 3.50/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK0)) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2095,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0)) | r1_tarski(sK3,X0) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2097,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 3.50/0.99      | r1_tarski(sK3,k1_xboole_0) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2095]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2854,plain,
% 3.50/0.99      ( r1_tarski(k2_relat_1(sK3),sK2) ),
% 3.50/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2853]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2894,plain,
% 3.50/0.99      ( sK2 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK2 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_729]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2895,plain,
% 3.50/0.99      ( sK2 != k1_xboole_0
% 3.50/0.99      | k1_xboole_0 = sK2
% 3.50/0.99      | k1_xboole_0 != k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_2894]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2042,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(X0),k1_xboole_0) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 3.50/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_4,c_1190]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3104,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.50/0.99      | v1_relat_1(sK3) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1535,c_2042]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3494,plain,
% 3.50/0.99      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_3104,c_31,c_1370]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3495,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 3.50/0.99      inference(renaming,[status(thm)],[c_3494]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3496,plain,
% 3.50/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0))
% 3.50/0.99      | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0) ),
% 3.50/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3495]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_8,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.50/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1195,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.50/0.99      | r1_tarski(X0,X1) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1538,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_4,c_1187]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2669,plain,
% 3.50/0.99      ( r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.50/0.99      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1195,c_1538]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3544,plain,
% 3.50/0.99      ( sK1 = k1_xboole_0
% 3.50/0.99      | r1_tarski(sK0,X0) = iProver_top
% 3.50/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_3402,c_2669]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3569,plain,
% 3.50/0.99      ( r1_tarski(sK0,X0)
% 3.50/0.99      | ~ r1_tarski(sK3,k1_xboole_0)
% 3.50/0.99      | sK1 = k1_xboole_0 ),
% 3.50/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3544]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3571,plain,
% 3.50/0.99      ( r1_tarski(sK0,k1_xboole_0)
% 3.50/0.99      | ~ r1_tarski(sK3,k1_xboole_0)
% 3.50/0.99      | sK1 = k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_3569]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1525,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,X1)
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3),X2)
% 3.50/0.99      | X2 != X1
% 3.50/0.99      | k2_relat_1(sK3) != X0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_730]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1976,plain,
% 3.50/0.99      ( ~ r1_tarski(k2_relat_1(sK3),X0)
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3),X1)
% 3.50/0.99      | X1 != X0
% 3.50/0.99      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1525]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7456,plain,
% 3.50/0.99      ( r1_tarski(k2_relat_1(sK3),X0)
% 3.50/0.99      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 3.50/0.99      | X0 != sK2
% 3.50/0.99      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_1976]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7463,plain,
% 3.50/0.99      ( ~ r1_tarski(k2_relat_1(sK3),sK2)
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 3.50/0.99      | k2_relat_1(sK3) != k2_relat_1(sK3)
% 3.50/0.99      | k1_xboole_0 != sK2 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_7456]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11136,plain,
% 3.50/0.99      ( sK0 = k1_xboole_0 ),
% 3.50/0.99      inference(global_propositional_subsumption,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_10126,c_26,c_31,c_82,c_83,c_546,c_1369,c_1370,c_1379,
% 3.50/0.99                 c_1380,c_1382,c_1390,c_1553,c_1572,c_1771,c_1977,c_2078,
% 3.50/0.99                 c_2097,c_2357,c_2361,c_2853,c_2854,c_2895,c_3402,c_3496,
% 3.50/0.99                 c_3571,c_3917,c_4184,c_4206,c_4450,c_4451,c_7463,c_9872,
% 3.50/0.99                 c_9945]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1194,plain,
% 3.50/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.50/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_2145,plain,
% 3.50/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK0,sK1)) = iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1188,c_1194]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11175,plain,
% 3.50/0.99      ( r1_tarski(sK3,k2_zfmisc_1(k1_xboole_0,sK1)) = iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_11136,c_2145]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11195,plain,
% 3.50/0.99      ( r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_11175,c_5]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3,plain,
% 3.50/0.99      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1197,plain,
% 3.50/0.99      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3547,plain,
% 3.50/0.99      ( k1_relat_1(X0) = k1_xboole_0
% 3.50/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_2669,c_1197]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11426,plain,
% 3.50/0.99      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_11195,c_3547]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3234,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.50/0.99      | m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_5,c_1192]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_3392,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_relat_1(X1)
% 3.50/0.99      | r1_tarski(X1,k1_xboole_0) != iProver_top ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_1195,c_3234]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11430,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_relat_1(sK3) ),
% 3.50/0.99      inference(superposition,[status(thm)],[c_11195,c_3392]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11464,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,X0,sK3) = k1_xboole_0 ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_11426,c_11430]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_11470,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_11464]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_19,plain,
% 3.50/0.99      ( v1_funct_2(X0,k1_xboole_0,X1)
% 3.50/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.50/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0 ),
% 3.50/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_429,plain,
% 3.50/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.50/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.50/0.99      | k1_relset_1(k1_xboole_0,X1,X0) != k1_xboole_0
% 3.50/0.99      | sK2 != X1
% 3.50/0.99      | sK0 != k1_xboole_0
% 3.50/0.99      | sK3 != X0 ),
% 3.50/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_148]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_430,plain,
% 3.50/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 3.50/0.99      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
% 3.50/0.99      | k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.50/0.99      | sK0 != k1_xboole_0 ),
% 3.50/0.99      inference(unflattening,[status(thm)],[c_429]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1184,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.50/0.99      | sK0 != k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2))) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_430]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_1302,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,sK2,sK3) != k1_xboole_0
% 3.50/0.99      | sK0 != k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_1184,c_5]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10114,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
% 3.50/0.99      | sK0 != k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_10095,c_1302]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_10134,plain,
% 3.50/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) != k1_xboole_0
% 3.50/0.99      | sK0 != k1_xboole_0
% 3.50/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.50/0.99      inference(demodulation,[status(thm)],[c_10114,c_4]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7462,plain,
% 3.50/0.99      ( X0 != sK2
% 3.50/0.99      | k2_relat_1(sK3) != k2_relat_1(sK3)
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3),X0) = iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 3.50/0.99      inference(predicate_to_equality,[status(thm)],[c_7456]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(c_7464,plain,
% 3.50/0.99      ( k2_relat_1(sK3) != k2_relat_1(sK3)
% 3.50/0.99      | k1_xboole_0 != sK2
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 3.50/0.99      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) = iProver_top ),
% 3.50/0.99      inference(instantiation,[status(thm)],[c_7462]) ).
% 3.50/0.99  
% 3.50/0.99  cnf(contradiction,plain,
% 3.50/0.99      ( $false ),
% 3.50/0.99      inference(minisat,
% 3.50/0.99                [status(thm)],
% 3.50/0.99                [c_11470,c_10134,c_10095,c_7464,c_7463,c_4450,c_3571,
% 3.50/0.99                 c_3496,c_3495,c_2895,c_2854,c_2853,c_2097,c_2078,c_1977,
% 3.50/0.99                 c_1606,c_1572,c_1444,c_1390,c_1382,c_1379,c_1369,c_482,
% 3.50/0.99                 c_83,c_82,c_26]) ).
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.50/0.99  
% 3.50/0.99  ------                               Statistics
% 3.50/0.99  
% 3.50/0.99  ------ General
% 3.50/0.99  
% 3.50/0.99  abstr_ref_over_cycles:                  0
% 3.50/0.99  abstr_ref_under_cycles:                 0
% 3.50/0.99  gc_basic_clause_elim:                   0
% 3.50/0.99  forced_gc_time:                         0
% 3.50/0.99  parsing_time:                           0.01
% 3.50/0.99  unif_index_cands_time:                  0.
% 3.50/0.99  unif_index_add_time:                    0.
% 3.50/0.99  orderings_time:                         0.
% 3.50/0.99  out_proof_time:                         0.012
% 3.50/0.99  total_time:                             0.299
% 3.50/0.99  num_of_symbols:                         48
% 3.50/0.99  num_of_terms:                           6837
% 3.50/0.99  
% 3.50/0.99  ------ Preprocessing
% 3.50/0.99  
% 3.50/0.99  num_of_splits:                          0
% 3.50/0.99  num_of_split_atoms:                     0
% 3.50/0.99  num_of_reused_defs:                     0
% 3.50/0.99  num_eq_ax_congr_red:                    13
% 3.50/0.99  num_of_sem_filtered_clauses:            2
% 3.50/0.99  num_of_subtypes:                        0
% 3.50/0.99  monotx_restored_types:                  0
% 3.50/0.99  sat_num_of_epr_types:                   0
% 3.50/0.99  sat_num_of_non_cyclic_types:            0
% 3.50/0.99  sat_guarded_non_collapsed_types:        0
% 3.50/0.99  num_pure_diseq_elim:                    0
% 3.50/0.99  simp_replaced_by:                       0
% 3.50/0.99  res_preprocessed:                       117
% 3.50/0.99  prep_upred:                             0
% 3.50/0.99  prep_unflattend:                        33
% 3.50/0.99  smt_new_axioms:                         0
% 3.50/0.99  pred_elim_cands:                        3
% 3.50/0.99  pred_elim:                              2
% 3.50/0.99  pred_elim_cl:                           3
% 3.50/0.99  pred_elim_cycles:                       5
% 3.50/0.99  merged_defs:                            8
% 3.50/0.99  merged_defs_ncl:                        0
% 3.50/0.99  bin_hyper_res:                          8
% 3.50/0.99  prep_cycles:                            4
% 3.50/0.99  pred_elim_time:                         0.005
% 3.50/0.99  splitting_time:                         0.
% 3.50/0.99  sem_filter_time:                        0.
% 3.50/0.99  monotx_time:                            0.001
% 3.50/0.99  subtype_inf_time:                       0.
% 3.50/0.99  
% 3.50/0.99  ------ Problem properties
% 3.50/0.99  
% 3.50/0.99  clauses:                                24
% 3.50/0.99  conjectures:                            3
% 3.50/0.99  epr:                                    4
% 3.50/0.99  horn:                                   21
% 3.50/0.99  ground:                                 10
% 3.50/0.99  unary:                                  6
% 3.50/0.99  binary:                                 10
% 3.50/0.99  lits:                                   54
% 3.50/0.99  lits_eq:                                26
% 3.50/0.99  fd_pure:                                0
% 3.50/0.99  fd_pseudo:                              0
% 3.50/0.99  fd_cond:                                2
% 3.50/0.99  fd_pseudo_cond:                         1
% 3.50/0.99  ac_symbols:                             0
% 3.50/0.99  
% 3.50/0.99  ------ Propositional Solver
% 3.50/0.99  
% 3.50/0.99  prop_solver_calls:                      30
% 3.50/0.99  prop_fast_solver_calls:                 958
% 3.50/0.99  smt_solver_calls:                       0
% 3.50/0.99  smt_fast_solver_calls:                  0
% 3.50/0.99  prop_num_of_clauses:                    3912
% 3.50/0.99  prop_preprocess_simplified:             10288
% 3.50/0.99  prop_fo_subsumed:                       22
% 3.50/0.99  prop_solver_time:                       0.
% 3.50/0.99  smt_solver_time:                        0.
% 3.50/0.99  smt_fast_solver_time:                   0.
% 3.50/0.99  prop_fast_solver_time:                  0.
% 3.50/0.99  prop_unsat_core_time:                   0.
% 3.50/0.99  
% 3.50/0.99  ------ QBF
% 3.50/0.99  
% 3.50/0.99  qbf_q_res:                              0
% 3.50/0.99  qbf_num_tautologies:                    0
% 3.50/0.99  qbf_prep_cycles:                        0
% 3.50/0.99  
% 3.50/0.99  ------ BMC1
% 3.50/0.99  
% 3.50/0.99  bmc1_current_bound:                     -1
% 3.50/0.99  bmc1_last_solved_bound:                 -1
% 3.50/0.99  bmc1_unsat_core_size:                   -1
% 3.50/0.99  bmc1_unsat_core_parents_size:           -1
% 3.50/0.99  bmc1_merge_next_fun:                    0
% 3.50/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.50/0.99  
% 3.50/0.99  ------ Instantiation
% 3.50/0.99  
% 3.50/0.99  inst_num_of_clauses:                    1202
% 3.50/0.99  inst_num_in_passive:                    686
% 3.50/0.99  inst_num_in_active:                     507
% 3.50/0.99  inst_num_in_unprocessed:                9
% 3.50/0.99  inst_num_of_loops:                      670
% 3.50/0.99  inst_num_of_learning_restarts:          0
% 3.50/0.99  inst_num_moves_active_passive:          160
% 3.50/0.99  inst_lit_activity:                      0
% 3.50/0.99  inst_lit_activity_moves:                0
% 3.50/0.99  inst_num_tautologies:                   0
% 3.50/0.99  inst_num_prop_implied:                  0
% 3.50/0.99  inst_num_existing_simplified:           0
% 3.50/0.99  inst_num_eq_res_simplified:             0
% 3.50/0.99  inst_num_child_elim:                    0
% 3.50/0.99  inst_num_of_dismatching_blockings:      423
% 3.50/0.99  inst_num_of_non_proper_insts:           1507
% 3.50/0.99  inst_num_of_duplicates:                 0
% 3.50/0.99  inst_inst_num_from_inst_to_res:         0
% 3.50/0.99  inst_dismatching_checking_time:         0.
% 3.50/0.99  
% 3.50/0.99  ------ Resolution
% 3.50/0.99  
% 3.50/0.99  res_num_of_clauses:                     0
% 3.50/0.99  res_num_in_passive:                     0
% 3.50/0.99  res_num_in_active:                      0
% 3.50/0.99  res_num_of_loops:                       121
% 3.50/0.99  res_forward_subset_subsumed:            109
% 3.50/0.99  res_backward_subset_subsumed:           0
% 3.50/0.99  res_forward_subsumed:                   0
% 3.50/0.99  res_backward_subsumed:                  0
% 3.50/0.99  res_forward_subsumption_resolution:     1
% 3.50/0.99  res_backward_subsumption_resolution:    0
% 3.50/0.99  res_clause_to_clause_subsumption:       1499
% 3.50/0.99  res_orphan_elimination:                 0
% 3.50/0.99  res_tautology_del:                      98
% 3.50/0.99  res_num_eq_res_simplified:              1
% 3.50/0.99  res_num_sel_changes:                    0
% 3.50/0.99  res_moves_from_active_to_pass:          0
% 3.50/0.99  
% 3.50/0.99  ------ Superposition
% 3.50/0.99  
% 3.50/0.99  sup_time_total:                         0.
% 3.50/0.99  sup_time_generating:                    0.
% 3.50/0.99  sup_time_sim_full:                      0.
% 3.50/0.99  sup_time_sim_immed:                     0.
% 3.50/0.99  
% 3.50/0.99  sup_num_of_clauses:                     189
% 3.50/0.99  sup_num_in_active:                      64
% 3.50/0.99  sup_num_in_passive:                     125
% 3.50/0.99  sup_num_of_loops:                       133
% 3.50/0.99  sup_fw_superposition:                   254
% 3.50/0.99  sup_bw_superposition:                   86
% 3.50/0.99  sup_immediate_simplified:               82
% 3.50/0.99  sup_given_eliminated:                   4
% 3.50/0.99  comparisons_done:                       0
% 3.50/0.99  comparisons_avoided:                    57
% 3.50/0.99  
% 3.50/0.99  ------ Simplifications
% 3.50/0.99  
% 3.50/0.99  
% 3.50/0.99  sim_fw_subset_subsumed:                 16
% 3.50/0.99  sim_bw_subset_subsumed:                 12
% 3.50/0.99  sim_fw_subsumed:                        29
% 3.50/0.99  sim_bw_subsumed:                        7
% 3.50/0.99  sim_fw_subsumption_res:                 1
% 3.50/0.99  sim_bw_subsumption_res:                 0
% 3.50/0.99  sim_tautology_del:                      7
% 3.50/0.99  sim_eq_tautology_del:                   23
% 3.50/0.99  sim_eq_res_simp:                        2
% 3.50/0.99  sim_fw_demodulated:                     18
% 3.50/0.99  sim_bw_demodulated:                     79
% 3.50/0.99  sim_light_normalised:                   30
% 3.50/0.99  sim_joinable_taut:                      0
% 3.50/0.99  sim_joinable_simp:                      0
% 3.50/0.99  sim_ac_normalised:                      0
% 3.50/0.99  sim_smt_subsumption:                    0
% 3.50/0.99  
%------------------------------------------------------------------------------
