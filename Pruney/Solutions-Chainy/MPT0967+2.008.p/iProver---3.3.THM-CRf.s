%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:38 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.45s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_1942)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f38,plain,
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
   => ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
        | ~ v1_funct_2(sK3,sK0,sK2)
        | ~ v1_funct_1(sK3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f38])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f39])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( r1_tarski(k6_relat_1(X1),X2)
       => ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
          & k1_relset_1(X1,X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,k2_relset_1(X1,X0,X2))
        & k1_relset_1(X1,X0,X2) = X1 )
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(flattening,[],[f25])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X1,X0,X2) = X1
      | ~ r1_tarski(k6_relat_1(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f39])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f61])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f67,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f70,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f39])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1557,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k6_relat_1(X1),X0)
    | k1_relset_1(X1,X2,X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1559,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | r1_tarski(k6_relat_1(X0),X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_3126,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | r1_tarski(k6_relat_1(sK0),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1559])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1562,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2483,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1557,c_1562])).

cnf(c_3133,plain,
    ( k1_relat_1(sK3) = sK0
    | r1_tarski(k6_relat_1(sK0),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3126,c_2483])).

cnf(c_34,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_28,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_35,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_95,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_100,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_24,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_323,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_31])).

cnf(c_324,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_323])).

cnf(c_516,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(sK3),X2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != X1
    | sK3 != X0
    | k1_xboole_0 != X2
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_324])).

cnf(c_517,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_516])).

cnf(c_23,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_338,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_31])).

cnf(c_339,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(unflattening,[status(thm)],[c_338])).

cnf(c_341,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
    | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_339])).

cnf(c_519,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_517,c_341])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1786,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1787,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1786])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1793,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v5_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1794,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v5_relat_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1793])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_361,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_12,c_5])).

cnf(c_365,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_361,c_10])).

cnf(c_366,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_365])).

cnf(c_1796,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(instantiation,[status(thm)],[c_366])).

cnf(c_1110,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1943,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1881,plain,
    ( ~ v5_relat_1(sK3,X0)
    | r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1999,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | r1_tarski(k2_relat_1(sK3),sK1)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1881])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X0,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1880,plain,
    ( ~ v5_relat_1(sK3,X0)
    | v5_relat_1(sK3,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2056,plain,
    ( v5_relat_1(sK3,X0)
    | ~ v5_relat_1(sK3,sK1)
    | ~ r1_tarski(sK1,X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1880])).

cnf(c_2058,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | v5_relat_1(sK3,k1_xboole_0)
    | ~ r1_tarski(sK1,k1_xboole_0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2056])).

cnf(c_2075,plain,
    ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_1111,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2100,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_1111])).

cnf(c_2101,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2100])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_500,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_30])).

cnf(c_501,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_500])).

cnf(c_1553,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_501])).

cnf(c_27,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2165,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1553,c_27,c_95,c_100,c_2101])).

cnf(c_1817,plain,
    ( k1_relat_1(sK3) != X0
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1111])).

cnf(c_2185,plain,
    ( k1_relat_1(sK3) != k1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_2186,plain,
    ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1110])).

cnf(c_2188,plain,
    ( k1_relat_1(sK3) != k1_relat_1(X0)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1817])).

cnf(c_2190,plain,
    ( k1_relat_1(sK3) != k1_relat_1(k1_xboole_0)
    | k1_relat_1(sK3) = k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2188])).

cnf(c_1113,plain,
    ( X0 != X1
    | k1_relat_1(X0) = k1_relat_1(X1) ),
    theory(equality)).

cnf(c_2189,plain,
    ( k1_relat_1(sK3) = k1_relat_1(X0)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_2191,plain,
    ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2189])).

cnf(c_1112,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2277,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK1,k1_xboole_0)
    | sK1 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_2279,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK1 != k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2277])).

cnf(c_2345,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | v5_relat_1(sK3,sK2)
    | ~ r1_tarski(sK1,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2056])).

cnf(c_2346,plain,
    ( v5_relat_1(sK3,sK1) != iProver_top
    | v5_relat_1(sK3,sK2) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2345])).

cnf(c_2367,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1881])).

cnf(c_2368,plain,
    ( v5_relat_1(sK3,sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2367])).

cnf(c_2383,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2387,plain,
    ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2383])).

cnf(c_1566,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_1552,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_521,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_519])).

cnf(c_2270,plain,
    ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
    | k1_xboole_0 = sK3
    | k1_xboole_0 = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1552,c_34,c_521,c_1787])).

cnf(c_2271,plain,
    ( k1_xboole_0 = k1_relat_1(sK3)
    | k1_xboole_0 = sK3
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2270])).

cnf(c_2561,plain,
    ( k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0
    | v5_relat_1(sK3,k1_xboole_0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1566,c_2271])).

cnf(c_2590,plain,
    ( ~ v5_relat_1(sK3,k1_xboole_0)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2561])).

cnf(c_1555,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_366])).

cnf(c_2411,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1557,c_1555])).

cnf(c_1570,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2692,plain,
    ( k1_relat_1(sK3) = sK0
    | r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2411,c_1570])).

cnf(c_2693,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | k1_relat_1(sK3) = sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2692])).

cnf(c_1909,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k2_relat_1(sK3),X2)
    | X2 != X1
    | k2_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_2074,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),X0)
    | r1_tarski(k2_relat_1(sK3),X1)
    | X1 != X0
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1909])).

cnf(c_2732,plain,
    ( r1_tarski(k2_relat_1(sK3),X0)
    | ~ r1_tarski(k2_relat_1(sK3),sK1)
    | X0 != sK1
    | k2_relat_1(sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2074])).

cnf(c_2734,plain,
    ( ~ r1_tarski(k2_relat_1(sK3),sK1)
    | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
    | k2_relat_1(sK3) != k2_relat_1(sK3)
    | k1_xboole_0 != sK1 ),
    inference(instantiation,[status(thm)],[c_2732])).

cnf(c_2339,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_relat_1(sK3))
    | k1_relat_1(sK3) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_2753,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k1_relat_1(sK3))
    | k1_relat_1(sK3) != X0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2339])).

cnf(c_2755,plain,
    ( r1_tarski(sK0,k1_relat_1(sK3))
    | ~ r1_tarski(sK0,k1_xboole_0)
    | k1_relat_1(sK3) != k1_xboole_0
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2753])).

cnf(c_1934,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != X0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_2147,plain,
    ( ~ r1_tarski(sK0,X0)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != sK0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1934])).

cnf(c_2868,plain,
    ( ~ r1_tarski(sK0,sK0)
    | r1_tarski(sK0,k1_xboole_0)
    | sK0 != sK0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2147])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2869,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_605,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_30])).

cnf(c_606,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_605])).

cnf(c_608,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_606,c_29])).

cnf(c_2809,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_608,c_2483])).

cnf(c_26,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_167,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_26,c_31])).

cnf(c_168,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_167])).

cnf(c_655,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != sK0
    | sK2 != X0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_168,c_324])).

cnf(c_656,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(sK3) != sK0 ),
    inference(unflattening,[status(thm)],[c_655])).

cnf(c_666,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | k1_relat_1(sK3) != sK0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_656,c_10])).

cnf(c_1546,plain,
    ( k1_relat_1(sK3) != sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_2909,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2809,c_1546])).

cnf(c_1556,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_340,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_339])).

cnf(c_1867,plain,
    ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1556,c_34,c_340,c_1787])).

cnf(c_1868,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_1867])).

cnf(c_2910,plain,
    ( sK1 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2809,c_1868])).

cnf(c_2920,plain,
    ( sK1 = k1_xboole_0
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2909,c_2910])).

cnf(c_1833,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(k1_relat_1(X2),X3)
    | X3 != X1
    | k1_relat_1(X2) != X0 ),
    inference(instantiation,[status(thm)],[c_1112])).

cnf(c_2232,plain,
    ( ~ r1_tarski(k1_relat_1(X0),X1)
    | r1_tarski(k1_relat_1(X2),X3)
    | X3 != X1
    | k1_relat_1(X2) != k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_1833])).

cnf(c_2960,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | X1 != sK0
    | k1_relat_1(X0) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2232])).

cnf(c_2962,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK0)
    | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | k1_relat_1(k1_xboole_0) != k1_relat_1(sK3)
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2960])).

cnf(c_3026,plain,
    ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
    | k1_xboole_0 = k1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_3028,plain,
    ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
    | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3026])).

cnf(c_3266,plain,
    ( X0 != sK3
    | k1_relat_1(X0) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1113])).

cnf(c_3267,plain,
    ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK3)
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3266])).

cnf(c_3356,plain,
    ( k1_relat_1(sK3) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3133,c_29,c_34,c_35,c_95,c_100,c_519,c_1786,c_1787,c_1793,c_1794,c_1796,c_1942,c_1943,c_1999,c_2058,c_2075,c_2101,c_2165,c_2185,c_2186,c_2190,c_2191,c_2279,c_2341,c_2346,c_2368,c_2387,c_2590,c_2693,c_2734,c_2920,c_2962,c_3028,c_3267])).

cnf(c_3367,plain,
    ( sK0 != sK0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3356,c_1546])).

cnf(c_3373,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3367])).

cnf(c_3368,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3356,c_1868])).

cnf(c_3376,plain,
    ( r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3373,c_3368])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3376,c_2368,c_2346,c_1794,c_1787,c_35,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:37:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 2.45/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.01  
% 2.45/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.45/1.01  
% 2.45/1.01  ------  iProver source info
% 2.45/1.01  
% 2.45/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.45/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.45/1.01  git: non_committed_changes: false
% 2.45/1.01  git: last_make_outside_of_git: false
% 2.45/1.01  
% 2.45/1.01  ------ 
% 2.45/1.01  
% 2.45/1.01  ------ Input Options
% 2.45/1.01  
% 2.45/1.01  --out_options                           all
% 2.45/1.01  --tptp_safe_out                         true
% 2.45/1.01  --problem_path                          ""
% 2.45/1.01  --include_path                          ""
% 2.45/1.01  --clausifier                            res/vclausify_rel
% 2.45/1.01  --clausifier_options                    --mode clausify
% 2.45/1.01  --stdin                                 false
% 2.45/1.01  --stats_out                             all
% 2.45/1.01  
% 2.45/1.01  ------ General Options
% 2.45/1.01  
% 2.45/1.01  --fof                                   false
% 2.45/1.01  --time_out_real                         305.
% 2.45/1.01  --time_out_virtual                      -1.
% 2.45/1.01  --symbol_type_check                     false
% 2.45/1.01  --clausify_out                          false
% 2.45/1.01  --sig_cnt_out                           false
% 2.45/1.01  --trig_cnt_out                          false
% 2.45/1.01  --trig_cnt_out_tolerance                1.
% 2.45/1.01  --trig_cnt_out_sk_spl                   false
% 2.45/1.01  --abstr_cl_out                          false
% 2.45/1.01  
% 2.45/1.01  ------ Global Options
% 2.45/1.01  
% 2.45/1.01  --schedule                              default
% 2.45/1.01  --add_important_lit                     false
% 2.45/1.01  --prop_solver_per_cl                    1000
% 2.45/1.01  --min_unsat_core                        false
% 2.45/1.01  --soft_assumptions                      false
% 2.45/1.01  --soft_lemma_size                       3
% 2.45/1.01  --prop_impl_unit_size                   0
% 2.45/1.01  --prop_impl_unit                        []
% 2.45/1.01  --share_sel_clauses                     true
% 2.45/1.01  --reset_solvers                         false
% 2.45/1.01  --bc_imp_inh                            [conj_cone]
% 2.45/1.01  --conj_cone_tolerance                   3.
% 2.45/1.01  --extra_neg_conj                        none
% 2.45/1.01  --large_theory_mode                     true
% 2.45/1.01  --prolific_symb_bound                   200
% 2.45/1.01  --lt_threshold                          2000
% 2.45/1.01  --clause_weak_htbl                      true
% 2.45/1.01  --gc_record_bc_elim                     false
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing Options
% 2.45/1.01  
% 2.45/1.01  --preprocessing_flag                    true
% 2.45/1.01  --time_out_prep_mult                    0.1
% 2.45/1.01  --splitting_mode                        input
% 2.45/1.01  --splitting_grd                         true
% 2.45/1.01  --splitting_cvd                         false
% 2.45/1.01  --splitting_cvd_svl                     false
% 2.45/1.01  --splitting_nvd                         32
% 2.45/1.01  --sub_typing                            true
% 2.45/1.01  --prep_gs_sim                           true
% 2.45/1.01  --prep_unflatten                        true
% 2.45/1.01  --prep_res_sim                          true
% 2.45/1.01  --prep_upred                            true
% 2.45/1.01  --prep_sem_filter                       exhaustive
% 2.45/1.01  --prep_sem_filter_out                   false
% 2.45/1.01  --pred_elim                             true
% 2.45/1.01  --res_sim_input                         true
% 2.45/1.01  --eq_ax_congr_red                       true
% 2.45/1.01  --pure_diseq_elim                       true
% 2.45/1.01  --brand_transform                       false
% 2.45/1.01  --non_eq_to_eq                          false
% 2.45/1.01  --prep_def_merge                        true
% 2.45/1.01  --prep_def_merge_prop_impl              false
% 2.45/1.01  --prep_def_merge_mbd                    true
% 2.45/1.01  --prep_def_merge_tr_red                 false
% 2.45/1.01  --prep_def_merge_tr_cl                  false
% 2.45/1.01  --smt_preprocessing                     true
% 2.45/1.01  --smt_ac_axioms                         fast
% 2.45/1.01  --preprocessed_out                      false
% 2.45/1.01  --preprocessed_stats                    false
% 2.45/1.01  
% 2.45/1.01  ------ Abstraction refinement Options
% 2.45/1.01  
% 2.45/1.01  --abstr_ref                             []
% 2.45/1.01  --abstr_ref_prep                        false
% 2.45/1.01  --abstr_ref_until_sat                   false
% 2.45/1.01  --abstr_ref_sig_restrict                funpre
% 2.45/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.01  --abstr_ref_under                       []
% 2.45/1.01  
% 2.45/1.01  ------ SAT Options
% 2.45/1.01  
% 2.45/1.01  --sat_mode                              false
% 2.45/1.01  --sat_fm_restart_options                ""
% 2.45/1.01  --sat_gr_def                            false
% 2.45/1.01  --sat_epr_types                         true
% 2.45/1.01  --sat_non_cyclic_types                  false
% 2.45/1.01  --sat_finite_models                     false
% 2.45/1.01  --sat_fm_lemmas                         false
% 2.45/1.01  --sat_fm_prep                           false
% 2.45/1.01  --sat_fm_uc_incr                        true
% 2.45/1.01  --sat_out_model                         small
% 2.45/1.01  --sat_out_clauses                       false
% 2.45/1.01  
% 2.45/1.01  ------ QBF Options
% 2.45/1.01  
% 2.45/1.01  --qbf_mode                              false
% 2.45/1.01  --qbf_elim_univ                         false
% 2.45/1.01  --qbf_dom_inst                          none
% 2.45/1.01  --qbf_dom_pre_inst                      false
% 2.45/1.01  --qbf_sk_in                             false
% 2.45/1.01  --qbf_pred_elim                         true
% 2.45/1.01  --qbf_split                             512
% 2.45/1.01  
% 2.45/1.01  ------ BMC1 Options
% 2.45/1.01  
% 2.45/1.01  --bmc1_incremental                      false
% 2.45/1.01  --bmc1_axioms                           reachable_all
% 2.45/1.01  --bmc1_min_bound                        0
% 2.45/1.01  --bmc1_max_bound                        -1
% 2.45/1.01  --bmc1_max_bound_default                -1
% 2.45/1.01  --bmc1_symbol_reachability              true
% 2.45/1.01  --bmc1_property_lemmas                  false
% 2.45/1.01  --bmc1_k_induction                      false
% 2.45/1.01  --bmc1_non_equiv_states                 false
% 2.45/1.01  --bmc1_deadlock                         false
% 2.45/1.01  --bmc1_ucm                              false
% 2.45/1.01  --bmc1_add_unsat_core                   none
% 2.45/1.01  --bmc1_unsat_core_children              false
% 2.45/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.01  --bmc1_out_stat                         full
% 2.45/1.01  --bmc1_ground_init                      false
% 2.45/1.01  --bmc1_pre_inst_next_state              false
% 2.45/1.01  --bmc1_pre_inst_state                   false
% 2.45/1.01  --bmc1_pre_inst_reach_state             false
% 2.45/1.01  --bmc1_out_unsat_core                   false
% 2.45/1.01  --bmc1_aig_witness_out                  false
% 2.45/1.01  --bmc1_verbose                          false
% 2.45/1.01  --bmc1_dump_clauses_tptp                false
% 2.45/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.01  --bmc1_dump_file                        -
% 2.45/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.01  --bmc1_ucm_extend_mode                  1
% 2.45/1.01  --bmc1_ucm_init_mode                    2
% 2.45/1.01  --bmc1_ucm_cone_mode                    none
% 2.45/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.01  --bmc1_ucm_relax_model                  4
% 2.45/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.01  --bmc1_ucm_layered_model                none
% 2.45/1.01  --bmc1_ucm_max_lemma_size               10
% 2.45/1.01  
% 2.45/1.01  ------ AIG Options
% 2.45/1.01  
% 2.45/1.01  --aig_mode                              false
% 2.45/1.01  
% 2.45/1.01  ------ Instantiation Options
% 2.45/1.01  
% 2.45/1.01  --instantiation_flag                    true
% 2.45/1.01  --inst_sos_flag                         false
% 2.45/1.01  --inst_sos_phase                        true
% 2.45/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel_side                     num_symb
% 2.45/1.01  --inst_solver_per_active                1400
% 2.45/1.01  --inst_solver_calls_frac                1.
% 2.45/1.01  --inst_passive_queue_type               priority_queues
% 2.45/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.01  --inst_passive_queues_freq              [25;2]
% 2.45/1.01  --inst_dismatching                      true
% 2.45/1.01  --inst_eager_unprocessed_to_passive     true
% 2.45/1.01  --inst_prop_sim_given                   true
% 2.45/1.01  --inst_prop_sim_new                     false
% 2.45/1.01  --inst_subs_new                         false
% 2.45/1.01  --inst_eq_res_simp                      false
% 2.45/1.01  --inst_subs_given                       false
% 2.45/1.01  --inst_orphan_elimination               true
% 2.45/1.01  --inst_learning_loop_flag               true
% 2.45/1.01  --inst_learning_start                   3000
% 2.45/1.01  --inst_learning_factor                  2
% 2.45/1.01  --inst_start_prop_sim_after_learn       3
% 2.45/1.01  --inst_sel_renew                        solver
% 2.45/1.01  --inst_lit_activity_flag                true
% 2.45/1.01  --inst_restr_to_given                   false
% 2.45/1.01  --inst_activity_threshold               500
% 2.45/1.01  --inst_out_proof                        true
% 2.45/1.01  
% 2.45/1.01  ------ Resolution Options
% 2.45/1.01  
% 2.45/1.01  --resolution_flag                       true
% 2.45/1.01  --res_lit_sel                           adaptive
% 2.45/1.01  --res_lit_sel_side                      none
% 2.45/1.01  --res_ordering                          kbo
% 2.45/1.01  --res_to_prop_solver                    active
% 2.45/1.01  --res_prop_simpl_new                    false
% 2.45/1.01  --res_prop_simpl_given                  true
% 2.45/1.01  --res_passive_queue_type                priority_queues
% 2.45/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.01  --res_passive_queues_freq               [15;5]
% 2.45/1.01  --res_forward_subs                      full
% 2.45/1.01  --res_backward_subs                     full
% 2.45/1.01  --res_forward_subs_resolution           true
% 2.45/1.01  --res_backward_subs_resolution          true
% 2.45/1.01  --res_orphan_elimination                true
% 2.45/1.01  --res_time_limit                        2.
% 2.45/1.01  --res_out_proof                         true
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Options
% 2.45/1.01  
% 2.45/1.01  --superposition_flag                    true
% 2.45/1.01  --sup_passive_queue_type                priority_queues
% 2.45/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.01  --demod_completeness_check              fast
% 2.45/1.01  --demod_use_ground                      true
% 2.45/1.01  --sup_to_prop_solver                    passive
% 2.45/1.01  --sup_prop_simpl_new                    true
% 2.45/1.01  --sup_prop_simpl_given                  true
% 2.45/1.01  --sup_fun_splitting                     false
% 2.45/1.01  --sup_smt_interval                      50000
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Simplification Setup
% 2.45/1.01  
% 2.45/1.01  --sup_indices_passive                   []
% 2.45/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_full_bw                           [BwDemod]
% 2.45/1.01  --sup_immed_triv                        [TrivRules]
% 2.45/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_immed_bw_main                     []
% 2.45/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  
% 2.45/1.01  ------ Combination Options
% 2.45/1.01  
% 2.45/1.01  --comb_res_mult                         3
% 2.45/1.01  --comb_sup_mult                         2
% 2.45/1.01  --comb_inst_mult                        10
% 2.45/1.01  
% 2.45/1.01  ------ Debug Options
% 2.45/1.01  
% 2.45/1.01  --dbg_backtrace                         false
% 2.45/1.01  --dbg_dump_prop_clauses                 false
% 2.45/1.01  --dbg_dump_prop_clauses_file            -
% 2.45/1.01  --dbg_out_stat                          false
% 2.45/1.01  ------ Parsing...
% 2.45/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.45/1.01  ------ Proving...
% 2.45/1.01  ------ Problem Properties 
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  clauses                                 29
% 2.45/1.01  conjectures                             3
% 2.45/1.01  EPR                                     6
% 2.45/1.01  Horn                                    25
% 2.45/1.01  unary                                   5
% 2.45/1.01  binary                                  7
% 2.45/1.01  lits                                    78
% 2.45/1.01  lits eq                                 28
% 2.45/1.01  fd_pure                                 0
% 2.45/1.01  fd_pseudo                               0
% 2.45/1.01  fd_cond                                 1
% 2.45/1.01  fd_pseudo_cond                          1
% 2.45/1.01  AC symbols                              0
% 2.45/1.01  
% 2.45/1.01  ------ Schedule dynamic 5 is on 
% 2.45/1.01  
% 2.45/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  ------ 
% 2.45/1.01  Current options:
% 2.45/1.01  ------ 
% 2.45/1.01  
% 2.45/1.01  ------ Input Options
% 2.45/1.01  
% 2.45/1.01  --out_options                           all
% 2.45/1.01  --tptp_safe_out                         true
% 2.45/1.01  --problem_path                          ""
% 2.45/1.01  --include_path                          ""
% 2.45/1.01  --clausifier                            res/vclausify_rel
% 2.45/1.01  --clausifier_options                    --mode clausify
% 2.45/1.01  --stdin                                 false
% 2.45/1.01  --stats_out                             all
% 2.45/1.01  
% 2.45/1.01  ------ General Options
% 2.45/1.01  
% 2.45/1.01  --fof                                   false
% 2.45/1.01  --time_out_real                         305.
% 2.45/1.01  --time_out_virtual                      -1.
% 2.45/1.01  --symbol_type_check                     false
% 2.45/1.01  --clausify_out                          false
% 2.45/1.01  --sig_cnt_out                           false
% 2.45/1.01  --trig_cnt_out                          false
% 2.45/1.01  --trig_cnt_out_tolerance                1.
% 2.45/1.01  --trig_cnt_out_sk_spl                   false
% 2.45/1.01  --abstr_cl_out                          false
% 2.45/1.01  
% 2.45/1.01  ------ Global Options
% 2.45/1.01  
% 2.45/1.01  --schedule                              default
% 2.45/1.01  --add_important_lit                     false
% 2.45/1.01  --prop_solver_per_cl                    1000
% 2.45/1.01  --min_unsat_core                        false
% 2.45/1.01  --soft_assumptions                      false
% 2.45/1.01  --soft_lemma_size                       3
% 2.45/1.01  --prop_impl_unit_size                   0
% 2.45/1.01  --prop_impl_unit                        []
% 2.45/1.01  --share_sel_clauses                     true
% 2.45/1.01  --reset_solvers                         false
% 2.45/1.01  --bc_imp_inh                            [conj_cone]
% 2.45/1.01  --conj_cone_tolerance                   3.
% 2.45/1.01  --extra_neg_conj                        none
% 2.45/1.01  --large_theory_mode                     true
% 2.45/1.01  --prolific_symb_bound                   200
% 2.45/1.01  --lt_threshold                          2000
% 2.45/1.01  --clause_weak_htbl                      true
% 2.45/1.01  --gc_record_bc_elim                     false
% 2.45/1.01  
% 2.45/1.01  ------ Preprocessing Options
% 2.45/1.01  
% 2.45/1.01  --preprocessing_flag                    true
% 2.45/1.01  --time_out_prep_mult                    0.1
% 2.45/1.01  --splitting_mode                        input
% 2.45/1.01  --splitting_grd                         true
% 2.45/1.01  --splitting_cvd                         false
% 2.45/1.01  --splitting_cvd_svl                     false
% 2.45/1.01  --splitting_nvd                         32
% 2.45/1.01  --sub_typing                            true
% 2.45/1.01  --prep_gs_sim                           true
% 2.45/1.01  --prep_unflatten                        true
% 2.45/1.01  --prep_res_sim                          true
% 2.45/1.01  --prep_upred                            true
% 2.45/1.01  --prep_sem_filter                       exhaustive
% 2.45/1.01  --prep_sem_filter_out                   false
% 2.45/1.01  --pred_elim                             true
% 2.45/1.01  --res_sim_input                         true
% 2.45/1.01  --eq_ax_congr_red                       true
% 2.45/1.01  --pure_diseq_elim                       true
% 2.45/1.01  --brand_transform                       false
% 2.45/1.01  --non_eq_to_eq                          false
% 2.45/1.01  --prep_def_merge                        true
% 2.45/1.01  --prep_def_merge_prop_impl              false
% 2.45/1.01  --prep_def_merge_mbd                    true
% 2.45/1.01  --prep_def_merge_tr_red                 false
% 2.45/1.01  --prep_def_merge_tr_cl                  false
% 2.45/1.01  --smt_preprocessing                     true
% 2.45/1.01  --smt_ac_axioms                         fast
% 2.45/1.01  --preprocessed_out                      false
% 2.45/1.01  --preprocessed_stats                    false
% 2.45/1.01  
% 2.45/1.01  ------ Abstraction refinement Options
% 2.45/1.01  
% 2.45/1.01  --abstr_ref                             []
% 2.45/1.01  --abstr_ref_prep                        false
% 2.45/1.01  --abstr_ref_until_sat                   false
% 2.45/1.01  --abstr_ref_sig_restrict                funpre
% 2.45/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.45/1.01  --abstr_ref_under                       []
% 2.45/1.01  
% 2.45/1.01  ------ SAT Options
% 2.45/1.01  
% 2.45/1.01  --sat_mode                              false
% 2.45/1.01  --sat_fm_restart_options                ""
% 2.45/1.01  --sat_gr_def                            false
% 2.45/1.01  --sat_epr_types                         true
% 2.45/1.01  --sat_non_cyclic_types                  false
% 2.45/1.01  --sat_finite_models                     false
% 2.45/1.01  --sat_fm_lemmas                         false
% 2.45/1.01  --sat_fm_prep                           false
% 2.45/1.01  --sat_fm_uc_incr                        true
% 2.45/1.01  --sat_out_model                         small
% 2.45/1.01  --sat_out_clauses                       false
% 2.45/1.01  
% 2.45/1.01  ------ QBF Options
% 2.45/1.01  
% 2.45/1.01  --qbf_mode                              false
% 2.45/1.01  --qbf_elim_univ                         false
% 2.45/1.01  --qbf_dom_inst                          none
% 2.45/1.01  --qbf_dom_pre_inst                      false
% 2.45/1.01  --qbf_sk_in                             false
% 2.45/1.01  --qbf_pred_elim                         true
% 2.45/1.01  --qbf_split                             512
% 2.45/1.01  
% 2.45/1.01  ------ BMC1 Options
% 2.45/1.01  
% 2.45/1.01  --bmc1_incremental                      false
% 2.45/1.01  --bmc1_axioms                           reachable_all
% 2.45/1.01  --bmc1_min_bound                        0
% 2.45/1.01  --bmc1_max_bound                        -1
% 2.45/1.01  --bmc1_max_bound_default                -1
% 2.45/1.01  --bmc1_symbol_reachability              true
% 2.45/1.01  --bmc1_property_lemmas                  false
% 2.45/1.01  --bmc1_k_induction                      false
% 2.45/1.01  --bmc1_non_equiv_states                 false
% 2.45/1.01  --bmc1_deadlock                         false
% 2.45/1.01  --bmc1_ucm                              false
% 2.45/1.01  --bmc1_add_unsat_core                   none
% 2.45/1.01  --bmc1_unsat_core_children              false
% 2.45/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.45/1.01  --bmc1_out_stat                         full
% 2.45/1.01  --bmc1_ground_init                      false
% 2.45/1.01  --bmc1_pre_inst_next_state              false
% 2.45/1.01  --bmc1_pre_inst_state                   false
% 2.45/1.01  --bmc1_pre_inst_reach_state             false
% 2.45/1.01  --bmc1_out_unsat_core                   false
% 2.45/1.01  --bmc1_aig_witness_out                  false
% 2.45/1.01  --bmc1_verbose                          false
% 2.45/1.01  --bmc1_dump_clauses_tptp                false
% 2.45/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.45/1.01  --bmc1_dump_file                        -
% 2.45/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.45/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.45/1.01  --bmc1_ucm_extend_mode                  1
% 2.45/1.01  --bmc1_ucm_init_mode                    2
% 2.45/1.01  --bmc1_ucm_cone_mode                    none
% 2.45/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.45/1.01  --bmc1_ucm_relax_model                  4
% 2.45/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.45/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.45/1.01  --bmc1_ucm_layered_model                none
% 2.45/1.01  --bmc1_ucm_max_lemma_size               10
% 2.45/1.01  
% 2.45/1.01  ------ AIG Options
% 2.45/1.01  
% 2.45/1.01  --aig_mode                              false
% 2.45/1.01  
% 2.45/1.01  ------ Instantiation Options
% 2.45/1.01  
% 2.45/1.01  --instantiation_flag                    true
% 2.45/1.01  --inst_sos_flag                         false
% 2.45/1.01  --inst_sos_phase                        true
% 2.45/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.45/1.01  --inst_lit_sel_side                     none
% 2.45/1.01  --inst_solver_per_active                1400
% 2.45/1.01  --inst_solver_calls_frac                1.
% 2.45/1.01  --inst_passive_queue_type               priority_queues
% 2.45/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.45/1.01  --inst_passive_queues_freq              [25;2]
% 2.45/1.01  --inst_dismatching                      true
% 2.45/1.01  --inst_eager_unprocessed_to_passive     true
% 2.45/1.01  --inst_prop_sim_given                   true
% 2.45/1.01  --inst_prop_sim_new                     false
% 2.45/1.01  --inst_subs_new                         false
% 2.45/1.01  --inst_eq_res_simp                      false
% 2.45/1.01  --inst_subs_given                       false
% 2.45/1.01  --inst_orphan_elimination               true
% 2.45/1.01  --inst_learning_loop_flag               true
% 2.45/1.01  --inst_learning_start                   3000
% 2.45/1.01  --inst_learning_factor                  2
% 2.45/1.01  --inst_start_prop_sim_after_learn       3
% 2.45/1.01  --inst_sel_renew                        solver
% 2.45/1.01  --inst_lit_activity_flag                true
% 2.45/1.01  --inst_restr_to_given                   false
% 2.45/1.01  --inst_activity_threshold               500
% 2.45/1.01  --inst_out_proof                        true
% 2.45/1.01  
% 2.45/1.01  ------ Resolution Options
% 2.45/1.01  
% 2.45/1.01  --resolution_flag                       false
% 2.45/1.01  --res_lit_sel                           adaptive
% 2.45/1.01  --res_lit_sel_side                      none
% 2.45/1.01  --res_ordering                          kbo
% 2.45/1.01  --res_to_prop_solver                    active
% 2.45/1.01  --res_prop_simpl_new                    false
% 2.45/1.01  --res_prop_simpl_given                  true
% 2.45/1.01  --res_passive_queue_type                priority_queues
% 2.45/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.45/1.01  --res_passive_queues_freq               [15;5]
% 2.45/1.01  --res_forward_subs                      full
% 2.45/1.01  --res_backward_subs                     full
% 2.45/1.01  --res_forward_subs_resolution           true
% 2.45/1.01  --res_backward_subs_resolution          true
% 2.45/1.01  --res_orphan_elimination                true
% 2.45/1.01  --res_time_limit                        2.
% 2.45/1.01  --res_out_proof                         true
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Options
% 2.45/1.01  
% 2.45/1.01  --superposition_flag                    true
% 2.45/1.01  --sup_passive_queue_type                priority_queues
% 2.45/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.45/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.45/1.01  --demod_completeness_check              fast
% 2.45/1.01  --demod_use_ground                      true
% 2.45/1.01  --sup_to_prop_solver                    passive
% 2.45/1.01  --sup_prop_simpl_new                    true
% 2.45/1.01  --sup_prop_simpl_given                  true
% 2.45/1.01  --sup_fun_splitting                     false
% 2.45/1.01  --sup_smt_interval                      50000
% 2.45/1.01  
% 2.45/1.01  ------ Superposition Simplification Setup
% 2.45/1.01  
% 2.45/1.01  --sup_indices_passive                   []
% 2.45/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.45/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.45/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_full_bw                           [BwDemod]
% 2.45/1.01  --sup_immed_triv                        [TrivRules]
% 2.45/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.45/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_immed_bw_main                     []
% 2.45/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.45/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.45/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.45/1.01  
% 2.45/1.01  ------ Combination Options
% 2.45/1.01  
% 2.45/1.01  --comb_res_mult                         3
% 2.45/1.01  --comb_sup_mult                         2
% 2.45/1.01  --comb_inst_mult                        10
% 2.45/1.01  
% 2.45/1.01  ------ Debug Options
% 2.45/1.01  
% 2.45/1.01  --dbg_backtrace                         false
% 2.45/1.01  --dbg_dump_prop_clauses                 false
% 2.45/1.01  --dbg_dump_prop_clauses_file            -
% 2.45/1.01  --dbg_out_stat                          false
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  ------ Proving...
% 2.45/1.01  
% 2.45/1.01  
% 2.45/1.01  % SZS status Theorem for theBenchmark.p
% 2.45/1.01  
% 2.45/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.45/1.01  
% 2.45/1.01  fof(f14,conjecture,(
% 2.45/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f15,negated_conjecture,(
% 2.45/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.45/1.01    inference(negated_conjecture,[],[f14])).
% 2.45/1.01  
% 2.45/1.01  fof(f31,plain,(
% 2.45/1.01    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.45/1.01    inference(ennf_transformation,[],[f15])).
% 2.45/1.01  
% 2.45/1.01  fof(f32,plain,(
% 2.45/1.01    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.45/1.01    inference(flattening,[],[f31])).
% 2.45/1.01  
% 2.45/1.01  fof(f38,plain,(
% 2.45/1.01    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.45/1.01    introduced(choice_axiom,[])).
% 2.45/1.01  
% 2.45/1.01  fof(f39,plain,(
% 2.45/1.01    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.45/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f38])).
% 2.45/1.01  
% 2.45/1.01  fof(f68,plain,(
% 2.45/1.01    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.45/1.01    inference(cnf_transformation,[],[f39])).
% 2.45/1.01  
% 2.45/1.01  fof(f11,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (r1_tarski(k6_relat_1(X1),X2) => (r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1)))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f25,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (((r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1) | ~r1_tarski(k6_relat_1(X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.45/1.01    inference(ennf_transformation,[],[f11])).
% 2.45/1.01  
% 2.45/1.01  fof(f26,plain,(
% 2.45/1.01    ! [X0,X1,X2] : ((r1_tarski(X1,k2_relset_1(X1,X0,X2)) & k1_relset_1(X1,X0,X2) = X1) | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 2.45/1.01    inference(flattening,[],[f25])).
% 2.45/1.01  
% 2.45/1.01  fof(f55,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X1,X0,X2) = X1 | ~r1_tarski(k6_relat_1(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 2.45/1.01    inference(cnf_transformation,[],[f26])).
% 2.45/1.01  
% 2.45/1.01  fof(f9,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f22,plain,(
% 2.45/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.01    inference(ennf_transformation,[],[f9])).
% 2.45/1.01  
% 2.45/1.01  fof(f53,plain,(
% 2.45/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.01    inference(cnf_transformation,[],[f22])).
% 2.45/1.01  
% 2.45/1.01  fof(f69,plain,(
% 2.45/1.01    r1_tarski(sK1,sK2)),
% 2.45/1.01    inference(cnf_transformation,[],[f39])).
% 2.45/1.01  
% 2.45/1.01  fof(f2,axiom,(
% 2.45/1.01    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f43,plain,(
% 2.45/1.01    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f2])).
% 2.45/1.01  
% 2.45/1.01  fof(f1,axiom,(
% 2.45/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.01  
% 2.45/1.01  fof(f33,plain,(
% 2.45/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.45/1.01    inference(nnf_transformation,[],[f1])).
% 2.45/1.01  
% 2.45/1.01  fof(f34,plain,(
% 2.45/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.45/1.01    inference(flattening,[],[f33])).
% 2.45/1.01  
% 2.45/1.01  fof(f42,plain,(
% 2.45/1.01    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.45/1.01    inference(cnf_transformation,[],[f34])).
% 2.45/1.01  
% 2.45/1.01  fof(f12,axiom,(
% 2.45/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.45/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f27,plain,(
% 2.45/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.02    inference(ennf_transformation,[],[f12])).
% 2.45/1.02  
% 2.45/1.02  fof(f28,plain,(
% 2.45/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.02    inference(flattening,[],[f27])).
% 2.45/1.02  
% 2.45/1.02  fof(f37,plain,(
% 2.45/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.02    inference(nnf_transformation,[],[f28])).
% 2.45/1.02  
% 2.45/1.02  fof(f61,plain,(
% 2.45/1.02    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.02    inference(cnf_transformation,[],[f37])).
% 2.45/1.02  
% 2.45/1.02  fof(f76,plain,(
% 2.45/1.02    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.45/1.02    inference(equality_resolution,[],[f61])).
% 2.45/1.02  
% 2.45/1.02  fof(f13,axiom,(
% 2.45/1.02    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f29,plain,(
% 2.45/1.02    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.45/1.02    inference(ennf_transformation,[],[f13])).
% 2.45/1.02  
% 2.45/1.02  fof(f30,plain,(
% 2.45/1.02    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.45/1.02    inference(flattening,[],[f29])).
% 2.45/1.02  
% 2.45/1.02  fof(f64,plain,(
% 2.45/1.02    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f30])).
% 2.45/1.02  
% 2.45/1.02  fof(f66,plain,(
% 2.45/1.02    v1_funct_1(sK3)),
% 2.45/1.02    inference(cnf_transformation,[],[f39])).
% 2.45/1.02  
% 2.45/1.02  fof(f65,plain,(
% 2.45/1.02    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f30])).
% 2.45/1.02  
% 2.45/1.02  fof(f7,axiom,(
% 2.45/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f20,plain,(
% 2.45/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.02    inference(ennf_transformation,[],[f7])).
% 2.45/1.02  
% 2.45/1.02  fof(f50,plain,(
% 2.45/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.02    inference(cnf_transformation,[],[f20])).
% 2.45/1.02  
% 2.45/1.02  fof(f8,axiom,(
% 2.45/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f21,plain,(
% 2.45/1.02    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.45/1.02    inference(ennf_transformation,[],[f8])).
% 2.45/1.02  
% 2.45/1.02  fof(f52,plain,(
% 2.45/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.02    inference(cnf_transformation,[],[f21])).
% 2.45/1.02  
% 2.45/1.02  fof(f51,plain,(
% 2.45/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.02    inference(cnf_transformation,[],[f21])).
% 2.45/1.02  
% 2.45/1.02  fof(f3,axiom,(
% 2.45/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f16,plain,(
% 2.45/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.45/1.02    inference(ennf_transformation,[],[f3])).
% 2.45/1.02  
% 2.45/1.02  fof(f35,plain,(
% 2.45/1.02    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.45/1.02    inference(nnf_transformation,[],[f16])).
% 2.45/1.02  
% 2.45/1.02  fof(f44,plain,(
% 2.45/1.02    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f35])).
% 2.45/1.02  
% 2.45/1.02  fof(f4,axiom,(
% 2.45/1.02    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f17,plain,(
% 2.45/1.02    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.45/1.02    inference(ennf_transformation,[],[f4])).
% 2.45/1.02  
% 2.45/1.02  fof(f36,plain,(
% 2.45/1.02    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.45/1.02    inference(nnf_transformation,[],[f17])).
% 2.45/1.02  
% 2.45/1.02  fof(f46,plain,(
% 2.45/1.02    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f36])).
% 2.45/1.02  
% 2.45/1.02  fof(f5,axiom,(
% 2.45/1.02    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 2.45/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.45/1.02  
% 2.45/1.02  fof(f18,plain,(
% 2.45/1.02    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | (~v5_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 2.45/1.02    inference(ennf_transformation,[],[f5])).
% 2.45/1.02  
% 2.45/1.02  fof(f19,plain,(
% 2.45/1.02    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 2.45/1.02    inference(flattening,[],[f18])).
% 2.45/1.02  
% 2.45/1.02  fof(f48,plain,(
% 2.45/1.02    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 2.45/1.02    inference(cnf_transformation,[],[f19])).
% 2.45/1.02  
% 2.45/1.02  fof(f67,plain,(
% 2.45/1.02    v1_funct_2(sK3,sK0,sK1)),
% 2.45/1.02    inference(cnf_transformation,[],[f39])).
% 2.45/1.02  
% 2.45/1.02  fof(f70,plain,(
% 2.45/1.02    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.45/1.02    inference(cnf_transformation,[],[f39])).
% 2.45/1.02  
% 2.45/1.02  fof(f40,plain,(
% 2.45/1.02    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.45/1.02    inference(cnf_transformation,[],[f34])).
% 2.45/1.02  
% 2.45/1.02  fof(f73,plain,(
% 2.45/1.02    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.45/1.02    inference(equality_resolution,[],[f40])).
% 2.45/1.02  
% 2.45/1.02  fof(f57,plain,(
% 2.45/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.45/1.02    inference(cnf_transformation,[],[f37])).
% 2.45/1.02  
% 2.45/1.02  fof(f71,plain,(
% 2.45/1.02    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 2.45/1.02    inference(cnf_transformation,[],[f39])).
% 2.45/1.02  
% 2.45/1.02  cnf(c_29,negated_conjecture,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.45/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1557,plain,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_16,plain,
% 2.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.02      | ~ r1_tarski(k6_relat_1(X1),X0)
% 2.45/1.02      | k1_relset_1(X1,X2,X0) = X1 ),
% 2.45/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1559,plain,
% 2.45/1.02      ( k1_relset_1(X0,X1,X2) = X0
% 2.45/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 2.45/1.02      | r1_tarski(k6_relat_1(X0),X2) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3126,plain,
% 2.45/1.02      ( k1_relset_1(sK0,sK1,sK3) = sK0
% 2.45/1.02      | r1_tarski(k6_relat_1(sK0),sK3) != iProver_top ),
% 2.45/1.02      inference(superposition,[status(thm)],[c_1557,c_1559]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_13,plain,
% 2.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1562,plain,
% 2.45/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.45/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2483,plain,
% 2.45/1.02      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.45/1.02      inference(superposition,[status(thm)],[c_1557,c_1562]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3133,plain,
% 2.45/1.02      ( k1_relat_1(sK3) = sK0
% 2.45/1.02      | r1_tarski(k6_relat_1(sK0),sK3) != iProver_top ),
% 2.45/1.02      inference(demodulation,[status(thm)],[c_3126,c_2483]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_34,plain,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_28,negated_conjecture,
% 2.45/1.02      ( r1_tarski(sK1,sK2) ),
% 2.45/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_35,plain,
% 2.45/1.02      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3,plain,
% 2.45/1.02      ( r1_tarski(k1_xboole_0,X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f43]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_95,plain,
% 2.45/1.02      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_0,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.45/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_100,plain,
% 2.45/1.02      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.45/1.02      | k1_xboole_0 = k1_xboole_0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_18,plain,
% 2.45/1.02      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.45/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.45/1.02      | k1_xboole_0 = X1
% 2.45/1.02      | k1_xboole_0 = X0 ),
% 2.45/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_24,plain,
% 2.45/1.02      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.45/1.02      | ~ v1_funct_1(X0)
% 2.45/1.02      | ~ v1_relat_1(X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_31,negated_conjecture,
% 2.45/1.02      ( v1_funct_1(sK3) ),
% 2.45/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_323,plain,
% 2.45/1.02      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.45/1.02      | ~ v1_relat_1(X0)
% 2.45/1.02      | sK3 != X0 ),
% 2.45/1.02      inference(resolution_lifted,[status(thm)],[c_24,c_31]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_324,plain,
% 2.45/1.02      ( v1_funct_2(sK3,k1_relat_1(sK3),X0)
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.45/1.02      | ~ v1_relat_1(sK3) ),
% 2.45/1.02      inference(unflattening,[status(thm)],[c_323]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_516,plain,
% 2.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(sK3),X2)
% 2.45/1.02      | ~ v1_relat_1(sK3)
% 2.45/1.02      | k1_relat_1(sK3) != X1
% 2.45/1.02      | sK3 != X0
% 2.45/1.02      | k1_xboole_0 != X2
% 2.45/1.02      | k1_xboole_0 = X0
% 2.45/1.02      | k1_xboole_0 = X1 ),
% 2.45/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_324]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_517,plain,
% 2.45/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 2.45/1.02      | ~ v1_relat_1(sK3)
% 2.45/1.02      | k1_xboole_0 = k1_relat_1(sK3)
% 2.45/1.02      | k1_xboole_0 = sK3 ),
% 2.45/1.02      inference(unflattening,[status(thm)],[c_516]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_23,plain,
% 2.45/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.45/1.02      | ~ v1_funct_1(X0)
% 2.45/1.02      | ~ v1_relat_1(X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_338,plain,
% 2.45/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(X0),X1)
% 2.45/1.02      | ~ v1_relat_1(X0)
% 2.45/1.02      | sK3 != X0 ),
% 2.45/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_31]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_339,plain,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0)))
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.45/1.02      | ~ v1_relat_1(sK3) ),
% 2.45/1.02      inference(unflattening,[status(thm)],[c_338]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_341,plain,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k1_xboole_0)))
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 2.45/1.02      | ~ v1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_339]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_519,plain,
% 2.45/1.02      ( ~ r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 2.45/1.02      | ~ v1_relat_1(sK3)
% 2.45/1.02      | k1_xboole_0 = k1_relat_1(sK3)
% 2.45/1.02      | k1_xboole_0 = sK3 ),
% 2.45/1.02      inference(global_propositional_subsumption,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_517,c_341]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_10,plain,
% 2.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.02      | v1_relat_1(X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1786,plain,
% 2.45/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.45/1.02      | v1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1787,plain,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.45/1.02      | v1_relat_1(sK3) = iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_1786]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_11,plain,
% 2.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.02      | v5_relat_1(X0,X2) ),
% 2.45/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1793,plain,
% 2.45/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.45/1.02      | v5_relat_1(sK3,sK1) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_11]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1794,plain,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.45/1.02      | v5_relat_1(sK3,sK1) = iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_1793]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_12,plain,
% 2.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.02      | v4_relat_1(X0,X1) ),
% 2.45/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_5,plain,
% 2.45/1.02      ( ~ v4_relat_1(X0,X1)
% 2.45/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 2.45/1.02      | ~ v1_relat_1(X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_361,plain,
% 2.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.02      | r1_tarski(k1_relat_1(X0),X1)
% 2.45/1.02      | ~ v1_relat_1(X0) ),
% 2.45/1.02      inference(resolution,[status(thm)],[c_12,c_5]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_365,plain,
% 2.45/1.02      ( r1_tarski(k1_relat_1(X0),X1)
% 2.45/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.45/1.02      inference(global_propositional_subsumption,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_361,c_10]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_366,plain,
% 2.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.02      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.45/1.02      inference(renaming,[status(thm)],[c_365]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1796,plain,
% 2.45/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.45/1.02      | r1_tarski(k1_relat_1(sK3),sK0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_366]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1110,plain,( X0 = X0 ),theory(equality) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1943,plain,
% 2.45/1.02      ( sK0 = sK0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1110]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_7,plain,
% 2.45/1.02      ( ~ v5_relat_1(X0,X1)
% 2.45/1.02      | r1_tarski(k2_relat_1(X0),X1)
% 2.45/1.02      | ~ v1_relat_1(X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f46]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1881,plain,
% 2.45/1.02      ( ~ v5_relat_1(sK3,X0)
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),X0)
% 2.45/1.02      | ~ v1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_7]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1999,plain,
% 2.45/1.02      ( ~ v5_relat_1(sK3,sK1)
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),sK1)
% 2.45/1.02      | ~ v1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1881]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_8,plain,
% 2.45/1.02      ( ~ v5_relat_1(X0,X1)
% 2.45/1.02      | v5_relat_1(X0,X2)
% 2.45/1.02      | ~ r1_tarski(X1,X2)
% 2.45/1.02      | ~ v1_relat_1(X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1880,plain,
% 2.45/1.02      ( ~ v5_relat_1(sK3,X0)
% 2.45/1.02      | v5_relat_1(sK3,X1)
% 2.45/1.02      | ~ r1_tarski(X0,X1)
% 2.45/1.02      | ~ v1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2056,plain,
% 2.45/1.02      ( v5_relat_1(sK3,X0)
% 2.45/1.02      | ~ v5_relat_1(sK3,sK1)
% 2.45/1.02      | ~ r1_tarski(sK1,X0)
% 2.45/1.02      | ~ v1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1880]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2058,plain,
% 2.45/1.02      ( ~ v5_relat_1(sK3,sK1)
% 2.45/1.02      | v5_relat_1(sK3,k1_xboole_0)
% 2.45/1.02      | ~ r1_tarski(sK1,k1_xboole_0)
% 2.45/1.02      | ~ v1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2056]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2075,plain,
% 2.45/1.02      ( k2_relat_1(sK3) = k2_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1110]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1111,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2100,plain,
% 2.45/1.02      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1111]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2101,plain,
% 2.45/1.02      ( sK1 != k1_xboole_0
% 2.45/1.02      | k1_xboole_0 = sK1
% 2.45/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2100]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_30,negated_conjecture,
% 2.45/1.02      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.45/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_500,plain,
% 2.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.45/1.02      | sK1 != k1_xboole_0
% 2.45/1.02      | sK0 != X1
% 2.45/1.02      | sK3 != X0
% 2.45/1.02      | k1_xboole_0 = X0
% 2.45/1.02      | k1_xboole_0 = X1 ),
% 2.45/1.02      inference(resolution_lifted,[status(thm)],[c_18,c_30]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_501,plain,
% 2.45/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 2.45/1.02      | sK1 != k1_xboole_0
% 2.45/1.02      | k1_xboole_0 = sK0
% 2.45/1.02      | k1_xboole_0 = sK3 ),
% 2.45/1.02      inference(unflattening,[status(thm)],[c_500]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1553,plain,
% 2.45/1.02      ( sK1 != k1_xboole_0
% 2.45/1.02      | k1_xboole_0 = sK0
% 2.45/1.02      | k1_xboole_0 = sK3
% 2.45/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_501]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_27,negated_conjecture,
% 2.45/1.02      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 2.45/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2165,plain,
% 2.45/1.02      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK0 ),
% 2.45/1.02      inference(global_propositional_subsumption,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_1553,c_27,c_95,c_100,c_2101]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1817,plain,
% 2.45/1.02      ( k1_relat_1(sK3) != X0
% 2.45/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 2.45/1.02      | k1_xboole_0 != X0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1111]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2185,plain,
% 2.45/1.02      ( k1_relat_1(sK3) != k1_relat_1(sK3)
% 2.45/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 2.45/1.02      | k1_xboole_0 != k1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1817]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2186,plain,
% 2.45/1.02      ( k1_relat_1(sK3) = k1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1110]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2188,plain,
% 2.45/1.02      ( k1_relat_1(sK3) != k1_relat_1(X0)
% 2.45/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 2.45/1.02      | k1_xboole_0 != k1_relat_1(X0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1817]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2190,plain,
% 2.45/1.02      ( k1_relat_1(sK3) != k1_relat_1(k1_xboole_0)
% 2.45/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 2.45/1.02      | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2188]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1113,plain,
% 2.45/1.02      ( X0 != X1 | k1_relat_1(X0) = k1_relat_1(X1) ),
% 2.45/1.02      theory(equality) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2189,plain,
% 2.45/1.02      ( k1_relat_1(sK3) = k1_relat_1(X0) | sK3 != X0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1113]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2191,plain,
% 2.45/1.02      ( k1_relat_1(sK3) = k1_relat_1(k1_xboole_0) | sK3 != k1_xboole_0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2189]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1112,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.45/1.02      theory(equality) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2277,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1)
% 2.45/1.02      | r1_tarski(sK1,k1_xboole_0)
% 2.45/1.02      | sK1 != X0
% 2.45/1.02      | k1_xboole_0 != X1 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1112]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2279,plain,
% 2.45/1.02      ( r1_tarski(sK1,k1_xboole_0)
% 2.45/1.02      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.45/1.02      | sK1 != k1_xboole_0
% 2.45/1.02      | k1_xboole_0 != k1_xboole_0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2277]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2345,plain,
% 2.45/1.02      ( ~ v5_relat_1(sK3,sK1)
% 2.45/1.02      | v5_relat_1(sK3,sK2)
% 2.45/1.02      | ~ r1_tarski(sK1,sK2)
% 2.45/1.02      | ~ v1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2056]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2346,plain,
% 2.45/1.02      ( v5_relat_1(sK3,sK1) != iProver_top
% 2.45/1.02      | v5_relat_1(sK3,sK2) = iProver_top
% 2.45/1.02      | r1_tarski(sK1,sK2) != iProver_top
% 2.45/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_2345]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2367,plain,
% 2.45/1.02      ( ~ v5_relat_1(sK3,sK2)
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),sK2)
% 2.45/1.02      | ~ v1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1881]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2368,plain,
% 2.45/1.02      ( v5_relat_1(sK3,sK2) != iProver_top
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.45/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_2367]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2383,plain,
% 2.45/1.02      ( r1_tarski(k1_xboole_0,k1_relat_1(X0)) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_3]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2387,plain,
% 2.45/1.02      ( r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2383]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1566,plain,
% 2.45/1.02      ( v5_relat_1(X0,X1) != iProver_top
% 2.45/1.02      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 2.45/1.02      | v1_relat_1(X0) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1552,plain,
% 2.45/1.02      ( k1_xboole_0 = k1_relat_1(sK3)
% 2.45/1.02      | k1_xboole_0 = sK3
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.45/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_521,plain,
% 2.45/1.02      ( k1_xboole_0 = k1_relat_1(sK3)
% 2.45/1.02      | k1_xboole_0 = sK3
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.45/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_519]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2270,plain,
% 2.45/1.02      ( r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top
% 2.45/1.02      | k1_xboole_0 = sK3
% 2.45/1.02      | k1_xboole_0 = k1_relat_1(sK3) ),
% 2.45/1.02      inference(global_propositional_subsumption,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_1552,c_34,c_521,c_1787]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2271,plain,
% 2.45/1.02      ( k1_xboole_0 = k1_relat_1(sK3)
% 2.45/1.02      | k1_xboole_0 = sK3
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),k1_xboole_0) != iProver_top ),
% 2.45/1.02      inference(renaming,[status(thm)],[c_2270]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2561,plain,
% 2.45/1.02      ( k1_relat_1(sK3) = k1_xboole_0
% 2.45/1.02      | sK3 = k1_xboole_0
% 2.45/1.02      | v5_relat_1(sK3,k1_xboole_0) != iProver_top
% 2.45/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.45/1.02      inference(superposition,[status(thm)],[c_1566,c_2271]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2590,plain,
% 2.45/1.02      ( ~ v5_relat_1(sK3,k1_xboole_0)
% 2.45/1.02      | ~ v1_relat_1(sK3)
% 2.45/1.02      | k1_relat_1(sK3) = k1_xboole_0
% 2.45/1.02      | sK3 = k1_xboole_0 ),
% 2.45/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2561]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1555,plain,
% 2.45/1.02      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.45/1.02      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_366]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2411,plain,
% 2.45/1.02      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 2.45/1.02      inference(superposition,[status(thm)],[c_1557,c_1555]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1570,plain,
% 2.45/1.02      ( X0 = X1
% 2.45/1.02      | r1_tarski(X0,X1) != iProver_top
% 2.45/1.02      | r1_tarski(X1,X0) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2692,plain,
% 2.45/1.02      ( k1_relat_1(sK3) = sK0
% 2.45/1.02      | r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top ),
% 2.45/1.02      inference(superposition,[status(thm)],[c_2411,c_1570]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2693,plain,
% 2.45/1.02      ( ~ r1_tarski(sK0,k1_relat_1(sK3)) | k1_relat_1(sK3) = sK0 ),
% 2.45/1.02      inference(predicate_to_equality_rev,[status(thm)],[c_2692]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1909,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1)
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),X2)
% 2.45/1.02      | X2 != X1
% 2.45/1.02      | k2_relat_1(sK3) != X0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1112]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2074,plain,
% 2.45/1.02      ( ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),X1)
% 2.45/1.02      | X1 != X0
% 2.45/1.02      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1909]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2732,plain,
% 2.45/1.02      ( r1_tarski(k2_relat_1(sK3),X0)
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(sK3),sK1)
% 2.45/1.02      | X0 != sK1
% 2.45/1.02      | k2_relat_1(sK3) != k2_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2074]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2734,plain,
% 2.45/1.02      ( ~ r1_tarski(k2_relat_1(sK3),sK1)
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),k1_xboole_0)
% 2.45/1.02      | k2_relat_1(sK3) != k2_relat_1(sK3)
% 2.45/1.02      | k1_xboole_0 != sK1 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2732]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2339,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1)
% 2.45/1.02      | r1_tarski(sK0,k1_relat_1(sK3))
% 2.45/1.02      | k1_relat_1(sK3) != X1
% 2.45/1.02      | sK0 != X0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1112]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2753,plain,
% 2.45/1.02      ( ~ r1_tarski(sK0,X0)
% 2.45/1.02      | r1_tarski(sK0,k1_relat_1(sK3))
% 2.45/1.02      | k1_relat_1(sK3) != X0
% 2.45/1.02      | sK0 != sK0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2339]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2755,plain,
% 2.45/1.02      ( r1_tarski(sK0,k1_relat_1(sK3))
% 2.45/1.02      | ~ r1_tarski(sK0,k1_xboole_0)
% 2.45/1.02      | k1_relat_1(sK3) != k1_xboole_0
% 2.45/1.02      | sK0 != sK0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2753]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1934,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1)
% 2.45/1.02      | r1_tarski(sK0,k1_xboole_0)
% 2.45/1.02      | sK0 != X0
% 2.45/1.02      | k1_xboole_0 != X1 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1112]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2147,plain,
% 2.45/1.02      ( ~ r1_tarski(sK0,X0)
% 2.45/1.02      | r1_tarski(sK0,k1_xboole_0)
% 2.45/1.02      | sK0 != sK0
% 2.45/1.02      | k1_xboole_0 != X0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1934]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2868,plain,
% 2.45/1.02      ( ~ r1_tarski(sK0,sK0)
% 2.45/1.02      | r1_tarski(sK0,k1_xboole_0)
% 2.45/1.02      | sK0 != sK0
% 2.45/1.02      | k1_xboole_0 != sK0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2147]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2,plain,
% 2.45/1.02      ( r1_tarski(X0,X0) ),
% 2.45/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2869,plain,
% 2.45/1.02      ( r1_tarski(sK0,sK0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_22,plain,
% 2.45/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.45/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.45/1.02      | k1_xboole_0 = X2 ),
% 2.45/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_605,plain,
% 2.45/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.45/1.02      | k1_relset_1(X1,X2,X0) = X1
% 2.45/1.02      | sK1 != X2
% 2.45/1.02      | sK0 != X1
% 2.45/1.02      | sK3 != X0
% 2.45/1.02      | k1_xboole_0 = X2 ),
% 2.45/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_30]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_606,plain,
% 2.45/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.45/1.02      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.45/1.02      | k1_xboole_0 = sK1 ),
% 2.45/1.02      inference(unflattening,[status(thm)],[c_605]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_608,plain,
% 2.45/1.02      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.45/1.02      inference(global_propositional_subsumption,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_606,c_29]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2809,plain,
% 2.45/1.02      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.45/1.02      inference(superposition,[status(thm)],[c_608,c_2483]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_26,negated_conjecture,
% 2.45/1.02      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.45/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.45/1.02      | ~ v1_funct_1(sK3) ),
% 2.45/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_167,plain,
% 2.45/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.45/1.02      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 2.45/1.02      inference(global_propositional_subsumption,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_26,c_31]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_168,negated_conjecture,
% 2.45/1.02      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.45/1.02      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.45/1.02      inference(renaming,[status(thm)],[c_167]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_655,plain,
% 2.45/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(sK3),X0)
% 2.45/1.02      | ~ v1_relat_1(sK3)
% 2.45/1.02      | k1_relat_1(sK3) != sK0
% 2.45/1.02      | sK2 != X0
% 2.45/1.02      | sK3 != sK3 ),
% 2.45/1.02      inference(resolution_lifted,[status(thm)],[c_168,c_324]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_656,plain,
% 2.45/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.45/1.02      | ~ v1_relat_1(sK3)
% 2.45/1.02      | k1_relat_1(sK3) != sK0 ),
% 2.45/1.02      inference(unflattening,[status(thm)],[c_655]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_666,plain,
% 2.45/1.02      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.45/1.02      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.45/1.02      | k1_relat_1(sK3) != sK0 ),
% 2.45/1.02      inference(forward_subsumption_resolution,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_656,c_10]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1546,plain,
% 2.45/1.02      ( k1_relat_1(sK3) != sK0
% 2.45/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2909,plain,
% 2.45/1.02      ( sK1 = k1_xboole_0
% 2.45/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.45/1.02      inference(superposition,[status(thm)],[c_2809,c_1546]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1556,plain,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 2.45/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_340,plain,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 2.45/1.02      | v1_relat_1(sK3) != iProver_top ),
% 2.45/1.02      inference(predicate_to_equality,[status(thm)],[c_339]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1867,plain,
% 2.45/1.02      ( r1_tarski(k2_relat_1(sK3),X0) != iProver_top
% 2.45/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top ),
% 2.45/1.02      inference(global_propositional_subsumption,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_1556,c_34,c_340,c_1787]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1868,plain,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),X0))) = iProver_top
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 2.45/1.02      inference(renaming,[status(thm)],[c_1867]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2910,plain,
% 2.45/1.02      ( sK1 = k1_xboole_0
% 2.45/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 2.45/1.02      inference(superposition,[status(thm)],[c_2809,c_1868]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2920,plain,
% 2.45/1.02      ( sK1 = k1_xboole_0
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.45/1.02      inference(forward_subsumption_resolution,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_2909,c_2910]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_1833,plain,
% 2.45/1.02      ( ~ r1_tarski(X0,X1)
% 2.45/1.02      | r1_tarski(k1_relat_1(X2),X3)
% 2.45/1.02      | X3 != X1
% 2.45/1.02      | k1_relat_1(X2) != X0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1112]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2232,plain,
% 2.45/1.02      ( ~ r1_tarski(k1_relat_1(X0),X1)
% 2.45/1.02      | r1_tarski(k1_relat_1(X2),X3)
% 2.45/1.02      | X3 != X1
% 2.45/1.02      | k1_relat_1(X2) != k1_relat_1(X0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1833]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2960,plain,
% 2.45/1.02      ( r1_tarski(k1_relat_1(X0),X1)
% 2.45/1.02      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 2.45/1.02      | X1 != sK0
% 2.45/1.02      | k1_relat_1(X0) != k1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2232]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_2962,plain,
% 2.45/1.02      ( ~ r1_tarski(k1_relat_1(sK3),sK0)
% 2.45/1.02      | r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 2.45/1.02      | k1_relat_1(k1_xboole_0) != k1_relat_1(sK3)
% 2.45/1.02      | k1_xboole_0 != sK0 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_2960]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3026,plain,
% 2.45/1.02      ( ~ r1_tarski(k1_relat_1(X0),k1_xboole_0)
% 2.45/1.02      | ~ r1_tarski(k1_xboole_0,k1_relat_1(X0))
% 2.45/1.02      | k1_xboole_0 = k1_relat_1(X0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3028,plain,
% 2.45/1.02      ( ~ r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
% 2.45/1.02      | ~ r1_tarski(k1_xboole_0,k1_relat_1(k1_xboole_0))
% 2.45/1.02      | k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_3026]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3266,plain,
% 2.45/1.02      ( X0 != sK3 | k1_relat_1(X0) = k1_relat_1(sK3) ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_1113]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3267,plain,
% 2.45/1.02      ( k1_relat_1(k1_xboole_0) = k1_relat_1(sK3) | k1_xboole_0 != sK3 ),
% 2.45/1.02      inference(instantiation,[status(thm)],[c_3266]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3356,plain,
% 2.45/1.02      ( k1_relat_1(sK3) = sK0 ),
% 2.45/1.02      inference(global_propositional_subsumption,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_3133,c_29,c_34,c_35,c_95,c_100,c_519,c_1786,c_1787,
% 2.45/1.02                 c_1793,c_1794,c_1796,c_1942,c_1943,c_1999,c_2058,c_2075,
% 2.45/1.02                 c_2101,c_2165,c_2185,c_2186,c_2190,c_2191,c_2279,c_2341,
% 2.45/1.02                 c_2346,c_2368,c_2387,c_2590,c_2693,c_2734,c_2920,c_2962,
% 2.45/1.02                 c_3028,c_3267]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3367,plain,
% 2.45/1.02      ( sK0 != sK0
% 2.45/1.02      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.45/1.02      inference(demodulation,[status(thm)],[c_3356,c_1546]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3373,plain,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.45/1.02      inference(equality_resolution_simp,[status(thm)],[c_3367]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3368,plain,
% 2.45/1.02      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0))) = iProver_top
% 2.45/1.02      | r1_tarski(k2_relat_1(sK3),X0) != iProver_top ),
% 2.45/1.02      inference(demodulation,[status(thm)],[c_3356,c_1868]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(c_3376,plain,
% 2.45/1.02      ( r1_tarski(k2_relat_1(sK3),sK2) != iProver_top ),
% 2.45/1.02      inference(forward_subsumption_resolution,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_3373,c_3368]) ).
% 2.45/1.02  
% 2.45/1.02  cnf(contradiction,plain,
% 2.45/1.02      ( $false ),
% 2.45/1.02      inference(minisat,
% 2.45/1.02                [status(thm)],
% 2.45/1.02                [c_3376,c_2368,c_2346,c_1794,c_1787,c_35,c_34]) ).
% 2.45/1.02  
% 2.45/1.02  
% 2.45/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.45/1.02  
% 2.45/1.02  ------                               Statistics
% 2.45/1.02  
% 2.45/1.02  ------ General
% 2.45/1.02  
% 2.45/1.02  abstr_ref_over_cycles:                  0
% 2.45/1.02  abstr_ref_under_cycles:                 0
% 2.45/1.02  gc_basic_clause_elim:                   0
% 2.45/1.02  forced_gc_time:                         0
% 2.45/1.02  parsing_time:                           0.013
% 2.45/1.02  unif_index_cands_time:                  0.
% 2.45/1.02  unif_index_add_time:                    0.
% 2.45/1.02  orderings_time:                         0.
% 2.45/1.02  out_proof_time:                         0.012
% 2.45/1.02  total_time:                             0.13
% 2.45/1.02  num_of_symbols:                         50
% 2.45/1.02  num_of_terms:                           1916
% 2.45/1.02  
% 2.45/1.02  ------ Preprocessing
% 2.45/1.02  
% 2.45/1.02  num_of_splits:                          0
% 2.45/1.02  num_of_split_atoms:                     0
% 2.45/1.02  num_of_reused_defs:                     0
% 2.45/1.02  num_eq_ax_congr_red:                    22
% 2.45/1.02  num_of_sem_filtered_clauses:            1
% 2.45/1.02  num_of_subtypes:                        0
% 2.45/1.02  monotx_restored_types:                  0
% 2.45/1.02  sat_num_of_epr_types:                   0
% 2.45/1.02  sat_num_of_non_cyclic_types:            0
% 2.45/1.02  sat_guarded_non_collapsed_types:        0
% 2.45/1.02  num_pure_diseq_elim:                    0
% 2.45/1.02  simp_replaced_by:                       0
% 2.45/1.02  res_preprocessed:                       140
% 2.45/1.02  prep_upred:                             0
% 2.45/1.02  prep_unflattend:                        52
% 2.45/1.02  smt_new_axioms:                         0
% 2.45/1.02  pred_elim_cands:                        4
% 2.45/1.02  pred_elim:                              3
% 2.45/1.02  pred_elim_cl:                           1
% 2.45/1.02  pred_elim_cycles:                       6
% 2.45/1.02  merged_defs:                            0
% 2.45/1.02  merged_defs_ncl:                        0
% 2.45/1.02  bin_hyper_res:                          0
% 2.45/1.02  prep_cycles:                            4
% 2.45/1.02  pred_elim_time:                         0.011
% 2.45/1.02  splitting_time:                         0.
% 2.45/1.02  sem_filter_time:                        0.
% 2.45/1.02  monotx_time:                            0.001
% 2.45/1.02  subtype_inf_time:                       0.
% 2.45/1.02  
% 2.45/1.02  ------ Problem properties
% 2.45/1.02  
% 2.45/1.02  clauses:                                29
% 2.45/1.02  conjectures:                            3
% 2.45/1.02  epr:                                    6
% 2.45/1.02  horn:                                   25
% 2.45/1.02  ground:                                 13
% 2.45/1.02  unary:                                  5
% 2.45/1.02  binary:                                 7
% 2.45/1.02  lits:                                   78
% 2.45/1.02  lits_eq:                                28
% 2.45/1.02  fd_pure:                                0
% 2.45/1.02  fd_pseudo:                              0
% 2.45/1.02  fd_cond:                                1
% 2.45/1.02  fd_pseudo_cond:                         1
% 2.45/1.02  ac_symbols:                             0
% 2.45/1.02  
% 2.45/1.02  ------ Propositional Solver
% 2.45/1.02  
% 2.45/1.02  prop_solver_calls:                      27
% 2.45/1.02  prop_fast_solver_calls:                 982
% 2.45/1.02  smt_solver_calls:                       0
% 2.45/1.02  smt_fast_solver_calls:                  0
% 2.45/1.02  prop_num_of_clauses:                    943
% 2.45/1.02  prop_preprocess_simplified:             4449
% 2.45/1.02  prop_fo_subsumed:                       12
% 2.45/1.02  prop_solver_time:                       0.
% 2.45/1.02  smt_solver_time:                        0.
% 2.45/1.02  smt_fast_solver_time:                   0.
% 2.45/1.02  prop_fast_solver_time:                  0.
% 2.45/1.02  prop_unsat_core_time:                   0.
% 2.45/1.02  
% 2.45/1.02  ------ QBF
% 2.45/1.02  
% 2.45/1.02  qbf_q_res:                              0
% 2.45/1.02  qbf_num_tautologies:                    0
% 2.45/1.02  qbf_prep_cycles:                        0
% 2.45/1.02  
% 2.45/1.02  ------ BMC1
% 2.45/1.02  
% 2.45/1.02  bmc1_current_bound:                     -1
% 2.45/1.02  bmc1_last_solved_bound:                 -1
% 2.45/1.02  bmc1_unsat_core_size:                   -1
% 2.45/1.02  bmc1_unsat_core_parents_size:           -1
% 2.45/1.02  bmc1_merge_next_fun:                    0
% 2.45/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.45/1.02  
% 2.45/1.02  ------ Instantiation
% 2.45/1.02  
% 2.45/1.02  inst_num_of_clauses:                    294
% 2.45/1.02  inst_num_in_passive:                    110
% 2.45/1.02  inst_num_in_active:                     162
% 2.45/1.02  inst_num_in_unprocessed:                22
% 2.45/1.02  inst_num_of_loops:                      210
% 2.45/1.02  inst_num_of_learning_restarts:          0
% 2.45/1.02  inst_num_moves_active_passive:          45
% 2.45/1.02  inst_lit_activity:                      0
% 2.45/1.02  inst_lit_activity_moves:                0
% 2.45/1.02  inst_num_tautologies:                   0
% 2.45/1.02  inst_num_prop_implied:                  0
% 2.45/1.02  inst_num_existing_simplified:           0
% 2.45/1.02  inst_num_eq_res_simplified:             0
% 2.45/1.02  inst_num_child_elim:                    0
% 2.45/1.02  inst_num_of_dismatching_blockings:      44
% 2.45/1.02  inst_num_of_non_proper_insts:           286
% 2.45/1.02  inst_num_of_duplicates:                 0
% 2.45/1.02  inst_inst_num_from_inst_to_res:         0
% 2.45/1.02  inst_dismatching_checking_time:         0.
% 2.45/1.02  
% 2.45/1.02  ------ Resolution
% 2.45/1.02  
% 2.45/1.02  res_num_of_clauses:                     0
% 2.45/1.02  res_num_in_passive:                     0
% 2.45/1.02  res_num_in_active:                      0
% 2.45/1.02  res_num_of_loops:                       144
% 2.45/1.02  res_forward_subset_subsumed:            35
% 2.45/1.02  res_backward_subset_subsumed:           0
% 2.45/1.02  res_forward_subsumed:                   0
% 2.45/1.02  res_backward_subsumed:                  0
% 2.45/1.02  res_forward_subsumption_resolution:     2
% 2.45/1.02  res_backward_subsumption_resolution:    0
% 2.45/1.02  res_clause_to_clause_subsumption:       218
% 2.45/1.02  res_orphan_elimination:                 0
% 2.45/1.02  res_tautology_del:                      29
% 2.45/1.02  res_num_eq_res_simplified:              1
% 2.45/1.02  res_num_sel_changes:                    0
% 2.45/1.02  res_moves_from_active_to_pass:          0
% 2.45/1.02  
% 2.45/1.02  ------ Superposition
% 2.45/1.02  
% 2.45/1.02  sup_time_total:                         0.
% 2.45/1.02  sup_time_generating:                    0.
% 2.45/1.02  sup_time_sim_full:                      0.
% 2.45/1.02  sup_time_sim_immed:                     0.
% 2.45/1.02  
% 2.45/1.02  sup_num_of_clauses:                     55
% 2.45/1.02  sup_num_in_active:                      28
% 2.45/1.02  sup_num_in_passive:                     27
% 2.45/1.02  sup_num_of_loops:                       41
% 2.45/1.02  sup_fw_superposition:                   27
% 2.45/1.02  sup_bw_superposition:                   18
% 2.45/1.02  sup_immediate_simplified:               13
% 2.45/1.02  sup_given_eliminated:                   0
% 2.45/1.02  comparisons_done:                       0
% 2.45/1.02  comparisons_avoided:                    4
% 2.45/1.02  
% 2.45/1.02  ------ Simplifications
% 2.45/1.02  
% 2.45/1.02  
% 2.45/1.02  sim_fw_subset_subsumed:                 3
% 2.45/1.02  sim_bw_subset_subsumed:                 3
% 2.45/1.02  sim_fw_subsumed:                        5
% 2.45/1.02  sim_bw_subsumed:                        2
% 2.45/1.02  sim_fw_subsumption_res:                 2
% 2.45/1.02  sim_bw_subsumption_res:                 0
% 2.45/1.02  sim_tautology_del:                      3
% 2.45/1.02  sim_eq_tautology_del:                   1
% 2.45/1.02  sim_eq_res_simp:                        1
% 2.45/1.02  sim_fw_demodulated:                     1
% 2.45/1.02  sim_bw_demodulated:                     10
% 2.45/1.02  sim_light_normalised:                   0
% 2.45/1.02  sim_joinable_taut:                      0
% 2.45/1.02  sim_joinable_simp:                      0
% 2.45/1.02  sim_ac_normalised:                      0
% 2.45/1.02  sim_smt_subsumption:                    0
% 2.45/1.02  
%------------------------------------------------------------------------------
