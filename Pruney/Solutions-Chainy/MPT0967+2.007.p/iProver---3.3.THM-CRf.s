%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:38 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : ERROR: Analysing output (Could not find formula named c_536)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f30,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,conjecture,(
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

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f31,plain,
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

fof(f32,plain,
    ( ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
      | ~ v1_funct_2(sK3,sK0,sK2)
      | ~ v1_funct_1(sK3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f31])).

fof(f54,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( ( v5_relat_1(X2,X0)
            & v1_relat_1(X2) )
         => v5_relat_1(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X1)
          | ~ v5_relat_1(X2,X0)
          | ~ v1_relat_1(X2) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ v5_relat_1(X2,X0)
      | ~ v1_relat_1(X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r1_tarski(k2_relat_1(X2),X1)
      | ~ r1_tarski(k1_relat_1(X2),X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | k1_relset_1(X0,X1,X2) != X0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f58,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2)
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f57,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f32])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f48])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f51])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_460,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK1 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_24])).

cnf(c_461,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(unflattening,[status(thm)],[c_460])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_463,plain,
    ( k1_relset_1(sK0,sK1,sK3) = sK0
    | k1_xboole_0 = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_461,c_23])).

cnf(c_1037,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1040,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1756,plain,
    ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1037,c_1040])).

cnf(c_1758,plain,
    ( k1_relat_1(sK3) = sK0
    | sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_463,c_1756])).

cnf(c_22,negated_conjecture,
    ( r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1038,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1041,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v5_relat_1(X0,X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1500,plain,
    ( v5_relat_1(sK3,sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1041])).

cnf(c_8,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X0,X2)
    | ~ r1_tarski(X1,X2)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1043,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2070,plain,
    ( v5_relat_1(sK3,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1500,c_1043])).

cnf(c_28,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1201,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1202,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1201])).

cnf(c_2324,plain,
    ( r1_tarski(sK1,X0) != iProver_top
    | v5_relat_1(sK3,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2070,c_28,c_1202])).

cnf(c_2325,plain,
    ( v5_relat_1(sK3,X0) = iProver_top
    | r1_tarski(sK1,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2324])).

cnf(c_2333,plain,
    ( v5_relat_1(sK3,sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1038,c_2325])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v4_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_5,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_274,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_11,c_5])).

cnf(c_278,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_274,c_9])).

cnf(c_279,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_278])).

cnf(c_1036,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_279])).

cnf(c_1657,plain,
    ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1037,c_1036])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1044,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(k2_relat_1(X0),X2)
    | ~ r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1039,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X2) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1811,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(k2_relat_1(X2),X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1039,c_1040])).

cnf(c_2578,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | v5_relat_1(X2,X1) != iProver_top
    | r1_tarski(k1_relat_1(X2),X0) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1044,c_1811])).

cnf(c_2783,plain,
    ( k1_relset_1(sK0,X0,sK3) = k1_relat_1(sK3)
    | v5_relat_1(sK3,X0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_2578])).

cnf(c_2870,plain,
    ( v5_relat_1(sK3,X0) != iProver_top
    | k1_relset_1(sK0,X0,sK3) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2783,c_28,c_1202])).

cnf(c_2871,plain,
    ( k1_relset_1(sK0,X0,sK3) = k1_relat_1(sK3)
    | v5_relat_1(sK3,X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2870])).

cnf(c_2879,plain,
    ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_2333,c_2871])).

cnf(c_17,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) != X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_20,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_140,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ v1_funct_2(sK3,sK0,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_20,c_25])).

cnf(c_141,negated_conjecture,
    ( ~ v1_funct_2(sK3,sK0,sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    inference(renaming,[status(thm)],[c_140])).

cnf(c_447,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(X1,X2,X0) != X1
    | sK2 != X2
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_141])).

cnf(c_448,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_447])).

cnf(c_1031,plain,
    ( k1_relset_1(sK0,sK2,sK3) != sK0
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_448])).

cnf(c_2884,plain,
    ( k1_relat_1(sK3) != sK0
    | sK2 = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2879,c_1031])).

cnf(c_29,plain,
    ( r1_tarski(sK1,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_471,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | sK1 != sK2
    | sK0 != sK0
    | sK3 != sK3 ),
    inference(resolution_lifted,[status(thm)],[c_141,c_24])).

cnf(c_1204,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | v5_relat_1(sK3,sK1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_1205,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v5_relat_1(sK3,sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1204])).

cnf(c_1207,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | r1_tarski(k1_relat_1(sK3),sK0) ),
    inference(instantiation,[status(thm)],[c_279])).

cnf(c_1208,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1207])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1213,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_714,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1263,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_1279,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_1292,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_714])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1452,plain,
    ( r1_tarski(k1_xboole_0,sK1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_716,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1281,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK2,sK1)
    | sK1 != X1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_1467,plain,
    ( ~ r1_tarski(X0,sK1)
    | r1_tarski(sK2,sK1)
    | sK1 != sK1
    | sK2 != X0 ),
    inference(instantiation,[status(thm)],[c_1281])).

cnf(c_1469,plain,
    ( r1_tarski(sK2,sK1)
    | ~ r1_tarski(k1_xboole_0,sK1)
    | sK1 != sK1
    | sK2 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1467])).

cnf(c_1232,plain,
    ( ~ v5_relat_1(sK3,X0)
    | v5_relat_1(sK3,X1)
    | ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1360,plain,
    ( v5_relat_1(sK3,X0)
    | ~ v5_relat_1(sK3,sK1)
    | ~ r1_tarski(sK1,X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1232])).

cnf(c_1505,plain,
    ( ~ v5_relat_1(sK3,sK1)
    | v5_relat_1(sK3,sK2)
    | ~ r1_tarski(sK1,sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1360])).

cnf(c_1506,plain,
    ( v5_relat_1(sK3,sK1) != iProver_top
    | v5_relat_1(sK3,sK2) = iProver_top
    | r1_tarski(sK1,sK2) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1505])).

cnf(c_1233,plain,
    ( ~ v5_relat_1(sK3,X0)
    | r1_tarski(k2_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1617,plain,
    ( ~ v5_relat_1(sK3,sK2)
    | r1_tarski(k2_relat_1(sK3),sK2)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1233])).

cnf(c_1618,plain,
    ( v5_relat_1(sK3,sK2) != iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1617])).

cnf(c_1231,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(k2_relat_1(sK3),X1)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2126,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),X0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1231])).

cnf(c_2433,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ r1_tarski(k2_relat_1(sK3),sK2)
    | ~ r1_tarski(k1_relat_1(sK3),sK0)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2126])).

cnf(c_2434,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
    | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2433])).

cnf(c_2969,plain,
    ( k1_relat_1(sK3) != sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2884,c_23,c_28,c_22,c_29,c_536,c_1201,c_1202,c_1204,c_1205,c_1207,c_1208,c_1213,c_1292,c_1452,c_1469,c_1505,c_1506,c_1617,c_1618,c_2433,c_2434])).

cnf(c_2972,plain,
    ( sK1 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1758,c_2969])).

cnf(c_3134,plain,
    ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_2972,c_1756])).

cnf(c_21,negated_conjecture,
    ( k1_xboole_0 != sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_3142,plain,
    ( sK0 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2972,c_21])).

cnf(c_3143,plain,
    ( sK0 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_3142])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_434,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | sK1 != X1
    | sK0 != k1_xboole_0
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_24])).

cnf(c_435,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_434])).

cnf(c_1032,plain,
    ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_435])).

cnf(c_3138,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | sK0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2972,c_1032])).

cnf(c_3150,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3138,c_3143])).

cnf(c_3151,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3150])).

cnf(c_3140,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2972,c_1037])).

cnf(c_3147,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3140,c_3143])).

cnf(c_3154,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3151,c_3147])).

cnf(c_3164,plain,
    ( k1_relat_1(sK3) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_3134,c_3143,c_3154])).

cnf(c_1048,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1938,plain,
    ( k1_relat_1(sK3) = sK0
    | r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1657,c_1048])).

cnf(c_1953,plain,
    ( ~ r1_tarski(sK0,k1_relat_1(sK3))
    | k1_relat_1(sK3) = sK0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1938])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_398,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | sK0 != X1
    | sK3 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_24])).

cnf(c_399,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_1034,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK3
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_78,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_83,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_715,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1381,plain,
    ( sK1 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK1 ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_1382,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1381])).

cnf(c_1561,plain,
    ( sK1 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1034,c_21,c_78,c_83,c_1382])).

cnf(c_1492,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK0,k1_relat_1(sK3))
    | k1_relat_1(sK3) != X1
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_716])).

cnf(c_1494,plain,
    ( r1_tarski(sK0,k1_relat_1(sK3))
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_relat_1(sK3) != k1_xboole_0
    | sK0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1492])).

cnf(c_1220,plain,
    ( sK0 != X0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_715])).

cnf(c_1278,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_1220])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3164,c_2884,c_2434,c_2433,c_1953,c_1758,c_1618,c_1617,c_1561,c_1506,c_1505,c_1494,c_1469,c_1452,c_1292,c_1279,c_1278,c_1263,c_1213,c_1208,c_1207,c_1205,c_1204,c_1202,c_1201,c_471,c_78,c_29,c_22,c_28,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:36:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.24/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.00  
% 2.24/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.24/1.00  
% 2.24/1.00  ------  iProver source info
% 2.24/1.00  
% 2.24/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.24/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.24/1.00  git: non_committed_changes: false
% 2.24/1.00  git: last_make_outside_of_git: false
% 2.24/1.00  
% 2.24/1.00  ------ 
% 2.24/1.00  
% 2.24/1.00  ------ Input Options
% 2.24/1.00  
% 2.24/1.00  --out_options                           all
% 2.24/1.00  --tptp_safe_out                         true
% 2.24/1.00  --problem_path                          ""
% 2.24/1.00  --include_path                          ""
% 2.24/1.00  --clausifier                            res/vclausify_rel
% 2.24/1.00  --clausifier_options                    --mode clausify
% 2.24/1.00  --stdin                                 false
% 2.24/1.00  --stats_out                             all
% 2.24/1.00  
% 2.24/1.00  ------ General Options
% 2.24/1.00  
% 2.24/1.00  --fof                                   false
% 2.24/1.00  --time_out_real                         305.
% 2.24/1.00  --time_out_virtual                      -1.
% 2.24/1.00  --symbol_type_check                     false
% 2.24/1.00  --clausify_out                          false
% 2.24/1.00  --sig_cnt_out                           false
% 2.24/1.00  --trig_cnt_out                          false
% 2.24/1.00  --trig_cnt_out_tolerance                1.
% 2.24/1.00  --trig_cnt_out_sk_spl                   false
% 2.24/1.00  --abstr_cl_out                          false
% 2.24/1.00  
% 2.24/1.00  ------ Global Options
% 2.24/1.00  
% 2.24/1.00  --schedule                              default
% 2.24/1.00  --add_important_lit                     false
% 2.24/1.00  --prop_solver_per_cl                    1000
% 2.24/1.00  --min_unsat_core                        false
% 2.24/1.00  --soft_assumptions                      false
% 2.24/1.00  --soft_lemma_size                       3
% 2.24/1.00  --prop_impl_unit_size                   0
% 2.24/1.00  --prop_impl_unit                        []
% 2.24/1.00  --share_sel_clauses                     true
% 2.24/1.00  --reset_solvers                         false
% 2.24/1.00  --bc_imp_inh                            [conj_cone]
% 2.24/1.00  --conj_cone_tolerance                   3.
% 2.24/1.00  --extra_neg_conj                        none
% 2.24/1.00  --large_theory_mode                     true
% 2.24/1.00  --prolific_symb_bound                   200
% 2.24/1.00  --lt_threshold                          2000
% 2.24/1.00  --clause_weak_htbl                      true
% 2.24/1.00  --gc_record_bc_elim                     false
% 2.24/1.00  
% 2.24/1.00  ------ Preprocessing Options
% 2.24/1.00  
% 2.24/1.00  --preprocessing_flag                    true
% 2.24/1.00  --time_out_prep_mult                    0.1
% 2.24/1.00  --splitting_mode                        input
% 2.24/1.00  --splitting_grd                         true
% 2.24/1.00  --splitting_cvd                         false
% 2.24/1.00  --splitting_cvd_svl                     false
% 2.24/1.00  --splitting_nvd                         32
% 2.24/1.00  --sub_typing                            true
% 2.24/1.00  --prep_gs_sim                           true
% 2.24/1.00  --prep_unflatten                        true
% 2.24/1.00  --prep_res_sim                          true
% 2.24/1.00  --prep_upred                            true
% 2.24/1.00  --prep_sem_filter                       exhaustive
% 2.24/1.00  --prep_sem_filter_out                   false
% 2.24/1.00  --pred_elim                             true
% 2.24/1.00  --res_sim_input                         true
% 2.24/1.00  --eq_ax_congr_red                       true
% 2.24/1.00  --pure_diseq_elim                       true
% 2.24/1.00  --brand_transform                       false
% 2.24/1.00  --non_eq_to_eq                          false
% 2.24/1.00  --prep_def_merge                        true
% 2.24/1.00  --prep_def_merge_prop_impl              false
% 2.24/1.00  --prep_def_merge_mbd                    true
% 2.24/1.00  --prep_def_merge_tr_red                 false
% 2.24/1.00  --prep_def_merge_tr_cl                  false
% 2.24/1.00  --smt_preprocessing                     true
% 2.24/1.00  --smt_ac_axioms                         fast
% 2.24/1.00  --preprocessed_out                      false
% 2.24/1.00  --preprocessed_stats                    false
% 2.24/1.00  
% 2.24/1.00  ------ Abstraction refinement Options
% 2.24/1.00  
% 2.24/1.00  --abstr_ref                             []
% 2.24/1.00  --abstr_ref_prep                        false
% 2.24/1.00  --abstr_ref_until_sat                   false
% 2.24/1.00  --abstr_ref_sig_restrict                funpre
% 2.24/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.24/1.00  --abstr_ref_under                       []
% 2.24/1.00  
% 2.24/1.00  ------ SAT Options
% 2.24/1.00  
% 2.24/1.00  --sat_mode                              false
% 2.24/1.00  --sat_fm_restart_options                ""
% 2.24/1.00  --sat_gr_def                            false
% 2.24/1.00  --sat_epr_types                         true
% 2.24/1.00  --sat_non_cyclic_types                  false
% 2.24/1.00  --sat_finite_models                     false
% 2.24/1.00  --sat_fm_lemmas                         false
% 2.24/1.00  --sat_fm_prep                           false
% 2.24/1.00  --sat_fm_uc_incr                        true
% 2.24/1.00  --sat_out_model                         small
% 2.24/1.00  --sat_out_clauses                       false
% 2.24/1.00  
% 2.24/1.00  ------ QBF Options
% 2.24/1.00  
% 2.24/1.00  --qbf_mode                              false
% 2.24/1.00  --qbf_elim_univ                         false
% 2.24/1.00  --qbf_dom_inst                          none
% 2.24/1.00  --qbf_dom_pre_inst                      false
% 2.24/1.00  --qbf_sk_in                             false
% 2.24/1.00  --qbf_pred_elim                         true
% 2.24/1.00  --qbf_split                             512
% 2.24/1.00  
% 2.24/1.00  ------ BMC1 Options
% 2.24/1.00  
% 2.24/1.00  --bmc1_incremental                      false
% 2.24/1.00  --bmc1_axioms                           reachable_all
% 2.24/1.00  --bmc1_min_bound                        0
% 2.24/1.00  --bmc1_max_bound                        -1
% 2.24/1.00  --bmc1_max_bound_default                -1
% 2.24/1.00  --bmc1_symbol_reachability              true
% 2.24/1.00  --bmc1_property_lemmas                  false
% 2.24/1.00  --bmc1_k_induction                      false
% 2.24/1.00  --bmc1_non_equiv_states                 false
% 2.24/1.00  --bmc1_deadlock                         false
% 2.24/1.00  --bmc1_ucm                              false
% 2.24/1.00  --bmc1_add_unsat_core                   none
% 2.24/1.00  --bmc1_unsat_core_children              false
% 2.24/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.24/1.00  --bmc1_out_stat                         full
% 2.24/1.00  --bmc1_ground_init                      false
% 2.24/1.00  --bmc1_pre_inst_next_state              false
% 2.24/1.00  --bmc1_pre_inst_state                   false
% 2.24/1.00  --bmc1_pre_inst_reach_state             false
% 2.24/1.00  --bmc1_out_unsat_core                   false
% 2.24/1.00  --bmc1_aig_witness_out                  false
% 2.24/1.00  --bmc1_verbose                          false
% 2.24/1.00  --bmc1_dump_clauses_tptp                false
% 2.24/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.24/1.00  --bmc1_dump_file                        -
% 2.24/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.24/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.24/1.00  --bmc1_ucm_extend_mode                  1
% 2.24/1.00  --bmc1_ucm_init_mode                    2
% 2.24/1.00  --bmc1_ucm_cone_mode                    none
% 2.24/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.24/1.00  --bmc1_ucm_relax_model                  4
% 2.24/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.24/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.24/1.00  --bmc1_ucm_layered_model                none
% 2.24/1.00  --bmc1_ucm_max_lemma_size               10
% 2.24/1.00  
% 2.24/1.00  ------ AIG Options
% 2.24/1.00  
% 2.24/1.00  --aig_mode                              false
% 2.24/1.00  
% 2.24/1.00  ------ Instantiation Options
% 2.24/1.00  
% 2.24/1.00  --instantiation_flag                    true
% 2.24/1.00  --inst_sos_flag                         false
% 2.24/1.00  --inst_sos_phase                        true
% 2.24/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.24/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.24/1.00  --inst_lit_sel_side                     num_symb
% 2.24/1.00  --inst_solver_per_active                1400
% 2.24/1.00  --inst_solver_calls_frac                1.
% 2.24/1.00  --inst_passive_queue_type               priority_queues
% 2.24/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.24/1.00  --inst_passive_queues_freq              [25;2]
% 2.24/1.00  --inst_dismatching                      true
% 2.24/1.00  --inst_eager_unprocessed_to_passive     true
% 2.24/1.00  --inst_prop_sim_given                   true
% 2.24/1.00  --inst_prop_sim_new                     false
% 2.24/1.00  --inst_subs_new                         false
% 2.24/1.00  --inst_eq_res_simp                      false
% 2.24/1.00  --inst_subs_given                       false
% 2.24/1.00  --inst_orphan_elimination               true
% 2.24/1.00  --inst_learning_loop_flag               true
% 2.24/1.00  --inst_learning_start                   3000
% 2.24/1.00  --inst_learning_factor                  2
% 2.24/1.00  --inst_start_prop_sim_after_learn       3
% 2.24/1.00  --inst_sel_renew                        solver
% 2.24/1.00  --inst_lit_activity_flag                true
% 2.24/1.00  --inst_restr_to_given                   false
% 2.24/1.00  --inst_activity_threshold               500
% 2.24/1.00  --inst_out_proof                        true
% 2.24/1.00  
% 2.24/1.00  ------ Resolution Options
% 2.24/1.00  
% 2.24/1.00  --resolution_flag                       true
% 2.24/1.00  --res_lit_sel                           adaptive
% 2.24/1.00  --res_lit_sel_side                      none
% 2.24/1.00  --res_ordering                          kbo
% 2.24/1.00  --res_to_prop_solver                    active
% 2.24/1.00  --res_prop_simpl_new                    false
% 2.24/1.00  --res_prop_simpl_given                  true
% 2.24/1.00  --res_passive_queue_type                priority_queues
% 2.24/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.24/1.00  --res_passive_queues_freq               [15;5]
% 2.24/1.00  --res_forward_subs                      full
% 2.24/1.00  --res_backward_subs                     full
% 2.24/1.00  --res_forward_subs_resolution           true
% 2.24/1.00  --res_backward_subs_resolution          true
% 2.24/1.00  --res_orphan_elimination                true
% 2.24/1.00  --res_time_limit                        2.
% 2.24/1.00  --res_out_proof                         true
% 2.24/1.00  
% 2.24/1.00  ------ Superposition Options
% 2.24/1.00  
% 2.24/1.00  --superposition_flag                    true
% 2.24/1.00  --sup_passive_queue_type                priority_queues
% 2.24/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.24/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.24/1.00  --demod_completeness_check              fast
% 2.24/1.00  --demod_use_ground                      true
% 2.24/1.00  --sup_to_prop_solver                    passive
% 2.24/1.00  --sup_prop_simpl_new                    true
% 2.24/1.00  --sup_prop_simpl_given                  true
% 2.24/1.00  --sup_fun_splitting                     false
% 2.24/1.00  --sup_smt_interval                      50000
% 2.24/1.00  
% 2.24/1.00  ------ Superposition Simplification Setup
% 2.24/1.00  
% 2.24/1.00  --sup_indices_passive                   []
% 2.24/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.24/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.00  --sup_full_bw                           [BwDemod]
% 2.24/1.00  --sup_immed_triv                        [TrivRules]
% 2.24/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.24/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.00  --sup_immed_bw_main                     []
% 2.24/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.24/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.00  
% 2.24/1.00  ------ Combination Options
% 2.24/1.00  
% 2.24/1.00  --comb_res_mult                         3
% 2.24/1.00  --comb_sup_mult                         2
% 2.24/1.00  --comb_inst_mult                        10
% 2.24/1.00  
% 2.24/1.00  ------ Debug Options
% 2.24/1.00  
% 2.24/1.00  --dbg_backtrace                         false
% 2.24/1.00  --dbg_dump_prop_clauses                 false
% 2.24/1.00  --dbg_dump_prop_clauses_file            -
% 2.24/1.00  --dbg_out_stat                          false
% 2.24/1.00  ------ Parsing...
% 2.24/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.24/1.00  
% 2.24/1.00  ------ Preprocessing... sf_s  rm: 3 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.24/1.00  
% 2.24/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.24/1.00  
% 2.24/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.24/1.00  ------ Proving...
% 2.24/1.00  ------ Problem Properties 
% 2.24/1.00  
% 2.24/1.00  
% 2.24/1.00  clauses                                 21
% 2.24/1.00  conjectures                             3
% 2.24/1.00  EPR                                     6
% 2.24/1.00  Horn                                    19
% 2.24/1.00  unary                                   4
% 2.24/1.00  binary                                  7
% 2.24/1.00  lits                                    54
% 2.24/1.00  lits eq                                 19
% 2.24/1.00  fd_pure                                 0
% 2.24/1.00  fd_pseudo                               0
% 2.24/1.00  fd_cond                                 0
% 2.24/1.00  fd_pseudo_cond                          1
% 2.24/1.00  AC symbols                              0
% 2.24/1.00  
% 2.24/1.00  ------ Schedule dynamic 5 is on 
% 2.24/1.00  
% 2.24/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.24/1.00  
% 2.24/1.00  
% 2.24/1.00  ------ 
% 2.24/1.00  Current options:
% 2.24/1.00  ------ 
% 2.24/1.00  
% 2.24/1.00  ------ Input Options
% 2.24/1.00  
% 2.24/1.00  --out_options                           all
% 2.24/1.00  --tptp_safe_out                         true
% 2.24/1.00  --problem_path                          ""
% 2.24/1.00  --include_path                          ""
% 2.24/1.00  --clausifier                            res/vclausify_rel
% 2.24/1.00  --clausifier_options                    --mode clausify
% 2.24/1.00  --stdin                                 false
% 2.24/1.00  --stats_out                             all
% 2.24/1.00  
% 2.24/1.00  ------ General Options
% 2.24/1.00  
% 2.24/1.00  --fof                                   false
% 2.24/1.00  --time_out_real                         305.
% 2.24/1.00  --time_out_virtual                      -1.
% 2.24/1.00  --symbol_type_check                     false
% 2.24/1.00  --clausify_out                          false
% 2.24/1.00  --sig_cnt_out                           false
% 2.24/1.00  --trig_cnt_out                          false
% 2.24/1.00  --trig_cnt_out_tolerance                1.
% 2.24/1.00  --trig_cnt_out_sk_spl                   false
% 2.24/1.00  --abstr_cl_out                          false
% 2.24/1.00  
% 2.24/1.00  ------ Global Options
% 2.24/1.00  
% 2.24/1.00  --schedule                              default
% 2.24/1.00  --add_important_lit                     false
% 2.24/1.00  --prop_solver_per_cl                    1000
% 2.24/1.00  --min_unsat_core                        false
% 2.24/1.00  --soft_assumptions                      false
% 2.24/1.00  --soft_lemma_size                       3
% 2.24/1.00  --prop_impl_unit_size                   0
% 2.24/1.00  --prop_impl_unit                        []
% 2.24/1.00  --share_sel_clauses                     true
% 2.24/1.00  --reset_solvers                         false
% 2.24/1.00  --bc_imp_inh                            [conj_cone]
% 2.24/1.00  --conj_cone_tolerance                   3.
% 2.24/1.00  --extra_neg_conj                        none
% 2.24/1.00  --large_theory_mode                     true
% 2.24/1.00  --prolific_symb_bound                   200
% 2.24/1.00  --lt_threshold                          2000
% 2.24/1.00  --clause_weak_htbl                      true
% 2.24/1.00  --gc_record_bc_elim                     false
% 2.24/1.00  
% 2.24/1.00  ------ Preprocessing Options
% 2.24/1.00  
% 2.24/1.00  --preprocessing_flag                    true
% 2.24/1.00  --time_out_prep_mult                    0.1
% 2.24/1.00  --splitting_mode                        input
% 2.24/1.00  --splitting_grd                         true
% 2.24/1.00  --splitting_cvd                         false
% 2.24/1.00  --splitting_cvd_svl                     false
% 2.24/1.00  --splitting_nvd                         32
% 2.24/1.00  --sub_typing                            true
% 2.24/1.00  --prep_gs_sim                           true
% 2.24/1.00  --prep_unflatten                        true
% 2.24/1.00  --prep_res_sim                          true
% 2.24/1.00  --prep_upred                            true
% 2.24/1.00  --prep_sem_filter                       exhaustive
% 2.24/1.00  --prep_sem_filter_out                   false
% 2.24/1.00  --pred_elim                             true
% 2.24/1.00  --res_sim_input                         true
% 2.24/1.00  --eq_ax_congr_red                       true
% 2.24/1.00  --pure_diseq_elim                       true
% 2.24/1.00  --brand_transform                       false
% 2.24/1.00  --non_eq_to_eq                          false
% 2.24/1.00  --prep_def_merge                        true
% 2.24/1.00  --prep_def_merge_prop_impl              false
% 2.24/1.00  --prep_def_merge_mbd                    true
% 2.24/1.00  --prep_def_merge_tr_red                 false
% 2.24/1.00  --prep_def_merge_tr_cl                  false
% 2.24/1.00  --smt_preprocessing                     true
% 2.24/1.00  --smt_ac_axioms                         fast
% 2.24/1.00  --preprocessed_out                      false
% 2.24/1.00  --preprocessed_stats                    false
% 2.24/1.00  
% 2.24/1.00  ------ Abstraction refinement Options
% 2.24/1.00  
% 2.24/1.00  --abstr_ref                             []
% 2.24/1.00  --abstr_ref_prep                        false
% 2.24/1.00  --abstr_ref_until_sat                   false
% 2.24/1.00  --abstr_ref_sig_restrict                funpre
% 2.24/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.24/1.00  --abstr_ref_under                       []
% 2.24/1.00  
% 2.24/1.00  ------ SAT Options
% 2.24/1.00  
% 2.24/1.00  --sat_mode                              false
% 2.24/1.00  --sat_fm_restart_options                ""
% 2.24/1.00  --sat_gr_def                            false
% 2.24/1.00  --sat_epr_types                         true
% 2.24/1.00  --sat_non_cyclic_types                  false
% 2.24/1.00  --sat_finite_models                     false
% 2.24/1.00  --sat_fm_lemmas                         false
% 2.24/1.00  --sat_fm_prep                           false
% 2.24/1.00  --sat_fm_uc_incr                        true
% 2.24/1.00  --sat_out_model                         small
% 2.24/1.00  --sat_out_clauses                       false
% 2.24/1.00  
% 2.24/1.00  ------ QBF Options
% 2.24/1.00  
% 2.24/1.00  --qbf_mode                              false
% 2.24/1.00  --qbf_elim_univ                         false
% 2.24/1.00  --qbf_dom_inst                          none
% 2.24/1.00  --qbf_dom_pre_inst                      false
% 2.24/1.00  --qbf_sk_in                             false
% 2.24/1.00  --qbf_pred_elim                         true
% 2.24/1.00  --qbf_split                             512
% 2.24/1.00  
% 2.24/1.00  ------ BMC1 Options
% 2.24/1.00  
% 2.24/1.00  --bmc1_incremental                      false
% 2.24/1.00  --bmc1_axioms                           reachable_all
% 2.24/1.00  --bmc1_min_bound                        0
% 2.24/1.00  --bmc1_max_bound                        -1
% 2.24/1.00  --bmc1_max_bound_default                -1
% 2.24/1.00  --bmc1_symbol_reachability              true
% 2.24/1.00  --bmc1_property_lemmas                  false
% 2.24/1.00  --bmc1_k_induction                      false
% 2.24/1.00  --bmc1_non_equiv_states                 false
% 2.24/1.00  --bmc1_deadlock                         false
% 2.24/1.00  --bmc1_ucm                              false
% 2.24/1.00  --bmc1_add_unsat_core                   none
% 2.24/1.00  --bmc1_unsat_core_children              false
% 2.24/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.24/1.00  --bmc1_out_stat                         full
% 2.24/1.00  --bmc1_ground_init                      false
% 2.24/1.00  --bmc1_pre_inst_next_state              false
% 2.24/1.00  --bmc1_pre_inst_state                   false
% 2.24/1.00  --bmc1_pre_inst_reach_state             false
% 2.24/1.00  --bmc1_out_unsat_core                   false
% 2.24/1.00  --bmc1_aig_witness_out                  false
% 2.24/1.00  --bmc1_verbose                          false
% 2.24/1.00  --bmc1_dump_clauses_tptp                false
% 2.24/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.24/1.00  --bmc1_dump_file                        -
% 2.24/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.24/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.24/1.00  --bmc1_ucm_extend_mode                  1
% 2.24/1.00  --bmc1_ucm_init_mode                    2
% 2.24/1.00  --bmc1_ucm_cone_mode                    none
% 2.24/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.24/1.00  --bmc1_ucm_relax_model                  4
% 2.24/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.24/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.24/1.00  --bmc1_ucm_layered_model                none
% 2.24/1.00  --bmc1_ucm_max_lemma_size               10
% 2.24/1.00  
% 2.24/1.00  ------ AIG Options
% 2.24/1.00  
% 2.24/1.00  --aig_mode                              false
% 2.24/1.00  
% 2.24/1.00  ------ Instantiation Options
% 2.24/1.00  
% 2.24/1.00  --instantiation_flag                    true
% 2.24/1.00  --inst_sos_flag                         false
% 2.24/1.00  --inst_sos_phase                        true
% 2.24/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.24/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.24/1.00  --inst_lit_sel_side                     none
% 2.24/1.00  --inst_solver_per_active                1400
% 2.24/1.00  --inst_solver_calls_frac                1.
% 2.24/1.00  --inst_passive_queue_type               priority_queues
% 2.24/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.24/1.00  --inst_passive_queues_freq              [25;2]
% 2.24/1.00  --inst_dismatching                      true
% 2.24/1.00  --inst_eager_unprocessed_to_passive     true
% 2.24/1.00  --inst_prop_sim_given                   true
% 2.24/1.00  --inst_prop_sim_new                     false
% 2.24/1.00  --inst_subs_new                         false
% 2.24/1.00  --inst_eq_res_simp                      false
% 2.24/1.00  --inst_subs_given                       false
% 2.24/1.00  --inst_orphan_elimination               true
% 2.24/1.00  --inst_learning_loop_flag               true
% 2.24/1.00  --inst_learning_start                   3000
% 2.24/1.00  --inst_learning_factor                  2
% 2.24/1.00  --inst_start_prop_sim_after_learn       3
% 2.24/1.00  --inst_sel_renew                        solver
% 2.24/1.00  --inst_lit_activity_flag                true
% 2.24/1.00  --inst_restr_to_given                   false
% 2.24/1.00  --inst_activity_threshold               500
% 2.24/1.00  --inst_out_proof                        true
% 2.24/1.00  
% 2.24/1.00  ------ Resolution Options
% 2.24/1.00  
% 2.24/1.00  --resolution_flag                       false
% 2.24/1.00  --res_lit_sel                           adaptive
% 2.24/1.00  --res_lit_sel_side                      none
% 2.24/1.00  --res_ordering                          kbo
% 2.24/1.00  --res_to_prop_solver                    active
% 2.24/1.00  --res_prop_simpl_new                    false
% 2.24/1.00  --res_prop_simpl_given                  true
% 2.24/1.00  --res_passive_queue_type                priority_queues
% 2.24/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.24/1.00  --res_passive_queues_freq               [15;5]
% 2.24/1.00  --res_forward_subs                      full
% 2.24/1.00  --res_backward_subs                     full
% 2.24/1.00  --res_forward_subs_resolution           true
% 2.24/1.00  --res_backward_subs_resolution          true
% 2.24/1.00  --res_orphan_elimination                true
% 2.24/1.00  --res_time_limit                        2.
% 2.24/1.00  --res_out_proof                         true
% 2.24/1.00  
% 2.24/1.00  ------ Superposition Options
% 2.24/1.00  
% 2.24/1.00  --superposition_flag                    true
% 2.24/1.00  --sup_passive_queue_type                priority_queues
% 2.24/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.24/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.24/1.00  --demod_completeness_check              fast
% 2.24/1.00  --demod_use_ground                      true
% 2.24/1.00  --sup_to_prop_solver                    passive
% 2.24/1.00  --sup_prop_simpl_new                    true
% 2.24/1.00  --sup_prop_simpl_given                  true
% 2.24/1.00  --sup_fun_splitting                     false
% 2.24/1.00  --sup_smt_interval                      50000
% 2.24/1.00  
% 2.24/1.00  ------ Superposition Simplification Setup
% 2.24/1.00  
% 2.24/1.00  --sup_indices_passive                   []
% 2.24/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.24/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.24/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.00  --sup_full_bw                           [BwDemod]
% 2.24/1.00  --sup_immed_triv                        [TrivRules]
% 2.24/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.24/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.00  --sup_immed_bw_main                     []
% 2.24/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.24/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.24/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.24/1.00  
% 2.24/1.00  ------ Combination Options
% 2.24/1.00  
% 2.24/1.00  --comb_res_mult                         3
% 2.24/1.00  --comb_sup_mult                         2
% 2.24/1.00  --comb_inst_mult                        10
% 2.24/1.00  
% 2.24/1.00  ------ Debug Options
% 2.24/1.00  
% 2.24/1.00  --dbg_backtrace                         false
% 2.24/1.00  --dbg_dump_prop_clauses                 false
% 2.24/1.00  --dbg_dump_prop_clauses_file            -
% 2.24/1.00  --dbg_out_stat                          false
% 2.24/1.00  
% 2.24/1.00  
% 2.24/1.00  
% 2.24/1.00  
% 2.24/1.00  ------ Proving...
% 2.24/1.00  
% 2.24/1.00  
% 2.24/1.00  % SZS status Theorem for theBenchmark.p
% 2.24/1.00  
% 2.24/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.24/1.00  
% 2.24/1.00  fof(f10,axiom,(
% 2.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/1.00  
% 2.24/1.00  fof(f22,plain,(
% 2.24/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.00    inference(ennf_transformation,[],[f10])).
% 2.24/1.00  
% 2.24/1.00  fof(f23,plain,(
% 2.24/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.00    inference(flattening,[],[f22])).
% 2.24/1.00  
% 2.24/1.00  fof(f30,plain,(
% 2.24/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.00    inference(nnf_transformation,[],[f23])).
% 2.24/1.00  
% 2.24/1.00  fof(f47,plain,(
% 2.24/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.00    inference(cnf_transformation,[],[f30])).
% 2.24/1.00  
% 2.24/1.00  fof(f11,conjecture,(
% 2.24/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/1.00  
% 2.24/1.00  fof(f12,negated_conjecture,(
% 2.24/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_tarski(X1,X2) => ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) & v1_funct_2(X3,X0,X2) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.24/1.00    inference(negated_conjecture,[],[f11])).
% 2.24/1.00  
% 2.24/1.00  fof(f24,plain,(
% 2.24/1.00    ? [X0,X1,X2,X3] : ((((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_tarski(X1,X2)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 2.24/1.00    inference(ennf_transformation,[],[f12])).
% 2.24/1.00  
% 2.24/1.00  fof(f25,plain,(
% 2.24/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 2.24/1.00    inference(flattening,[],[f24])).
% 2.24/1.00  
% 2.24/1.00  fof(f31,plain,(
% 2.24/1.00    ? [X0,X1,X2,X3] : ((~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X2))) | ~v1_funct_2(X3,X0,X2) | ~v1_funct_1(X3)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_tarski(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 2.24/1.00    introduced(choice_axiom,[])).
% 2.24/1.00  
% 2.24/1.00  fof(f32,plain,(
% 2.24/1.00    (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)) & (k1_xboole_0 = sK0 | k1_xboole_0 != sK1) & r1_tarski(sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 2.24/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f31])).
% 2.24/1.00  
% 2.24/1.00  fof(f54,plain,(
% 2.24/1.00    v1_funct_2(sK3,sK0,sK1)),
% 2.24/1.00    inference(cnf_transformation,[],[f32])).
% 2.24/1.00  
% 2.24/1.00  fof(f55,plain,(
% 2.24/1.00    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.24/1.00    inference(cnf_transformation,[],[f32])).
% 2.24/1.00  
% 2.24/1.00  fof(f8,axiom,(
% 2.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/1.00  
% 2.24/1.00  fof(f19,plain,(
% 2.24/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.00    inference(ennf_transformation,[],[f8])).
% 2.24/1.00  
% 2.24/1.00  fof(f45,plain,(
% 2.24/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.00    inference(cnf_transformation,[],[f19])).
% 2.24/1.00  
% 2.24/1.00  fof(f56,plain,(
% 2.24/1.00    r1_tarski(sK1,sK2)),
% 2.24/1.00    inference(cnf_transformation,[],[f32])).
% 2.24/1.00  
% 2.24/1.00  fof(f7,axiom,(
% 2.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/1.00  
% 2.24/1.00  fof(f18,plain,(
% 2.24/1.00    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.00    inference(ennf_transformation,[],[f7])).
% 2.24/1.00  
% 2.24/1.00  fof(f44,plain,(
% 2.24/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.00    inference(cnf_transformation,[],[f18])).
% 2.24/1.00  
% 2.24/1.00  fof(f5,axiom,(
% 2.24/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : ((v5_relat_1(X2,X0) & v1_relat_1(X2)) => v5_relat_1(X2,X1)))),
% 2.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/1.00  
% 2.24/1.00  fof(f15,plain,(
% 2.24/1.00    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | (~v5_relat_1(X2,X0) | ~v1_relat_1(X2))) | ~r1_tarski(X0,X1))),
% 2.24/1.00    inference(ennf_transformation,[],[f5])).
% 2.24/1.00  
% 2.24/1.00  fof(f16,plain,(
% 2.24/1.00    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2)) | ~r1_tarski(X0,X1))),
% 2.24/1.00    inference(flattening,[],[f15])).
% 2.24/1.00  
% 2.24/1.00  fof(f41,plain,(
% 2.24/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~v5_relat_1(X2,X0) | ~v1_relat_1(X2) | ~r1_tarski(X0,X1)) )),
% 2.24/1.00    inference(cnf_transformation,[],[f16])).
% 2.24/1.00  
% 2.24/1.00  fof(f6,axiom,(
% 2.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/1.00  
% 2.24/1.00  fof(f17,plain,(
% 2.24/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.24/1.00    inference(ennf_transformation,[],[f6])).
% 2.24/1.00  
% 2.24/1.00  fof(f42,plain,(
% 2.24/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.00    inference(cnf_transformation,[],[f17])).
% 2.24/1.00  
% 2.24/1.00  fof(f43,plain,(
% 2.24/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.00    inference(cnf_transformation,[],[f18])).
% 2.24/1.00  
% 2.24/1.00  fof(f3,axiom,(
% 2.24/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 2.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/1.00  
% 2.24/1.00  fof(f13,plain,(
% 2.24/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.24/1.00    inference(ennf_transformation,[],[f3])).
% 2.24/1.00  
% 2.24/1.00  fof(f28,plain,(
% 2.24/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.24/1.00    inference(nnf_transformation,[],[f13])).
% 2.24/1.00  
% 2.24/1.00  fof(f37,plain,(
% 2.24/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.24/1.00    inference(cnf_transformation,[],[f28])).
% 2.24/1.00  
% 2.24/1.00  fof(f4,axiom,(
% 2.24/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/1.00  
% 2.24/1.00  fof(f14,plain,(
% 2.24/1.00    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.24/1.00    inference(ennf_transformation,[],[f4])).
% 2.24/1.00  
% 2.24/1.00  fof(f29,plain,(
% 2.24/1.00    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.24/1.00    inference(nnf_transformation,[],[f14])).
% 2.24/1.00  
% 2.24/1.00  fof(f39,plain,(
% 2.24/1.00    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.24/1.00    inference(cnf_transformation,[],[f29])).
% 2.24/1.00  
% 2.24/1.00  fof(f9,axiom,(
% 2.24/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/1.00  
% 2.24/1.00  fof(f20,plain,(
% 2.24/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | (~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0))) | ~v1_relat_1(X2))),
% 2.24/1.00    inference(ennf_transformation,[],[f9])).
% 2.24/1.00  
% 2.24/1.00  fof(f21,plain,(
% 2.24/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2))),
% 2.24/1.00    inference(flattening,[],[f20])).
% 2.24/1.00  
% 2.24/1.00  fof(f46,plain,(
% 2.24/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r1_tarski(k2_relat_1(X2),X1) | ~r1_tarski(k1_relat_1(X2),X0) | ~v1_relat_1(X2)) )),
% 2.24/1.00    inference(cnf_transformation,[],[f21])).
% 2.24/1.00  
% 2.24/1.00  fof(f49,plain,(
% 2.24/1.00    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.00    inference(cnf_transformation,[],[f30])).
% 2.24/1.00  
% 2.24/1.00  fof(f58,plain,(
% 2.24/1.00    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) | ~v1_funct_2(sK3,sK0,sK2) | ~v1_funct_1(sK3)),
% 2.24/1.00    inference(cnf_transformation,[],[f32])).
% 2.24/1.00  
% 2.24/1.00  fof(f53,plain,(
% 2.24/1.00    v1_funct_1(sK3)),
% 2.24/1.00    inference(cnf_transformation,[],[f32])).
% 2.24/1.00  
% 2.24/1.00  fof(f1,axiom,(
% 2.24/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/1.00  
% 2.24/1.00  fof(f26,plain,(
% 2.24/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.24/1.00    inference(nnf_transformation,[],[f1])).
% 2.24/1.00  
% 2.24/1.00  fof(f27,plain,(
% 2.24/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.24/1.00    inference(flattening,[],[f26])).
% 2.24/1.00  
% 2.24/1.00  fof(f35,plain,(
% 2.24/1.00    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 2.24/1.00    inference(cnf_transformation,[],[f27])).
% 2.24/1.00  
% 2.24/1.00  fof(f2,axiom,(
% 2.24/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.24/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.24/1.00  
% 2.24/1.00  fof(f36,plain,(
% 2.24/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.24/1.00    inference(cnf_transformation,[],[f2])).
% 2.24/1.00  
% 2.24/1.00  fof(f57,plain,(
% 2.24/1.00    k1_xboole_0 = sK0 | k1_xboole_0 != sK1),
% 2.24/1.00    inference(cnf_transformation,[],[f32])).
% 2.24/1.00  
% 2.24/1.00  fof(f48,plain,(
% 2.24/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.00    inference(cnf_transformation,[],[f30])).
% 2.24/1.00  
% 2.24/1.00  fof(f65,plain,(
% 2.24/1.00    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 2.24/1.00    inference(equality_resolution,[],[f48])).
% 2.24/1.00  
% 2.24/1.00  fof(f51,plain,(
% 2.24/1.00    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.24/1.00    inference(cnf_transformation,[],[f30])).
% 2.24/1.00  
% 2.24/1.00  fof(f63,plain,(
% 2.24/1.00    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 2.24/1.00    inference(equality_resolution,[],[f51])).
% 2.24/1.00  
% 2.24/1.00  cnf(c_19,plain,
% 2.24/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.24/1.00      | k1_xboole_0 = X2 ),
% 2.24/1.00      inference(cnf_transformation,[],[f47]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_24,negated_conjecture,
% 2.24/1.00      ( v1_funct_2(sK3,sK0,sK1) ),
% 2.24/1.00      inference(cnf_transformation,[],[f54]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_460,plain,
% 2.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.00      | k1_relset_1(X1,X2,X0) = X1
% 2.24/1.00      | sK1 != X2
% 2.24/1.00      | sK0 != X1
% 2.24/1.00      | sK3 != X0
% 2.24/1.00      | k1_xboole_0 = X2 ),
% 2.24/1.00      inference(resolution_lifted,[status(thm)],[c_19,c_24]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_461,plain,
% 2.24/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.24/1.00      | k1_relset_1(sK0,sK1,sK3) = sK0
% 2.24/1.00      | k1_xboole_0 = sK1 ),
% 2.24/1.00      inference(unflattening,[status(thm)],[c_460]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_23,negated_conjecture,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 2.24/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_463,plain,
% 2.24/1.00      ( k1_relset_1(sK0,sK1,sK3) = sK0 | k1_xboole_0 = sK1 ),
% 2.24/1.00      inference(global_propositional_subsumption,
% 2.24/1.00                [status(thm)],
% 2.24/1.00                [c_461,c_23]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1037,plain,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_12,plain,
% 2.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.24/1.00      inference(cnf_transformation,[],[f45]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1040,plain,
% 2.24/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.24/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1756,plain,
% 2.24/1.00      ( k1_relset_1(sK0,sK1,sK3) = k1_relat_1(sK3) ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_1037,c_1040]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1758,plain,
% 2.24/1.00      ( k1_relat_1(sK3) = sK0 | sK1 = k1_xboole_0 ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_463,c_1756]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_22,negated_conjecture,
% 2.24/1.00      ( r1_tarski(sK1,sK2) ),
% 2.24/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1038,plain,
% 2.24/1.00      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_10,plain,
% 2.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.00      | v5_relat_1(X0,X2) ),
% 2.24/1.00      inference(cnf_transformation,[],[f44]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1041,plain,
% 2.24/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.24/1.00      | v5_relat_1(X0,X2) = iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1500,plain,
% 2.24/1.00      ( v5_relat_1(sK3,sK1) = iProver_top ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_1037,c_1041]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_8,plain,
% 2.24/1.00      ( ~ v5_relat_1(X0,X1)
% 2.24/1.00      | v5_relat_1(X0,X2)
% 2.24/1.00      | ~ r1_tarski(X1,X2)
% 2.24/1.00      | ~ v1_relat_1(X0) ),
% 2.24/1.00      inference(cnf_transformation,[],[f41]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1043,plain,
% 2.24/1.00      ( v5_relat_1(X0,X1) != iProver_top
% 2.24/1.00      | v5_relat_1(X0,X2) = iProver_top
% 2.24/1.00      | r1_tarski(X1,X2) != iProver_top
% 2.24/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2070,plain,
% 2.24/1.00      ( v5_relat_1(sK3,X0) = iProver_top
% 2.24/1.00      | r1_tarski(sK1,X0) != iProver_top
% 2.24/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_1500,c_1043]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_28,plain,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_9,plain,
% 2.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.00      | v1_relat_1(X0) ),
% 2.24/1.00      inference(cnf_transformation,[],[f42]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1201,plain,
% 2.24/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.24/1.00      | v1_relat_1(sK3) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1202,plain,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.24/1.00      | v1_relat_1(sK3) = iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_1201]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2324,plain,
% 2.24/1.00      ( r1_tarski(sK1,X0) != iProver_top
% 2.24/1.00      | v5_relat_1(sK3,X0) = iProver_top ),
% 2.24/1.00      inference(global_propositional_subsumption,
% 2.24/1.00                [status(thm)],
% 2.24/1.00                [c_2070,c_28,c_1202]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2325,plain,
% 2.24/1.00      ( v5_relat_1(sK3,X0) = iProver_top
% 2.24/1.00      | r1_tarski(sK1,X0) != iProver_top ),
% 2.24/1.00      inference(renaming,[status(thm)],[c_2324]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2333,plain,
% 2.24/1.00      ( v5_relat_1(sK3,sK2) = iProver_top ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_1038,c_2325]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_11,plain,
% 2.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.00      | v4_relat_1(X0,X1) ),
% 2.24/1.00      inference(cnf_transformation,[],[f43]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_5,plain,
% 2.24/1.00      ( ~ v4_relat_1(X0,X1)
% 2.24/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 2.24/1.00      | ~ v1_relat_1(X0) ),
% 2.24/1.00      inference(cnf_transformation,[],[f37]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_274,plain,
% 2.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 2.24/1.00      | ~ v1_relat_1(X0) ),
% 2.24/1.00      inference(resolution,[status(thm)],[c_11,c_5]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_278,plain,
% 2.24/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 2.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.24/1.00      inference(global_propositional_subsumption,
% 2.24/1.00                [status(thm)],
% 2.24/1.00                [c_274,c_9]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_279,plain,
% 2.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 2.24/1.00      inference(renaming,[status(thm)],[c_278]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1036,plain,
% 2.24/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.24/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_279]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1657,plain,
% 2.24/1.00      ( r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_1037,c_1036]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_7,plain,
% 2.24/1.00      ( ~ v5_relat_1(X0,X1)
% 2.24/1.00      | r1_tarski(k2_relat_1(X0),X1)
% 2.24/1.00      | ~ v1_relat_1(X0) ),
% 2.24/1.00      inference(cnf_transformation,[],[f39]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1044,plain,
% 2.24/1.00      ( v5_relat_1(X0,X1) != iProver_top
% 2.24/1.00      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 2.24/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_13,plain,
% 2.24/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.00      | ~ r1_tarski(k2_relat_1(X0),X2)
% 2.24/1.00      | ~ r1_tarski(k1_relat_1(X0),X1)
% 2.24/1.00      | ~ v1_relat_1(X0) ),
% 2.24/1.00      inference(cnf_transformation,[],[f46]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1039,plain,
% 2.24/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
% 2.24/1.00      | r1_tarski(k2_relat_1(X0),X2) != iProver_top
% 2.24/1.00      | r1_tarski(k1_relat_1(X0),X1) != iProver_top
% 2.24/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1811,plain,
% 2.24/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.24/1.00      | r1_tarski(k2_relat_1(X2),X1) != iProver_top
% 2.24/1.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 2.24/1.00      | v1_relat_1(X2) != iProver_top ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_1039,c_1040]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2578,plain,
% 2.24/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.24/1.00      | v5_relat_1(X2,X1) != iProver_top
% 2.24/1.00      | r1_tarski(k1_relat_1(X2),X0) != iProver_top
% 2.24/1.00      | v1_relat_1(X2) != iProver_top ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_1044,c_1811]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2783,plain,
% 2.24/1.00      ( k1_relset_1(sK0,X0,sK3) = k1_relat_1(sK3)
% 2.24/1.00      | v5_relat_1(sK3,X0) != iProver_top
% 2.24/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_1657,c_2578]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2870,plain,
% 2.24/1.00      ( v5_relat_1(sK3,X0) != iProver_top
% 2.24/1.00      | k1_relset_1(sK0,X0,sK3) = k1_relat_1(sK3) ),
% 2.24/1.00      inference(global_propositional_subsumption,
% 2.24/1.00                [status(thm)],
% 2.24/1.00                [c_2783,c_28,c_1202]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2871,plain,
% 2.24/1.00      ( k1_relset_1(sK0,X0,sK3) = k1_relat_1(sK3)
% 2.24/1.00      | v5_relat_1(sK3,X0) != iProver_top ),
% 2.24/1.00      inference(renaming,[status(thm)],[c_2870]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2879,plain,
% 2.24/1.00      ( k1_relset_1(sK0,sK2,sK3) = k1_relat_1(sK3) ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_2333,c_2871]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_17,plain,
% 2.24/1.00      ( v1_funct_2(X0,X1,X2)
% 2.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.00      | k1_relset_1(X1,X2,X0) != X1
% 2.24/1.00      | k1_xboole_0 = X2 ),
% 2.24/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_20,negated_conjecture,
% 2.24/1.00      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.24/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.24/1.00      | ~ v1_funct_1(sK3) ),
% 2.24/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_25,negated_conjecture,
% 2.24/1.00      ( v1_funct_1(sK3) ),
% 2.24/1.00      inference(cnf_transformation,[],[f53]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_140,plain,
% 2.24/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.24/1.00      | ~ v1_funct_2(sK3,sK0,sK2) ),
% 2.24/1.00      inference(global_propositional_subsumption,
% 2.24/1.00                [status(thm)],
% 2.24/1.00                [c_20,c_25]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_141,negated_conjecture,
% 2.24/1.00      ( ~ v1_funct_2(sK3,sK0,sK2)
% 2.24/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
% 2.24/1.00      inference(renaming,[status(thm)],[c_140]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_447,plain,
% 2.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.24/1.00      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.24/1.00      | k1_relset_1(X1,X2,X0) != X1
% 2.24/1.00      | sK2 != X2
% 2.24/1.00      | sK0 != X1
% 2.24/1.00      | sK3 != X0
% 2.24/1.00      | k1_xboole_0 = X2 ),
% 2.24/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_141]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_448,plain,
% 2.24/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.24/1.00      | k1_relset_1(sK0,sK2,sK3) != sK0
% 2.24/1.00      | k1_xboole_0 = sK2 ),
% 2.24/1.00      inference(unflattening,[status(thm)],[c_447]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1031,plain,
% 2.24/1.00      ( k1_relset_1(sK0,sK2,sK3) != sK0
% 2.24/1.00      | k1_xboole_0 = sK2
% 2.24/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_448]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2884,plain,
% 2.24/1.00      ( k1_relat_1(sK3) != sK0
% 2.24/1.00      | sK2 = k1_xboole_0
% 2.24/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) != iProver_top ),
% 2.24/1.00      inference(demodulation,[status(thm)],[c_2879,c_1031]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_29,plain,
% 2.24/1.00      ( r1_tarski(sK1,sK2) = iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_471,plain,
% 2.24/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.24/1.00      | sK1 != sK2
% 2.24/1.00      | sK0 != sK0
% 2.24/1.00      | sK3 != sK3 ),
% 2.24/1.00      inference(resolution_lifted,[status(thm)],[c_141,c_24]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1204,plain,
% 2.24/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.24/1.00      | v5_relat_1(sK3,sK1) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1205,plain,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.24/1.00      | v5_relat_1(sK3,sK1) = iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_1204]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1207,plain,
% 2.24/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 2.24/1.00      | r1_tarski(k1_relat_1(sK3),sK0) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_279]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1208,plain,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 2.24/1.00      | r1_tarski(k1_relat_1(sK3),sK0) = iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_1207]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_0,plain,
% 2.24/1.00      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 2.24/1.00      inference(cnf_transformation,[],[f35]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1213,plain,
% 2.24/1.00      ( ~ r1_tarski(sK1,sK2) | ~ r1_tarski(sK2,sK1) | sK1 = sK2 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_714,plain,( X0 = X0 ),theory(equality) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1263,plain,
% 2.24/1.00      ( sK3 = sK3 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_714]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1279,plain,
% 2.24/1.00      ( sK0 = sK0 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_714]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1292,plain,
% 2.24/1.00      ( sK1 = sK1 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_714]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_3,plain,
% 2.24/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 2.24/1.00      inference(cnf_transformation,[],[f36]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1452,plain,
% 2.24/1.00      ( r1_tarski(k1_xboole_0,sK1) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_716,plain,
% 2.24/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X3) | X2 != X0 | X3 != X1 ),
% 2.24/1.00      theory(equality) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1281,plain,
% 2.24/1.00      ( ~ r1_tarski(X0,X1) | r1_tarski(sK2,sK1) | sK1 != X1 | sK2 != X0 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_716]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1467,plain,
% 2.24/1.00      ( ~ r1_tarski(X0,sK1)
% 2.24/1.00      | r1_tarski(sK2,sK1)
% 2.24/1.00      | sK1 != sK1
% 2.24/1.00      | sK2 != X0 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_1281]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1469,plain,
% 2.24/1.00      ( r1_tarski(sK2,sK1)
% 2.24/1.00      | ~ r1_tarski(k1_xboole_0,sK1)
% 2.24/1.00      | sK1 != sK1
% 2.24/1.00      | sK2 != k1_xboole_0 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_1467]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1232,plain,
% 2.24/1.00      ( ~ v5_relat_1(sK3,X0)
% 2.24/1.00      | v5_relat_1(sK3,X1)
% 2.24/1.00      | ~ r1_tarski(X0,X1)
% 2.24/1.00      | ~ v1_relat_1(sK3) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1360,plain,
% 2.24/1.00      ( v5_relat_1(sK3,X0)
% 2.24/1.00      | ~ v5_relat_1(sK3,sK1)
% 2.24/1.00      | ~ r1_tarski(sK1,X0)
% 2.24/1.00      | ~ v1_relat_1(sK3) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_1232]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1505,plain,
% 2.24/1.00      ( ~ v5_relat_1(sK3,sK1)
% 2.24/1.00      | v5_relat_1(sK3,sK2)
% 2.24/1.00      | ~ r1_tarski(sK1,sK2)
% 2.24/1.00      | ~ v1_relat_1(sK3) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_1360]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1506,plain,
% 2.24/1.00      ( v5_relat_1(sK3,sK1) != iProver_top
% 2.24/1.00      | v5_relat_1(sK3,sK2) = iProver_top
% 2.24/1.00      | r1_tarski(sK1,sK2) != iProver_top
% 2.24/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_1505]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1233,plain,
% 2.24/1.00      ( ~ v5_relat_1(sK3,X0)
% 2.24/1.00      | r1_tarski(k2_relat_1(sK3),X0)
% 2.24/1.00      | ~ v1_relat_1(sK3) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1617,plain,
% 2.24/1.00      ( ~ v5_relat_1(sK3,sK2)
% 2.24/1.00      | r1_tarski(k2_relat_1(sK3),sK2)
% 2.24/1.00      | ~ v1_relat_1(sK3) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_1233]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1618,plain,
% 2.24/1.00      ( v5_relat_1(sK3,sK2) != iProver_top
% 2.24/1.00      | r1_tarski(k2_relat_1(sK3),sK2) = iProver_top
% 2.24/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_1617]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1231,plain,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.24/1.00      | ~ r1_tarski(k2_relat_1(sK3),X1)
% 2.24/1.00      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 2.24/1.00      | ~ v1_relat_1(sK3) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2126,plain,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,sK2)))
% 2.24/1.00      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.24/1.00      | ~ r1_tarski(k1_relat_1(sK3),X0)
% 2.24/1.00      | ~ v1_relat_1(sK3) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_1231]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2433,plain,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
% 2.24/1.00      | ~ r1_tarski(k2_relat_1(sK3),sK2)
% 2.24/1.00      | ~ r1_tarski(k1_relat_1(sK3),sK0)
% 2.24/1.00      | ~ v1_relat_1(sK3) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_2126]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2434,plain,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 2.24/1.00      | r1_tarski(k2_relat_1(sK3),sK2) != iProver_top
% 2.24/1.00      | r1_tarski(k1_relat_1(sK3),sK0) != iProver_top
% 2.24/1.00      | v1_relat_1(sK3) != iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_2433]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2969,plain,
% 2.24/1.00      ( k1_relat_1(sK3) != sK0 ),
% 2.24/1.00      inference(global_propositional_subsumption,
% 2.24/1.00                [status(thm)],
% 2.24/1.00                [c_2884,c_23,c_28,c_22,c_29,c_536,c_1201,c_1202,c_1204,
% 2.24/1.00                 c_1205,c_1207,c_1208,c_1213,c_1292,c_1452,c_1469,c_1505,
% 2.24/1.00                 c_1506,c_1617,c_1618,c_2433,c_2434]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_2972,plain,
% 2.24/1.00      ( sK1 = k1_xboole_0 ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_1758,c_2969]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_3134,plain,
% 2.24/1.00      ( k1_relset_1(sK0,k1_xboole_0,sK3) = k1_relat_1(sK3) ),
% 2.24/1.00      inference(demodulation,[status(thm)],[c_2972,c_1756]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_21,negated_conjecture,
% 2.24/1.00      ( k1_xboole_0 != sK1 | k1_xboole_0 = sK0 ),
% 2.24/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_3142,plain,
% 2.24/1.00      ( sK0 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 2.24/1.00      inference(demodulation,[status(thm)],[c_2972,c_21]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_3143,plain,
% 2.24/1.00      ( sK0 = k1_xboole_0 ),
% 2.24/1.00      inference(equality_resolution_simp,[status(thm)],[c_3142]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_18,plain,
% 2.24/1.00      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 2.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.24/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 2.24/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_434,plain,
% 2.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 2.24/1.00      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 2.24/1.00      | sK1 != X1
% 2.24/1.00      | sK0 != k1_xboole_0
% 2.24/1.00      | sK3 != X0 ),
% 2.24/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_24]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_435,plain,
% 2.24/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
% 2.24/1.00      | k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.24/1.00      | sK0 != k1_xboole_0 ),
% 2.24/1.00      inference(unflattening,[status(thm)],[c_434]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1032,plain,
% 2.24/1.00      ( k1_relset_1(k1_xboole_0,sK1,sK3) = k1_xboole_0
% 2.24/1.00      | sK0 != k1_xboole_0
% 2.24/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) != iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_435]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_3138,plain,
% 2.24/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.24/1.00      | sK0 != k1_xboole_0
% 2.24/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.24/1.00      inference(demodulation,[status(thm)],[c_2972,c_1032]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_3150,plain,
% 2.24/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.24/1.00      | k1_xboole_0 != k1_xboole_0
% 2.24/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.24/1.00      inference(light_normalisation,[status(thm)],[c_3138,c_3143]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_3151,plain,
% 2.24/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0
% 2.24/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top ),
% 2.24/1.00      inference(equality_resolution_simp,[status(thm)],[c_3150]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_3140,plain,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) = iProver_top ),
% 2.24/1.00      inference(demodulation,[status(thm)],[c_2972,c_1037]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_3147,plain,
% 2.24/1.00      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 2.24/1.00      inference(light_normalisation,[status(thm)],[c_3140,c_3143]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_3154,plain,
% 2.24/1.00      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK3) = k1_xboole_0 ),
% 2.24/1.00      inference(forward_subsumption_resolution,
% 2.24/1.00                [status(thm)],
% 2.24/1.00                [c_3151,c_3147]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_3164,plain,
% 2.24/1.00      ( k1_relat_1(sK3) = k1_xboole_0 ),
% 2.24/1.00      inference(light_normalisation,[status(thm)],[c_3134,c_3143,c_3154]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1048,plain,
% 2.24/1.00      ( X0 = X1
% 2.24/1.00      | r1_tarski(X0,X1) != iProver_top
% 2.24/1.00      | r1_tarski(X1,X0) != iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1938,plain,
% 2.24/1.00      ( k1_relat_1(sK3) = sK0
% 2.24/1.00      | r1_tarski(sK0,k1_relat_1(sK3)) != iProver_top ),
% 2.24/1.00      inference(superposition,[status(thm)],[c_1657,c_1048]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1953,plain,
% 2.24/1.00      ( ~ r1_tarski(sK0,k1_relat_1(sK3)) | k1_relat_1(sK3) = sK0 ),
% 2.24/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1938]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_15,plain,
% 2.24/1.00      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 2.24/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.24/1.00      | k1_xboole_0 = X1
% 2.24/1.00      | k1_xboole_0 = X0 ),
% 2.24/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_398,plain,
% 2.24/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 2.24/1.00      | sK1 != k1_xboole_0
% 2.24/1.00      | sK0 != X1
% 2.24/1.00      | sK3 != X0
% 2.24/1.00      | k1_xboole_0 = X0
% 2.24/1.00      | k1_xboole_0 = X1 ),
% 2.24/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_24]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_399,plain,
% 2.24/1.00      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
% 2.24/1.00      | sK1 != k1_xboole_0
% 2.24/1.00      | k1_xboole_0 = sK0
% 2.24/1.00      | k1_xboole_0 = sK3 ),
% 2.24/1.00      inference(unflattening,[status(thm)],[c_398]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1034,plain,
% 2.24/1.00      ( sK1 != k1_xboole_0
% 2.24/1.00      | k1_xboole_0 = sK0
% 2.24/1.00      | k1_xboole_0 = sK3
% 2.24/1.00      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0))) != iProver_top ),
% 2.24/1.00      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_78,plain,
% 2.24/1.00      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_3]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_83,plain,
% 2.24/1.00      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.24/1.00      | k1_xboole_0 = k1_xboole_0 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_0]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_715,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1381,plain,
% 2.24/1.00      ( sK1 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK1 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_715]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1382,plain,
% 2.24/1.00      ( sK1 != k1_xboole_0
% 2.24/1.00      | k1_xboole_0 = sK1
% 2.24/1.00      | k1_xboole_0 != k1_xboole_0 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_1381]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1561,plain,
% 2.24/1.00      ( sK1 != k1_xboole_0 | k1_xboole_0 = sK0 ),
% 2.24/1.00      inference(global_propositional_subsumption,
% 2.24/1.00                [status(thm)],
% 2.24/1.00                [c_1034,c_21,c_78,c_83,c_1382]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1492,plain,
% 2.24/1.00      ( ~ r1_tarski(X0,X1)
% 2.24/1.00      | r1_tarski(sK0,k1_relat_1(sK3))
% 2.24/1.00      | k1_relat_1(sK3) != X1
% 2.24/1.00      | sK0 != X0 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_716]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1494,plain,
% 2.24/1.00      ( r1_tarski(sK0,k1_relat_1(sK3))
% 2.24/1.00      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 2.24/1.00      | k1_relat_1(sK3) != k1_xboole_0
% 2.24/1.00      | sK0 != k1_xboole_0 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_1492]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1220,plain,
% 2.24/1.00      ( sK0 != X0 | sK0 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_715]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(c_1278,plain,
% 2.24/1.00      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 2.24/1.00      inference(instantiation,[status(thm)],[c_1220]) ).
% 2.24/1.00  
% 2.24/1.00  cnf(contradiction,plain,
% 2.24/1.00      ( $false ),
% 2.24/1.00      inference(minisat,
% 2.24/1.00                [status(thm)],
% 2.24/1.00                [c_3164,c_2884,c_2434,c_2433,c_1953,c_1758,c_1618,c_1617,
% 2.24/1.00                 c_1561,c_1506,c_1505,c_1494,c_1469,c_1452,c_1292,c_1279,
% 2.24/1.00                 c_1278,c_1263,c_1213,c_1208,c_1207,c_1205,c_1204,c_1202,
% 2.24/1.00                 c_1201,c_471,c_78,c_29,c_22,c_28,c_23]) ).
% 2.24/1.00  
% 2.24/1.00  
% 2.24/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.24/1.00  
% 2.24/1.00  ------                               Statistics
% 2.24/1.00  
% 2.24/1.00  ------ General
% 2.24/1.00  
% 2.24/1.00  abstr_ref_over_cycles:                  0
% 2.24/1.00  abstr_ref_under_cycles:                 0
% 2.24/1.00  gc_basic_clause_elim:                   0
% 2.24/1.00  forced_gc_time:                         0
% 2.24/1.00  parsing_time:                           0.02
% 2.24/1.00  unif_index_cands_time:                  0.
% 2.24/1.00  unif_index_add_time:                    0.
% 2.24/1.00  orderings_time:                         0.
% 2.24/1.00  out_proof_time:                         0.011
% 2.24/1.00  total_time:                             0.148
% 2.24/1.00  num_of_symbols:                         48
% 2.24/1.00  num_of_terms:                           1626
% 2.24/1.00  
% 2.24/1.00  ------ Preprocessing
% 2.24/1.00  
% 2.24/1.00  num_of_splits:                          0
% 2.24/1.00  num_of_split_atoms:                     0
% 2.24/1.00  num_of_reused_defs:                     0
% 2.24/1.00  num_eq_ax_congr_red:                    19
% 2.24/1.00  num_of_sem_filtered_clauses:            2
% 2.24/1.00  num_of_subtypes:                        0
% 2.24/1.00  monotx_restored_types:                  0
% 2.24/1.00  sat_num_of_epr_types:                   0
% 2.24/1.00  sat_num_of_non_cyclic_types:            0
% 2.24/1.00  sat_guarded_non_collapsed_types:        0
% 2.24/1.00  num_pure_diseq_elim:                    0
% 2.24/1.00  simp_replaced_by:                       0
% 2.24/1.00  res_preprocessed:                       103
% 2.24/1.00  prep_upred:                             0
% 2.24/1.00  prep_unflattend:                        33
% 2.24/1.00  smt_new_axioms:                         0
% 2.24/1.00  pred_elim_cands:                        4
% 2.24/1.00  pred_elim:                              2
% 2.24/1.00  pred_elim_cl:                           3
% 2.24/1.00  pred_elim_cycles:                       5
% 2.24/1.00  merged_defs:                            0
% 2.24/1.00  merged_defs_ncl:                        0
% 2.24/1.00  bin_hyper_res:                          0
% 2.24/1.00  prep_cycles:                            4
% 2.24/1.00  pred_elim_time:                         0.009
% 2.24/1.00  splitting_time:                         0.
% 2.24/1.00  sem_filter_time:                        0.
% 2.24/1.00  monotx_time:                            0.001
% 2.24/1.00  subtype_inf_time:                       0.
% 2.24/1.00  
% 2.24/1.00  ------ Problem properties
% 2.24/1.00  
% 2.24/1.00  clauses:                                21
% 2.24/1.00  conjectures:                            3
% 2.24/1.00  epr:                                    6
% 2.24/1.00  horn:                                   19
% 2.24/1.00  ground:                                 10
% 2.24/1.00  unary:                                  4
% 2.24/1.00  binary:                                 7
% 2.24/1.00  lits:                                   54
% 2.24/1.00  lits_eq:                                19
% 2.24/1.00  fd_pure:                                0
% 2.24/1.00  fd_pseudo:                              0
% 2.24/1.00  fd_cond:                                0
% 2.24/1.00  fd_pseudo_cond:                         1
% 2.24/1.00  ac_symbols:                             0
% 2.24/1.00  
% 2.24/1.00  ------ Propositional Solver
% 2.24/1.00  
% 2.24/1.00  prop_solver_calls:                      27
% 2.24/1.00  prop_fast_solver_calls:                 749
% 2.24/1.00  smt_solver_calls:                       0
% 2.24/1.00  smt_fast_solver_calls:                  0
% 2.24/1.00  prop_num_of_clauses:                    976
% 2.24/1.00  prop_preprocess_simplified:             3763
% 2.24/1.00  prop_fo_subsumed:                       19
% 2.24/1.00  prop_solver_time:                       0.
% 2.24/1.00  smt_solver_time:                        0.
% 2.24/1.00  smt_fast_solver_time:                   0.
% 2.24/1.00  prop_fast_solver_time:                  0.
% 2.24/1.00  prop_unsat_core_time:                   0.
% 2.24/1.00  
% 2.24/1.00  ------ QBF
% 2.24/1.00  
% 2.24/1.00  qbf_q_res:                              0
% 2.24/1.00  qbf_num_tautologies:                    0
% 2.24/1.00  qbf_prep_cycles:                        0
% 2.24/1.00  
% 2.24/1.00  ------ BMC1
% 2.24/1.00  
% 2.24/1.00  bmc1_current_bound:                     -1
% 2.24/1.00  bmc1_last_solved_bound:                 -1
% 2.24/1.00  bmc1_unsat_core_size:                   -1
% 2.24/1.00  bmc1_unsat_core_parents_size:           -1
% 2.24/1.00  bmc1_merge_next_fun:                    0
% 2.24/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.24/1.00  
% 2.24/1.00  ------ Instantiation
% 2.24/1.00  
% 2.24/1.00  inst_num_of_clauses:                    319
% 2.24/1.00  inst_num_in_passive:                    16
% 2.24/1.00  inst_num_in_active:                     231
% 2.24/1.00  inst_num_in_unprocessed:                72
% 2.24/1.00  inst_num_of_loops:                      250
% 2.24/1.00  inst_num_of_learning_restarts:          0
% 2.24/1.00  inst_num_moves_active_passive:          15
% 2.24/1.00  inst_lit_activity:                      0
% 2.24/1.00  inst_lit_activity_moves:                0
% 2.24/1.00  inst_num_tautologies:                   0
% 2.24/1.00  inst_num_prop_implied:                  0
% 2.24/1.00  inst_num_existing_simplified:           0
% 2.24/1.00  inst_num_eq_res_simplified:             0
% 2.24/1.00  inst_num_child_elim:                    0
% 2.24/1.00  inst_num_of_dismatching_blockings:      24
% 2.24/1.00  inst_num_of_non_proper_insts:           384
% 2.24/1.00  inst_num_of_duplicates:                 0
% 2.24/1.00  inst_inst_num_from_inst_to_res:         0
% 2.24/1.00  inst_dismatching_checking_time:         0.
% 2.24/1.00  
% 2.24/1.00  ------ Resolution
% 2.24/1.00  
% 2.24/1.00  res_num_of_clauses:                     0
% 2.24/1.00  res_num_in_passive:                     0
% 2.24/1.00  res_num_in_active:                      0
% 2.24/1.00  res_num_of_loops:                       107
% 2.24/1.00  res_forward_subset_subsumed:            53
% 2.24/1.00  res_backward_subset_subsumed:           0
% 2.24/1.00  res_forward_subsumed:                   0
% 2.24/1.00  res_backward_subsumed:                  0
% 2.24/1.00  res_forward_subsumption_resolution:     0
% 2.24/1.00  res_backward_subsumption_resolution:    0
% 2.24/1.00  res_clause_to_clause_subsumption:       141
% 2.24/1.00  res_orphan_elimination:                 0
% 2.24/1.00  res_tautology_del:                      40
% 2.24/1.00  res_num_eq_res_simplified:              1
% 2.24/1.00  res_num_sel_changes:                    0
% 2.24/1.00  res_moves_from_active_to_pass:          0
% 2.24/1.00  
% 2.24/1.00  ------ Superposition
% 2.24/1.00  
% 2.24/1.00  sup_time_total:                         0.
% 2.24/1.00  sup_time_generating:                    0.
% 2.24/1.00  sup_time_sim_full:                      0.
% 2.24/1.00  sup_time_sim_immed:                     0.
% 2.24/1.00  
% 2.24/1.00  sup_num_of_clauses:                     45
% 2.24/1.00  sup_num_in_active:                      35
% 2.24/1.00  sup_num_in_passive:                     10
% 2.24/1.00  sup_num_of_loops:                       49
% 2.24/1.00  sup_fw_superposition:                   43
% 2.24/1.00  sup_bw_superposition:                   9
% 2.24/1.00  sup_immediate_simplified:               10
% 2.24/1.00  sup_given_eliminated:                   0
% 2.24/1.00  comparisons_done:                       0
% 2.24/1.00  comparisons_avoided:                    6
% 2.24/1.00  
% 2.24/1.00  ------ Simplifications
% 2.24/1.00  
% 2.24/1.00  
% 2.24/1.00  sim_fw_subset_subsumed:                 4
% 2.24/1.00  sim_bw_subset_subsumed:                 1
% 2.24/1.00  sim_fw_subsumed:                        2
% 2.24/1.00  sim_bw_subsumed:                        0
% 2.24/1.00  sim_fw_subsumption_res:                 1
% 2.24/1.00  sim_bw_subsumption_res:                 0
% 2.24/1.00  sim_tautology_del:                      3
% 2.24/1.00  sim_eq_tautology_del:                   6
% 2.24/1.00  sim_eq_res_simp:                        3
% 2.24/1.00  sim_fw_demodulated:                     0
% 2.24/1.00  sim_bw_demodulated:                     14
% 2.24/1.00  sim_light_normalised:                   5
% 2.24/1.00  sim_joinable_taut:                      0
% 2.24/1.00  sim_joinable_simp:                      0
% 2.24/1.00  sim_ac_normalised:                      0
% 2.24/1.00  sim_smt_subsumption:                    0
% 2.24/1.00  
%------------------------------------------------------------------------------
